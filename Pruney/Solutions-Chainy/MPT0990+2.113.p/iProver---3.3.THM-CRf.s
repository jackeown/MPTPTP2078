%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:20 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  191 (1804 expanded)
%              Number of clauses        :  113 ( 481 expanded)
%              Number of leaves         :   20 ( 476 expanded)
%              Depth                    :   24
%              Number of atoms          :  766 (15534 expanded)
%              Number of equality atoms :  376 (5661 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
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

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f66,plain,(
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

fof(f65,plain,
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

fof(f67,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f60,f66,f65])).

fof(f112,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

fof(f115,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f113,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f117,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f67])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f126,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f95,f99])).

fof(f110,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f90,f99])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f116,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f67])).

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

fof(f51,plain,(
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

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f111,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f114,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f119,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f67])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f128,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f124,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f85,f99])).

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

fof(f53,plain,(
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

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f103,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f88,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f24,axiom,(
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

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f123,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f76,f99])).

fof(f118,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f120,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f67])).

fof(f121,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_50,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1569,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_47,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1572,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1583,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5897,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1572,c_1583])).

cnf(c_49,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_56,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_6061,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5897,c_56])).

cnf(c_6062,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6061])).

cnf(c_6069,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_6062])).

cnf(c_26,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_45,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_45])).

cnf(c_574,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_27,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_582,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_574,c_27])).

cnf(c_1564,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_52,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2014,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2565,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1564,c_52,c_50,c_49,c_47,c_582,c_2014])).

cnf(c_6070,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6069,c_2565])).

cnf(c_53,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_6368,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6070,c_53])).

cnf(c_22,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1588,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v2_funct_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8474,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6368,c_1588])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1587,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2747,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1569,c_1587])).

cnf(c_46,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2748,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2747,c_46])).

cnf(c_2746,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1572,c_1587])).

cnf(c_31,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_586,plain,
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
    inference(resolution_lifted,[status(thm)],[c_31,c_45])).

cnf(c_587,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_682,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_587])).

cnf(c_1563,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_2117,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1563])).

cnf(c_51,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_54,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_55,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_48,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_57,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_58,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_2572,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2117,c_53,c_54,c_55,c_56,c_57,c_58])).

cnf(c_2749,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2746,c_2572])).

cnf(c_8475,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != sK1
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8474,c_2748,c_2749])).

cnf(c_8476,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8475])).

cnf(c_43,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_164,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_168,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_912,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1706,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_1707,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1706])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1725,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2026,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_2646,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2026])).

cnf(c_2647,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2646])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2839,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2840,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2839])).

cnf(c_1600,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1601,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3079,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1601])).

cnf(c_3155,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1600,c_3079])).

cnf(c_17,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_3334,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3335,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3334])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1581,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8850,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_46,c_1581])).

cnf(c_8893,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8850,c_53,c_54,c_55])).

cnf(c_8894,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8893])).

cnf(c_8897,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_8894])).

cnf(c_8955,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8897,c_56,c_57,c_58,c_43,c_164,c_168,c_1707,c_3335])).

cnf(c_21,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1589,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8961,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8955,c_1589])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1574,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_3644,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_1574])).

cnf(c_5078,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3644,c_56,c_57,c_58,c_43,c_164,c_168,c_1707])).

cnf(c_5079,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5078])).

cnf(c_8965,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_8955,c_5079])).

cnf(c_8967,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8961,c_8965])).

cnf(c_9,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_8968,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8967,c_9])).

cnf(c_12716,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8476,c_53,c_56,c_57,c_58,c_43,c_164,c_168,c_1707,c_2647,c_2840,c_3155,c_3335,c_8897,c_8968])).

cnf(c_12722,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_12716,c_8965])).

cnf(c_14772,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | k2_relat_1(sK3) != k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_12722,c_1588])).

cnf(c_44,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1573,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_3846,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1573,c_1589])).

cnf(c_4001,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3846,c_53,c_3155])).

cnf(c_3643,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_46,c_1574])).

cnf(c_42,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1668,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_1806,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1668])).

cnf(c_1931,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1806])).

cnf(c_3856,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3643,c_52,c_51,c_50,c_46,c_44,c_42,c_1931])).

cnf(c_4003,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4001,c_3856])).

cnf(c_4004,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_4003,c_9])).

cnf(c_14783,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14772,c_2748,c_2749,c_4004])).

cnf(c_14784,plain,
    ( k2_funct_1(sK2) = sK3
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14783])).

cnf(c_41,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_60,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14784,c_3155,c_2840,c_2647,c_41,c_60,c_58,c_56,c_53])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.71/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/1.50  
% 7.71/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.71/1.50  
% 7.71/1.50  ------  iProver source info
% 7.71/1.50  
% 7.71/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.71/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.71/1.50  git: non_committed_changes: false
% 7.71/1.50  git: last_make_outside_of_git: false
% 7.71/1.50  
% 7.71/1.50  ------ 
% 7.71/1.50  
% 7.71/1.50  ------ Input Options
% 7.71/1.50  
% 7.71/1.50  --out_options                           all
% 7.71/1.50  --tptp_safe_out                         true
% 7.71/1.50  --problem_path                          ""
% 7.71/1.50  --include_path                          ""
% 7.71/1.50  --clausifier                            res/vclausify_rel
% 7.71/1.50  --clausifier_options                    ""
% 7.71/1.50  --stdin                                 false
% 7.71/1.50  --stats_out                             all
% 7.71/1.50  
% 7.71/1.50  ------ General Options
% 7.71/1.50  
% 7.71/1.50  --fof                                   false
% 7.71/1.50  --time_out_real                         305.
% 7.71/1.50  --time_out_virtual                      -1.
% 7.71/1.50  --symbol_type_check                     false
% 7.71/1.50  --clausify_out                          false
% 7.71/1.50  --sig_cnt_out                           false
% 7.71/1.50  --trig_cnt_out                          false
% 7.71/1.50  --trig_cnt_out_tolerance                1.
% 7.71/1.50  --trig_cnt_out_sk_spl                   false
% 7.71/1.50  --abstr_cl_out                          false
% 7.71/1.50  
% 7.71/1.50  ------ Global Options
% 7.71/1.50  
% 7.71/1.50  --schedule                              default
% 7.71/1.50  --add_important_lit                     false
% 7.71/1.50  --prop_solver_per_cl                    1000
% 7.71/1.50  --min_unsat_core                        false
% 7.71/1.50  --soft_assumptions                      false
% 7.71/1.50  --soft_lemma_size                       3
% 7.71/1.50  --prop_impl_unit_size                   0
% 7.71/1.50  --prop_impl_unit                        []
% 7.71/1.50  --share_sel_clauses                     true
% 7.71/1.50  --reset_solvers                         false
% 7.71/1.50  --bc_imp_inh                            [conj_cone]
% 7.71/1.50  --conj_cone_tolerance                   3.
% 7.71/1.50  --extra_neg_conj                        none
% 7.71/1.50  --large_theory_mode                     true
% 7.71/1.50  --prolific_symb_bound                   200
% 7.71/1.50  --lt_threshold                          2000
% 7.71/1.50  --clause_weak_htbl                      true
% 7.71/1.50  --gc_record_bc_elim                     false
% 7.71/1.50  
% 7.71/1.50  ------ Preprocessing Options
% 7.71/1.50  
% 7.71/1.50  --preprocessing_flag                    true
% 7.71/1.50  --time_out_prep_mult                    0.1
% 7.71/1.50  --splitting_mode                        input
% 7.71/1.50  --splitting_grd                         true
% 7.71/1.50  --splitting_cvd                         false
% 7.71/1.50  --splitting_cvd_svl                     false
% 7.71/1.50  --splitting_nvd                         32
% 7.71/1.50  --sub_typing                            true
% 7.71/1.50  --prep_gs_sim                           true
% 7.71/1.50  --prep_unflatten                        true
% 7.71/1.50  --prep_res_sim                          true
% 7.71/1.50  --prep_upred                            true
% 7.71/1.50  --prep_sem_filter                       exhaustive
% 7.71/1.50  --prep_sem_filter_out                   false
% 7.71/1.50  --pred_elim                             true
% 7.71/1.50  --res_sim_input                         true
% 7.71/1.50  --eq_ax_congr_red                       true
% 7.71/1.50  --pure_diseq_elim                       true
% 7.71/1.50  --brand_transform                       false
% 7.71/1.50  --non_eq_to_eq                          false
% 7.71/1.50  --prep_def_merge                        true
% 7.71/1.50  --prep_def_merge_prop_impl              false
% 7.71/1.50  --prep_def_merge_mbd                    true
% 7.71/1.50  --prep_def_merge_tr_red                 false
% 7.71/1.50  --prep_def_merge_tr_cl                  false
% 7.71/1.50  --smt_preprocessing                     true
% 7.71/1.50  --smt_ac_axioms                         fast
% 7.71/1.50  --preprocessed_out                      false
% 7.71/1.50  --preprocessed_stats                    false
% 7.71/1.50  
% 7.71/1.50  ------ Abstraction refinement Options
% 7.71/1.50  
% 7.71/1.50  --abstr_ref                             []
% 7.71/1.50  --abstr_ref_prep                        false
% 7.71/1.50  --abstr_ref_until_sat                   false
% 7.71/1.50  --abstr_ref_sig_restrict                funpre
% 7.71/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.71/1.50  --abstr_ref_under                       []
% 7.71/1.50  
% 7.71/1.50  ------ SAT Options
% 7.71/1.50  
% 7.71/1.50  --sat_mode                              false
% 7.71/1.50  --sat_fm_restart_options                ""
% 7.71/1.50  --sat_gr_def                            false
% 7.71/1.50  --sat_epr_types                         true
% 7.71/1.50  --sat_non_cyclic_types                  false
% 7.71/1.50  --sat_finite_models                     false
% 7.71/1.50  --sat_fm_lemmas                         false
% 7.71/1.50  --sat_fm_prep                           false
% 7.71/1.50  --sat_fm_uc_incr                        true
% 7.71/1.50  --sat_out_model                         small
% 7.71/1.50  --sat_out_clauses                       false
% 7.71/1.50  
% 7.71/1.50  ------ QBF Options
% 7.71/1.50  
% 7.71/1.50  --qbf_mode                              false
% 7.71/1.50  --qbf_elim_univ                         false
% 7.71/1.50  --qbf_dom_inst                          none
% 7.71/1.50  --qbf_dom_pre_inst                      false
% 7.71/1.50  --qbf_sk_in                             false
% 7.71/1.50  --qbf_pred_elim                         true
% 7.71/1.50  --qbf_split                             512
% 7.71/1.50  
% 7.71/1.50  ------ BMC1 Options
% 7.71/1.50  
% 7.71/1.50  --bmc1_incremental                      false
% 7.71/1.50  --bmc1_axioms                           reachable_all
% 7.71/1.50  --bmc1_min_bound                        0
% 7.71/1.50  --bmc1_max_bound                        -1
% 7.71/1.50  --bmc1_max_bound_default                -1
% 7.71/1.50  --bmc1_symbol_reachability              true
% 7.71/1.50  --bmc1_property_lemmas                  false
% 7.71/1.50  --bmc1_k_induction                      false
% 7.71/1.50  --bmc1_non_equiv_states                 false
% 7.71/1.50  --bmc1_deadlock                         false
% 7.71/1.50  --bmc1_ucm                              false
% 7.71/1.50  --bmc1_add_unsat_core                   none
% 7.71/1.50  --bmc1_unsat_core_children              false
% 7.71/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.71/1.50  --bmc1_out_stat                         full
% 7.71/1.50  --bmc1_ground_init                      false
% 7.71/1.50  --bmc1_pre_inst_next_state              false
% 7.71/1.50  --bmc1_pre_inst_state                   false
% 7.71/1.50  --bmc1_pre_inst_reach_state             false
% 7.71/1.50  --bmc1_out_unsat_core                   false
% 7.71/1.50  --bmc1_aig_witness_out                  false
% 7.71/1.50  --bmc1_verbose                          false
% 7.71/1.50  --bmc1_dump_clauses_tptp                false
% 7.71/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.71/1.50  --bmc1_dump_file                        -
% 7.71/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.71/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.71/1.50  --bmc1_ucm_extend_mode                  1
% 7.71/1.50  --bmc1_ucm_init_mode                    2
% 7.71/1.50  --bmc1_ucm_cone_mode                    none
% 7.71/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.71/1.50  --bmc1_ucm_relax_model                  4
% 7.71/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.71/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.71/1.50  --bmc1_ucm_layered_model                none
% 7.71/1.50  --bmc1_ucm_max_lemma_size               10
% 7.71/1.50  
% 7.71/1.50  ------ AIG Options
% 7.71/1.50  
% 7.71/1.50  --aig_mode                              false
% 7.71/1.50  
% 7.71/1.50  ------ Instantiation Options
% 7.71/1.50  
% 7.71/1.50  --instantiation_flag                    true
% 7.71/1.50  --inst_sos_flag                         true
% 7.71/1.50  --inst_sos_phase                        true
% 7.71/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.71/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.71/1.50  --inst_lit_sel_side                     num_symb
% 7.71/1.50  --inst_solver_per_active                1400
% 7.71/1.50  --inst_solver_calls_frac                1.
% 7.71/1.50  --inst_passive_queue_type               priority_queues
% 7.71/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.71/1.50  --inst_passive_queues_freq              [25;2]
% 7.71/1.50  --inst_dismatching                      true
% 7.71/1.50  --inst_eager_unprocessed_to_passive     true
% 7.71/1.50  --inst_prop_sim_given                   true
% 7.71/1.50  --inst_prop_sim_new                     false
% 7.71/1.50  --inst_subs_new                         false
% 7.71/1.50  --inst_eq_res_simp                      false
% 7.71/1.50  --inst_subs_given                       false
% 7.71/1.50  --inst_orphan_elimination               true
% 7.71/1.50  --inst_learning_loop_flag               true
% 7.71/1.50  --inst_learning_start                   3000
% 7.71/1.50  --inst_learning_factor                  2
% 7.71/1.50  --inst_start_prop_sim_after_learn       3
% 7.71/1.50  --inst_sel_renew                        solver
% 7.71/1.50  --inst_lit_activity_flag                true
% 7.71/1.50  --inst_restr_to_given                   false
% 7.71/1.50  --inst_activity_threshold               500
% 7.71/1.50  --inst_out_proof                        true
% 7.71/1.50  
% 7.71/1.50  ------ Resolution Options
% 7.71/1.50  
% 7.71/1.50  --resolution_flag                       true
% 7.71/1.50  --res_lit_sel                           adaptive
% 7.71/1.50  --res_lit_sel_side                      none
% 7.71/1.50  --res_ordering                          kbo
% 7.71/1.50  --res_to_prop_solver                    active
% 7.71/1.50  --res_prop_simpl_new                    false
% 7.71/1.50  --res_prop_simpl_given                  true
% 7.71/1.50  --res_passive_queue_type                priority_queues
% 7.71/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.71/1.51  --res_passive_queues_freq               [15;5]
% 7.71/1.51  --res_forward_subs                      full
% 7.71/1.51  --res_backward_subs                     full
% 7.71/1.51  --res_forward_subs_resolution           true
% 7.71/1.51  --res_backward_subs_resolution          true
% 7.71/1.51  --res_orphan_elimination                true
% 7.71/1.51  --res_time_limit                        2.
% 7.71/1.51  --res_out_proof                         true
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Options
% 7.71/1.51  
% 7.71/1.51  --superposition_flag                    true
% 7.71/1.51  --sup_passive_queue_type                priority_queues
% 7.71/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.71/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.71/1.51  --demod_completeness_check              fast
% 7.71/1.51  --demod_use_ground                      true
% 7.71/1.51  --sup_to_prop_solver                    passive
% 7.71/1.51  --sup_prop_simpl_new                    true
% 7.71/1.51  --sup_prop_simpl_given                  true
% 7.71/1.51  --sup_fun_splitting                     true
% 7.71/1.51  --sup_smt_interval                      50000
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Simplification Setup
% 7.71/1.51  
% 7.71/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.71/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.71/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.71/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.71/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.71/1.51  --sup_immed_triv                        [TrivRules]
% 7.71/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_immed_bw_main                     []
% 7.71/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.71/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.71/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_input_bw                          []
% 7.71/1.51  
% 7.71/1.51  ------ Combination Options
% 7.71/1.51  
% 7.71/1.51  --comb_res_mult                         3
% 7.71/1.51  --comb_sup_mult                         2
% 7.71/1.51  --comb_inst_mult                        10
% 7.71/1.51  
% 7.71/1.51  ------ Debug Options
% 7.71/1.51  
% 7.71/1.51  --dbg_backtrace                         false
% 7.71/1.51  --dbg_dump_prop_clauses                 false
% 7.71/1.51  --dbg_dump_prop_clauses_file            -
% 7.71/1.51  --dbg_out_stat                          false
% 7.71/1.51  ------ Parsing...
% 7.71/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.71/1.51  ------ Proving...
% 7.71/1.51  ------ Problem Properties 
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  clauses                                 47
% 7.71/1.51  conjectures                             11
% 7.71/1.51  EPR                                     9
% 7.71/1.51  Horn                                    43
% 7.71/1.51  unary                                   17
% 7.71/1.51  binary                                  2
% 7.71/1.51  lits                                    182
% 7.71/1.51  lits eq                                 38
% 7.71/1.51  fd_pure                                 0
% 7.71/1.51  fd_pseudo                               0
% 7.71/1.51  fd_cond                                 4
% 7.71/1.51  fd_pseudo_cond                          2
% 7.71/1.51  AC symbols                              0
% 7.71/1.51  
% 7.71/1.51  ------ Schedule dynamic 5 is on 
% 7.71/1.51  
% 7.71/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  ------ 
% 7.71/1.51  Current options:
% 7.71/1.51  ------ 
% 7.71/1.51  
% 7.71/1.51  ------ Input Options
% 7.71/1.51  
% 7.71/1.51  --out_options                           all
% 7.71/1.51  --tptp_safe_out                         true
% 7.71/1.51  --problem_path                          ""
% 7.71/1.51  --include_path                          ""
% 7.71/1.51  --clausifier                            res/vclausify_rel
% 7.71/1.51  --clausifier_options                    ""
% 7.71/1.51  --stdin                                 false
% 7.71/1.51  --stats_out                             all
% 7.71/1.51  
% 7.71/1.51  ------ General Options
% 7.71/1.51  
% 7.71/1.51  --fof                                   false
% 7.71/1.51  --time_out_real                         305.
% 7.71/1.51  --time_out_virtual                      -1.
% 7.71/1.51  --symbol_type_check                     false
% 7.71/1.51  --clausify_out                          false
% 7.71/1.51  --sig_cnt_out                           false
% 7.71/1.51  --trig_cnt_out                          false
% 7.71/1.51  --trig_cnt_out_tolerance                1.
% 7.71/1.51  --trig_cnt_out_sk_spl                   false
% 7.71/1.51  --abstr_cl_out                          false
% 7.71/1.51  
% 7.71/1.51  ------ Global Options
% 7.71/1.51  
% 7.71/1.51  --schedule                              default
% 7.71/1.51  --add_important_lit                     false
% 7.71/1.51  --prop_solver_per_cl                    1000
% 7.71/1.51  --min_unsat_core                        false
% 7.71/1.51  --soft_assumptions                      false
% 7.71/1.51  --soft_lemma_size                       3
% 7.71/1.51  --prop_impl_unit_size                   0
% 7.71/1.51  --prop_impl_unit                        []
% 7.71/1.51  --share_sel_clauses                     true
% 7.71/1.51  --reset_solvers                         false
% 7.71/1.51  --bc_imp_inh                            [conj_cone]
% 7.71/1.51  --conj_cone_tolerance                   3.
% 7.71/1.51  --extra_neg_conj                        none
% 7.71/1.51  --large_theory_mode                     true
% 7.71/1.51  --prolific_symb_bound                   200
% 7.71/1.51  --lt_threshold                          2000
% 7.71/1.51  --clause_weak_htbl                      true
% 7.71/1.51  --gc_record_bc_elim                     false
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing Options
% 7.71/1.51  
% 7.71/1.51  --preprocessing_flag                    true
% 7.71/1.51  --time_out_prep_mult                    0.1
% 7.71/1.51  --splitting_mode                        input
% 7.71/1.51  --splitting_grd                         true
% 7.71/1.51  --splitting_cvd                         false
% 7.71/1.51  --splitting_cvd_svl                     false
% 7.71/1.51  --splitting_nvd                         32
% 7.71/1.51  --sub_typing                            true
% 7.71/1.51  --prep_gs_sim                           true
% 7.71/1.51  --prep_unflatten                        true
% 7.71/1.51  --prep_res_sim                          true
% 7.71/1.51  --prep_upred                            true
% 7.71/1.51  --prep_sem_filter                       exhaustive
% 7.71/1.51  --prep_sem_filter_out                   false
% 7.71/1.51  --pred_elim                             true
% 7.71/1.51  --res_sim_input                         true
% 7.71/1.51  --eq_ax_congr_red                       true
% 7.71/1.51  --pure_diseq_elim                       true
% 7.71/1.51  --brand_transform                       false
% 7.71/1.51  --non_eq_to_eq                          false
% 7.71/1.51  --prep_def_merge                        true
% 7.71/1.51  --prep_def_merge_prop_impl              false
% 7.71/1.51  --prep_def_merge_mbd                    true
% 7.71/1.51  --prep_def_merge_tr_red                 false
% 7.71/1.51  --prep_def_merge_tr_cl                  false
% 7.71/1.51  --smt_preprocessing                     true
% 7.71/1.51  --smt_ac_axioms                         fast
% 7.71/1.51  --preprocessed_out                      false
% 7.71/1.51  --preprocessed_stats                    false
% 7.71/1.51  
% 7.71/1.51  ------ Abstraction refinement Options
% 7.71/1.51  
% 7.71/1.51  --abstr_ref                             []
% 7.71/1.51  --abstr_ref_prep                        false
% 7.71/1.51  --abstr_ref_until_sat                   false
% 7.71/1.51  --abstr_ref_sig_restrict                funpre
% 7.71/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.71/1.51  --abstr_ref_under                       []
% 7.71/1.51  
% 7.71/1.51  ------ SAT Options
% 7.71/1.51  
% 7.71/1.51  --sat_mode                              false
% 7.71/1.51  --sat_fm_restart_options                ""
% 7.71/1.51  --sat_gr_def                            false
% 7.71/1.51  --sat_epr_types                         true
% 7.71/1.51  --sat_non_cyclic_types                  false
% 7.71/1.51  --sat_finite_models                     false
% 7.71/1.51  --sat_fm_lemmas                         false
% 7.71/1.51  --sat_fm_prep                           false
% 7.71/1.51  --sat_fm_uc_incr                        true
% 7.71/1.51  --sat_out_model                         small
% 7.71/1.51  --sat_out_clauses                       false
% 7.71/1.51  
% 7.71/1.51  ------ QBF Options
% 7.71/1.51  
% 7.71/1.51  --qbf_mode                              false
% 7.71/1.51  --qbf_elim_univ                         false
% 7.71/1.51  --qbf_dom_inst                          none
% 7.71/1.51  --qbf_dom_pre_inst                      false
% 7.71/1.51  --qbf_sk_in                             false
% 7.71/1.51  --qbf_pred_elim                         true
% 7.71/1.51  --qbf_split                             512
% 7.71/1.51  
% 7.71/1.51  ------ BMC1 Options
% 7.71/1.51  
% 7.71/1.51  --bmc1_incremental                      false
% 7.71/1.51  --bmc1_axioms                           reachable_all
% 7.71/1.51  --bmc1_min_bound                        0
% 7.71/1.51  --bmc1_max_bound                        -1
% 7.71/1.51  --bmc1_max_bound_default                -1
% 7.71/1.51  --bmc1_symbol_reachability              true
% 7.71/1.51  --bmc1_property_lemmas                  false
% 7.71/1.51  --bmc1_k_induction                      false
% 7.71/1.51  --bmc1_non_equiv_states                 false
% 7.71/1.51  --bmc1_deadlock                         false
% 7.71/1.51  --bmc1_ucm                              false
% 7.71/1.51  --bmc1_add_unsat_core                   none
% 7.71/1.51  --bmc1_unsat_core_children              false
% 7.71/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.71/1.51  --bmc1_out_stat                         full
% 7.71/1.51  --bmc1_ground_init                      false
% 7.71/1.51  --bmc1_pre_inst_next_state              false
% 7.71/1.51  --bmc1_pre_inst_state                   false
% 7.71/1.51  --bmc1_pre_inst_reach_state             false
% 7.71/1.51  --bmc1_out_unsat_core                   false
% 7.71/1.51  --bmc1_aig_witness_out                  false
% 7.71/1.51  --bmc1_verbose                          false
% 7.71/1.51  --bmc1_dump_clauses_tptp                false
% 7.71/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.71/1.51  --bmc1_dump_file                        -
% 7.71/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.71/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.71/1.51  --bmc1_ucm_extend_mode                  1
% 7.71/1.51  --bmc1_ucm_init_mode                    2
% 7.71/1.51  --bmc1_ucm_cone_mode                    none
% 7.71/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.71/1.51  --bmc1_ucm_relax_model                  4
% 7.71/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.71/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.71/1.51  --bmc1_ucm_layered_model                none
% 7.71/1.51  --bmc1_ucm_max_lemma_size               10
% 7.71/1.51  
% 7.71/1.51  ------ AIG Options
% 7.71/1.51  
% 7.71/1.51  --aig_mode                              false
% 7.71/1.51  
% 7.71/1.51  ------ Instantiation Options
% 7.71/1.51  
% 7.71/1.51  --instantiation_flag                    true
% 7.71/1.51  --inst_sos_flag                         true
% 7.71/1.51  --inst_sos_phase                        true
% 7.71/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel_side                     none
% 7.71/1.51  --inst_solver_per_active                1400
% 7.71/1.51  --inst_solver_calls_frac                1.
% 7.71/1.51  --inst_passive_queue_type               priority_queues
% 7.71/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.71/1.51  --inst_passive_queues_freq              [25;2]
% 7.71/1.51  --inst_dismatching                      true
% 7.71/1.51  --inst_eager_unprocessed_to_passive     true
% 7.71/1.51  --inst_prop_sim_given                   true
% 7.71/1.51  --inst_prop_sim_new                     false
% 7.71/1.51  --inst_subs_new                         false
% 7.71/1.51  --inst_eq_res_simp                      false
% 7.71/1.51  --inst_subs_given                       false
% 7.71/1.51  --inst_orphan_elimination               true
% 7.71/1.51  --inst_learning_loop_flag               true
% 7.71/1.51  --inst_learning_start                   3000
% 7.71/1.51  --inst_learning_factor                  2
% 7.71/1.51  --inst_start_prop_sim_after_learn       3
% 7.71/1.51  --inst_sel_renew                        solver
% 7.71/1.51  --inst_lit_activity_flag                true
% 7.71/1.51  --inst_restr_to_given                   false
% 7.71/1.51  --inst_activity_threshold               500
% 7.71/1.51  --inst_out_proof                        true
% 7.71/1.51  
% 7.71/1.51  ------ Resolution Options
% 7.71/1.51  
% 7.71/1.51  --resolution_flag                       false
% 7.71/1.51  --res_lit_sel                           adaptive
% 7.71/1.51  --res_lit_sel_side                      none
% 7.71/1.51  --res_ordering                          kbo
% 7.71/1.51  --res_to_prop_solver                    active
% 7.71/1.51  --res_prop_simpl_new                    false
% 7.71/1.51  --res_prop_simpl_given                  true
% 7.71/1.51  --res_passive_queue_type                priority_queues
% 7.71/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.71/1.51  --res_passive_queues_freq               [15;5]
% 7.71/1.51  --res_forward_subs                      full
% 7.71/1.51  --res_backward_subs                     full
% 7.71/1.51  --res_forward_subs_resolution           true
% 7.71/1.51  --res_backward_subs_resolution          true
% 7.71/1.51  --res_orphan_elimination                true
% 7.71/1.51  --res_time_limit                        2.
% 7.71/1.51  --res_out_proof                         true
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Options
% 7.71/1.51  
% 7.71/1.51  --superposition_flag                    true
% 7.71/1.51  --sup_passive_queue_type                priority_queues
% 7.71/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.71/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.71/1.51  --demod_completeness_check              fast
% 7.71/1.51  --demod_use_ground                      true
% 7.71/1.51  --sup_to_prop_solver                    passive
% 7.71/1.51  --sup_prop_simpl_new                    true
% 7.71/1.51  --sup_prop_simpl_given                  true
% 7.71/1.51  --sup_fun_splitting                     true
% 7.71/1.51  --sup_smt_interval                      50000
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Simplification Setup
% 7.71/1.51  
% 7.71/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.71/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.71/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.71/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.71/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.71/1.51  --sup_immed_triv                        [TrivRules]
% 7.71/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_immed_bw_main                     []
% 7.71/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.71/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.71/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_input_bw                          []
% 7.71/1.51  
% 7.71/1.51  ------ Combination Options
% 7.71/1.51  
% 7.71/1.51  --comb_res_mult                         3
% 7.71/1.51  --comb_sup_mult                         2
% 7.71/1.51  --comb_inst_mult                        10
% 7.71/1.51  
% 7.71/1.51  ------ Debug Options
% 7.71/1.51  
% 7.71/1.51  --dbg_backtrace                         false
% 7.71/1.51  --dbg_dump_prop_clauses                 false
% 7.71/1.51  --dbg_dump_prop_clauses_file            -
% 7.71/1.51  --dbg_out_stat                          false
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  ------ Proving...
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  % SZS status Theorem for theBenchmark.p
% 7.71/1.51  
% 7.71/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.71/1.51  
% 7.71/1.51  fof(f25,conjecture,(
% 7.71/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f26,negated_conjecture,(
% 7.71/1.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.71/1.51    inference(negated_conjecture,[],[f25])).
% 7.71/1.51  
% 7.71/1.51  fof(f59,plain,(
% 7.71/1.51    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.71/1.51    inference(ennf_transformation,[],[f26])).
% 7.71/1.51  
% 7.71/1.51  fof(f60,plain,(
% 7.71/1.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.71/1.51    inference(flattening,[],[f59])).
% 7.71/1.51  
% 7.71/1.51  fof(f66,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.71/1.51    introduced(choice_axiom,[])).
% 7.71/1.51  
% 7.71/1.51  fof(f65,plain,(
% 7.71/1.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.71/1.51    introduced(choice_axiom,[])).
% 7.71/1.51  
% 7.71/1.51  fof(f67,plain,(
% 7.71/1.51    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.71/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f60,f66,f65])).
% 7.71/1.51  
% 7.71/1.51  fof(f112,plain,(
% 7.71/1.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.71/1.51    inference(cnf_transformation,[],[f67])).
% 7.71/1.51  
% 7.71/1.51  fof(f115,plain,(
% 7.71/1.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.71/1.51    inference(cnf_transformation,[],[f67])).
% 7.71/1.51  
% 7.71/1.51  fof(f19,axiom,(
% 7.71/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f49,plain,(
% 7.71/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.71/1.51    inference(ennf_transformation,[],[f19])).
% 7.71/1.51  
% 7.71/1.51  fof(f50,plain,(
% 7.71/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.71/1.51    inference(flattening,[],[f49])).
% 7.71/1.51  
% 7.71/1.51  fof(f98,plain,(
% 7.71/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f50])).
% 7.71/1.51  
% 7.71/1.51  fof(f113,plain,(
% 7.71/1.51    v1_funct_1(sK3)),
% 7.71/1.51    inference(cnf_transformation,[],[f67])).
% 7.71/1.51  
% 7.71/1.51  fof(f16,axiom,(
% 7.71/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f45,plain,(
% 7.71/1.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.71/1.51    inference(ennf_transformation,[],[f16])).
% 7.71/1.51  
% 7.71/1.51  fof(f46,plain,(
% 7.71/1.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.51    inference(flattening,[],[f45])).
% 7.71/1.51  
% 7.71/1.51  fof(f64,plain,(
% 7.71/1.51    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.51    inference(nnf_transformation,[],[f46])).
% 7.71/1.51  
% 7.71/1.51  fof(f93,plain,(
% 7.71/1.51    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f64])).
% 7.71/1.51  
% 7.71/1.51  fof(f117,plain,(
% 7.71/1.51    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.71/1.51    inference(cnf_transformation,[],[f67])).
% 7.71/1.51  
% 7.71/1.51  fof(f17,axiom,(
% 7.71/1.51    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f95,plain,(
% 7.71/1.51    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f17])).
% 7.71/1.51  
% 7.71/1.51  fof(f20,axiom,(
% 7.71/1.51    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f99,plain,(
% 7.71/1.51    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f20])).
% 7.71/1.51  
% 7.71/1.51  fof(f126,plain,(
% 7.71/1.51    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.71/1.51    inference(definition_unfolding,[],[f95,f99])).
% 7.71/1.51  
% 7.71/1.51  fof(f110,plain,(
% 7.71/1.51    v1_funct_1(sK2)),
% 7.71/1.51    inference(cnf_transformation,[],[f67])).
% 7.71/1.51  
% 7.71/1.51  fof(f18,axiom,(
% 7.71/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f47,plain,(
% 7.71/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.71/1.51    inference(ennf_transformation,[],[f18])).
% 7.71/1.51  
% 7.71/1.51  fof(f48,plain,(
% 7.71/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.71/1.51    inference(flattening,[],[f47])).
% 7.71/1.51  
% 7.71/1.51  fof(f97,plain,(
% 7.71/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f48])).
% 7.71/1.51  
% 7.71/1.51  fof(f13,axiom,(
% 7.71/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f41,plain,(
% 7.71/1.51    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.71/1.51    inference(ennf_transformation,[],[f13])).
% 7.71/1.51  
% 7.71/1.51  fof(f42,plain,(
% 7.71/1.51    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.71/1.51    inference(flattening,[],[f41])).
% 7.71/1.51  
% 7.71/1.51  fof(f90,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f42])).
% 7.71/1.51  
% 7.71/1.51  fof(f125,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.71/1.51    inference(definition_unfolding,[],[f90,f99])).
% 7.71/1.51  
% 7.71/1.51  fof(f15,axiom,(
% 7.71/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f44,plain,(
% 7.71/1.51    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.51    inference(ennf_transformation,[],[f15])).
% 7.71/1.51  
% 7.71/1.51  fof(f92,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f44])).
% 7.71/1.51  
% 7.71/1.51  fof(f116,plain,(
% 7.71/1.51    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.71/1.51    inference(cnf_transformation,[],[f67])).
% 7.71/1.51  
% 7.71/1.51  fof(f21,axiom,(
% 7.71/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f51,plain,(
% 7.71/1.51    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.71/1.51    inference(ennf_transformation,[],[f21])).
% 7.71/1.51  
% 7.71/1.51  fof(f52,plain,(
% 7.71/1.51    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.71/1.51    inference(flattening,[],[f51])).
% 7.71/1.51  
% 7.71/1.51  fof(f100,plain,(
% 7.71/1.51    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f52])).
% 7.71/1.51  
% 7.71/1.51  fof(f111,plain,(
% 7.71/1.51    v1_funct_2(sK2,sK0,sK1)),
% 7.71/1.51    inference(cnf_transformation,[],[f67])).
% 7.71/1.51  
% 7.71/1.51  fof(f114,plain,(
% 7.71/1.51    v1_funct_2(sK3,sK1,sK0)),
% 7.71/1.51    inference(cnf_transformation,[],[f67])).
% 7.71/1.51  
% 7.71/1.51  fof(f119,plain,(
% 7.71/1.51    k1_xboole_0 != sK0),
% 7.71/1.51    inference(cnf_transformation,[],[f67])).
% 7.71/1.51  
% 7.71/1.51  fof(f1,axiom,(
% 7.71/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f61,plain,(
% 7.71/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.71/1.51    inference(nnf_transformation,[],[f1])).
% 7.71/1.51  
% 7.71/1.51  fof(f62,plain,(
% 7.71/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.71/1.51    inference(flattening,[],[f61])).
% 7.71/1.51  
% 7.71/1.51  fof(f68,plain,(
% 7.71/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.71/1.51    inference(cnf_transformation,[],[f62])).
% 7.71/1.51  
% 7.71/1.51  fof(f128,plain,(
% 7.71/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.71/1.51    inference(equality_resolution,[],[f68])).
% 7.71/1.51  
% 7.71/1.51  fof(f70,plain,(
% 7.71/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f62])).
% 7.71/1.51  
% 7.71/1.51  fof(f2,axiom,(
% 7.71/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f28,plain,(
% 7.71/1.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.71/1.51    inference(ennf_transformation,[],[f2])).
% 7.71/1.51  
% 7.71/1.51  fof(f71,plain,(
% 7.71/1.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f28])).
% 7.71/1.51  
% 7.71/1.51  fof(f4,axiom,(
% 7.71/1.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f74,plain,(
% 7.71/1.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f4])).
% 7.71/1.51  
% 7.71/1.51  fof(f10,axiom,(
% 7.71/1.51    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f85,plain,(
% 7.71/1.51    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f10])).
% 7.71/1.51  
% 7.71/1.51  fof(f124,plain,(
% 7.71/1.51    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.71/1.51    inference(definition_unfolding,[],[f85,f99])).
% 7.71/1.51  
% 7.71/1.51  fof(f22,axiom,(
% 7.71/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f53,plain,(
% 7.71/1.51    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.71/1.51    inference(ennf_transformation,[],[f22])).
% 7.71/1.51  
% 7.71/1.51  fof(f54,plain,(
% 7.71/1.51    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.71/1.51    inference(flattening,[],[f53])).
% 7.71/1.51  
% 7.71/1.51  fof(f103,plain,(
% 7.71/1.51    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f54])).
% 7.71/1.51  
% 7.71/1.51  fof(f12,axiom,(
% 7.71/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f39,plain,(
% 7.71/1.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.71/1.51    inference(ennf_transformation,[],[f12])).
% 7.71/1.51  
% 7.71/1.51  fof(f40,plain,(
% 7.71/1.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.71/1.51    inference(flattening,[],[f39])).
% 7.71/1.51  
% 7.71/1.51  fof(f88,plain,(
% 7.71/1.51    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f40])).
% 7.71/1.51  
% 7.71/1.51  fof(f24,axiom,(
% 7.71/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f57,plain,(
% 7.71/1.51    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.71/1.51    inference(ennf_transformation,[],[f24])).
% 7.71/1.51  
% 7.71/1.51  fof(f58,plain,(
% 7.71/1.51    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.71/1.51    inference(flattening,[],[f57])).
% 7.71/1.51  
% 7.71/1.51  fof(f108,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f58])).
% 7.71/1.51  
% 7.71/1.51  fof(f6,axiom,(
% 7.71/1.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f76,plain,(
% 7.71/1.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.71/1.51    inference(cnf_transformation,[],[f6])).
% 7.71/1.51  
% 7.71/1.51  fof(f123,plain,(
% 7.71/1.51    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 7.71/1.51    inference(definition_unfolding,[],[f76,f99])).
% 7.71/1.51  
% 7.71/1.51  fof(f118,plain,(
% 7.71/1.51    v2_funct_1(sK2)),
% 7.71/1.51    inference(cnf_transformation,[],[f67])).
% 7.71/1.51  
% 7.71/1.51  fof(f120,plain,(
% 7.71/1.51    k1_xboole_0 != sK1),
% 7.71/1.51    inference(cnf_transformation,[],[f67])).
% 7.71/1.51  
% 7.71/1.51  fof(f121,plain,(
% 7.71/1.51    k2_funct_1(sK2) != sK3),
% 7.71/1.51    inference(cnf_transformation,[],[f67])).
% 7.71/1.51  
% 7.71/1.51  cnf(c_50,negated_conjecture,
% 7.71/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.71/1.51      inference(cnf_transformation,[],[f112]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1569,plain,
% 7.71/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_47,negated_conjecture,
% 7.71/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.71/1.51      inference(cnf_transformation,[],[f115]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1572,plain,
% 7.71/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_30,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X3)
% 7.71/1.51      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f98]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1583,plain,
% 7.71/1.51      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.71/1.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.71/1.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.51      | v1_funct_1(X5) != iProver_top
% 7.71/1.51      | v1_funct_1(X4) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_5897,plain,
% 7.71/1.51      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.51      | v1_funct_1(X2) != iProver_top
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1572,c_1583]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_49,negated_conjecture,
% 7.71/1.51      ( v1_funct_1(sK3) ),
% 7.71/1.51      inference(cnf_transformation,[],[f113]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_56,plain,
% 7.71/1.51      ( v1_funct_1(sK3) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_6061,plain,
% 7.71/1.51      ( v1_funct_1(X2) != iProver_top
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.51      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_5897,c_56]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_6062,plain,
% 7.71/1.51      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.71/1.51      inference(renaming,[status(thm)],[c_6061]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_6069,plain,
% 7.71/1.51      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.71/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1569,c_6062]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_26,plain,
% 7.71/1.51      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.71/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.71/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.71/1.51      | X3 = X2 ),
% 7.71/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_45,negated_conjecture,
% 7.71/1.51      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.71/1.51      inference(cnf_transformation,[],[f117]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_573,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | X3 = X0
% 7.71/1.51      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.71/1.51      | k6_partfun1(sK0) != X3
% 7.71/1.51      | sK0 != X2
% 7.71/1.51      | sK0 != X1 ),
% 7.71/1.51      inference(resolution_lifted,[status(thm)],[c_26,c_45]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_574,plain,
% 7.71/1.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.71/1.51      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.71/1.51      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.71/1.51      inference(unflattening,[status(thm)],[c_573]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_27,plain,
% 7.71/1.51      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.71/1.51      inference(cnf_transformation,[],[f126]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_582,plain,
% 7.71/1.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.71/1.51      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.71/1.51      inference(forward_subsumption_resolution,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_574,c_27]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1564,plain,
% 7.71/1.51      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.71/1.51      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_52,negated_conjecture,
% 7.71/1.51      ( v1_funct_1(sK2) ),
% 7.71/1.51      inference(cnf_transformation,[],[f110]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_28,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.71/1.51      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X3) ),
% 7.71/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2014,plain,
% 7.71/1.51      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.71/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.71/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.71/1.51      | ~ v1_funct_1(sK3)
% 7.71/1.51      | ~ v1_funct_1(sK2) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_28]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2565,plain,
% 7.71/1.51      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_1564,c_52,c_50,c_49,c_47,c_582,c_2014]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_6070,plain,
% 7.71/1.51      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.71/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.71/1.51      inference(light_normalisation,[status(thm)],[c_6069,c_2565]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_53,plain,
% 7.71/1.51      ( v1_funct_1(sK2) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_6368,plain,
% 7.71/1.51      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_6070,c_53]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_22,plain,
% 7.71/1.51      ( ~ v2_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X1)
% 7.71/1.51      | ~ v1_relat_1(X0)
% 7.71/1.51      | ~ v1_relat_1(X1)
% 7.71/1.51      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 7.71/1.51      | k2_funct_1(X0) = X1
% 7.71/1.51      | k2_relat_1(X1) != k1_relat_1(X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f125]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1588,plain,
% 7.71/1.51      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 7.71/1.51      | k2_funct_1(X1) = X0
% 7.71/1.51      | k2_relat_1(X0) != k1_relat_1(X1)
% 7.71/1.51      | v2_funct_1(X1) != iProver_top
% 7.71/1.51      | v1_funct_1(X1) != iProver_top
% 7.71/1.51      | v1_funct_1(X0) != iProver_top
% 7.71/1.51      | v1_relat_1(X1) != iProver_top
% 7.71/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8474,plain,
% 7.71/1.51      ( k2_funct_1(sK3) = sK2
% 7.71/1.51      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 7.71/1.51      | k2_relat_1(sK2) != k1_relat_1(sK3)
% 7.71/1.51      | v2_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_funct_1(sK2) != iProver_top
% 7.71/1.51      | v1_relat_1(sK3) != iProver_top
% 7.71/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_6368,c_1588]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_24,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1587,plain,
% 7.71/1.51      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2747,plain,
% 7.71/1.51      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1569,c_1587]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_46,negated_conjecture,
% 7.71/1.51      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.71/1.51      inference(cnf_transformation,[],[f116]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2748,plain,
% 7.71/1.51      ( k2_relat_1(sK2) = sK1 ),
% 7.71/1.51      inference(light_normalisation,[status(thm)],[c_2747,c_46]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2746,plain,
% 7.71/1.51      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1572,c_1587]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_31,plain,
% 7.71/1.51      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.71/1.51      | ~ v1_funct_2(X2,X0,X1)
% 7.71/1.51      | ~ v1_funct_2(X3,X1,X0)
% 7.71/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.71/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.71/1.51      | ~ v1_funct_1(X2)
% 7.71/1.51      | ~ v1_funct_1(X3)
% 7.71/1.51      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.71/1.51      inference(cnf_transformation,[],[f100]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_586,plain,
% 7.71/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.51      | ~ v1_funct_2(X3,X2,X1)
% 7.71/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.71/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X3)
% 7.71/1.51      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.71/1.51      | k2_relset_1(X1,X2,X0) = X2
% 7.71/1.51      | k6_partfun1(X2) != k6_partfun1(sK0)
% 7.71/1.51      | sK0 != X2 ),
% 7.71/1.51      inference(resolution_lifted,[status(thm)],[c_31,c_45]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_587,plain,
% 7.71/1.51      ( ~ v1_funct_2(X0,X1,sK0)
% 7.71/1.51      | ~ v1_funct_2(X2,sK0,X1)
% 7.71/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.71/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X2)
% 7.71/1.51      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.71/1.51      | k2_relset_1(X1,sK0,X0) = sK0
% 7.71/1.51      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.71/1.51      inference(unflattening,[status(thm)],[c_586]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_682,plain,
% 7.71/1.51      ( ~ v1_funct_2(X0,X1,sK0)
% 7.71/1.51      | ~ v1_funct_2(X2,sK0,X1)
% 7.71/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.71/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X2)
% 7.71/1.51      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.71/1.51      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.71/1.51      inference(equality_resolution_simp,[status(thm)],[c_587]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1563,plain,
% 7.71/1.51      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.71/1.51      | k2_relset_1(X0,sK0,X2) = sK0
% 7.71/1.51      | v1_funct_2(X2,X0,sK0) != iProver_top
% 7.71/1.51      | v1_funct_2(X1,sK0,X0) != iProver_top
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.71/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.71/1.51      | v1_funct_1(X2) != iProver_top
% 7.71/1.51      | v1_funct_1(X1) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2117,plain,
% 7.71/1.51      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.71/1.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.71/1.51      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.71/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.71/1.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.71/1.51      inference(equality_resolution,[status(thm)],[c_1563]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_51,negated_conjecture,
% 7.71/1.51      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.71/1.51      inference(cnf_transformation,[],[f111]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_54,plain,
% 7.71/1.51      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_55,plain,
% 7.71/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_48,negated_conjecture,
% 7.71/1.51      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f114]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_57,plain,
% 7.71/1.51      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_58,plain,
% 7.71/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2572,plain,
% 7.71/1.51      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_2117,c_53,c_54,c_55,c_56,c_57,c_58]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2749,plain,
% 7.71/1.51      ( k2_relat_1(sK3) = sK0 ),
% 7.71/1.51      inference(light_normalisation,[status(thm)],[c_2746,c_2572]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8475,plain,
% 7.71/1.51      ( k2_funct_1(sK3) = sK2
% 7.71/1.51      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 7.71/1.51      | k1_relat_1(sK3) != sK1
% 7.71/1.51      | v2_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_funct_1(sK2) != iProver_top
% 7.71/1.51      | v1_relat_1(sK3) != iProver_top
% 7.71/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.71/1.51      inference(light_normalisation,[status(thm)],[c_8474,c_2748,c_2749]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8476,plain,
% 7.71/1.51      ( k2_funct_1(sK3) = sK2
% 7.71/1.51      | k1_relat_1(sK3) != sK1
% 7.71/1.51      | v2_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_funct_1(sK2) != iProver_top
% 7.71/1.51      | v1_relat_1(sK3) != iProver_top
% 7.71/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.71/1.51      inference(equality_resolution_simp,[status(thm)],[c_8475]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_43,negated_conjecture,
% 7.71/1.51      ( k1_xboole_0 != sK0 ),
% 7.71/1.51      inference(cnf_transformation,[],[f119]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2,plain,
% 7.71/1.51      ( r1_tarski(X0,X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f128]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_164,plain,
% 7.71/1.51      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_0,plain,
% 7.71/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.71/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_168,plain,
% 7.71/1.51      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.71/1.51      | k1_xboole_0 = k1_xboole_0 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_912,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1706,plain,
% 7.71/1.51      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_912]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1707,plain,
% 7.71/1.51      ( sK0 != k1_xboole_0
% 7.71/1.51      | k1_xboole_0 = sK0
% 7.71/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_1706]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.71/1.51      | ~ v1_relat_1(X1)
% 7.71/1.51      | v1_relat_1(X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1725,plain,
% 7.71/1.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 7.71/1.51      | ~ v1_relat_1(X0)
% 7.71/1.51      | v1_relat_1(sK3) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2026,plain,
% 7.71/1.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.71/1.51      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 7.71/1.51      | v1_relat_1(sK3) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_1725]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2646,plain,
% 7.71/1.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.71/1.51      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 7.71/1.51      | v1_relat_1(sK3) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_2026]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2647,plain,
% 7.71/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.71/1.51      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.71/1.51      | v1_relat_1(sK3) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_2646]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_6,plain,
% 7.71/1.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.71/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2839,plain,
% 7.71/1.51      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2840,plain,
% 7.71/1.51      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_2839]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1600,plain,
% 7.71/1.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1601,plain,
% 7.71/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.71/1.51      | v1_relat_1(X1) != iProver_top
% 7.71/1.51      | v1_relat_1(X0) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3079,plain,
% 7.71/1.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.71/1.51      | v1_relat_1(sK2) = iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1569,c_1601]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3155,plain,
% 7.71/1.51      ( v1_relat_1(sK2) = iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1600,c_3079]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_17,plain,
% 7.71/1.51      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.71/1.51      inference(cnf_transformation,[],[f124]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3334,plain,
% 7.71/1.51      ( v2_funct_1(k6_partfun1(sK0)) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_17]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3335,plain,
% 7.71/1.51      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_3334]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_33,plain,
% 7.71/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.51      | ~ v1_funct_2(X3,X4,X1)
% 7.71/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 7.71/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | v2_funct_1(X0)
% 7.71/1.51      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X3)
% 7.71/1.51      | k2_relset_1(X4,X1,X3) != X1
% 7.71/1.51      | k1_xboole_0 = X2 ),
% 7.71/1.51      inference(cnf_transformation,[],[f103]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1581,plain,
% 7.71/1.51      ( k2_relset_1(X0,X1,X2) != X1
% 7.71/1.51      | k1_xboole_0 = X3
% 7.71/1.51      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.71/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.71/1.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.51      | v2_funct_1(X4) = iProver_top
% 7.71/1.51      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 7.71/1.51      | v1_funct_1(X4) != iProver_top
% 7.71/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8850,plain,
% 7.71/1.51      ( k1_xboole_0 = X0
% 7.71/1.51      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.71/1.51      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.71/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.71/1.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.71/1.51      | v2_funct_1(X1) = iProver_top
% 7.71/1.51      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.71/1.51      | v1_funct_1(X1) != iProver_top
% 7.71/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_46,c_1581]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8893,plain,
% 7.71/1.51      ( v1_funct_1(X1) != iProver_top
% 7.71/1.51      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.71/1.51      | v2_funct_1(X1) = iProver_top
% 7.71/1.51      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.71/1.51      | k1_xboole_0 = X0
% 7.71/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_8850,c_53,c_54,c_55]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8894,plain,
% 7.71/1.51      ( k1_xboole_0 = X0
% 7.71/1.51      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.71/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.71/1.51      | v2_funct_1(X1) = iProver_top
% 7.71/1.51      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.71/1.51      | v1_funct_1(X1) != iProver_top ),
% 7.71/1.51      inference(renaming,[status(thm)],[c_8893]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8897,plain,
% 7.71/1.51      ( sK0 = k1_xboole_0
% 7.71/1.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.71/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.71/1.51      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.71/1.51      | v2_funct_1(sK3) = iProver_top
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_2565,c_8894]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8955,plain,
% 7.71/1.51      ( v2_funct_1(sK3) = iProver_top ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_8897,c_56,c_57,c_58,c_43,c_164,c_168,c_1707,c_3335]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_21,plain,
% 7.71/1.51      ( ~ v2_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_relat_1(X0)
% 7.71/1.51      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1589,plain,
% 7.71/1.51      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 7.71/1.51      | v2_funct_1(X0) != iProver_top
% 7.71/1.51      | v1_funct_1(X0) != iProver_top
% 7.71/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8961,plain,
% 7.71/1.51      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_8955,c_1589]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_40,plain,
% 7.71/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | ~ v2_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | k2_relset_1(X1,X2,X0) != X2
% 7.71/1.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.71/1.51      | k1_xboole_0 = X2 ),
% 7.71/1.51      inference(cnf_transformation,[],[f108]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1574,plain,
% 7.71/1.51      ( k2_relset_1(X0,X1,X2) != X1
% 7.71/1.51      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 7.71/1.51      | k1_xboole_0 = X1
% 7.71/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.51      | v2_funct_1(X2) != iProver_top
% 7.71/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3644,plain,
% 7.71/1.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.71/1.51      | sK0 = k1_xboole_0
% 7.71/1.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.71/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.71/1.51      | v2_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_2572,c_1574]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_5078,plain,
% 7.71/1.51      ( v2_funct_1(sK3) != iProver_top
% 7.71/1.51      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_3644,c_56,c_57,c_58,c_43,c_164,c_168,c_1707]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_5079,plain,
% 7.71/1.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.71/1.51      | v2_funct_1(sK3) != iProver_top ),
% 7.71/1.51      inference(renaming,[status(thm)],[c_5078]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8965,plain,
% 7.71/1.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_8955,c_5079]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8967,plain,
% 7.71/1.51      ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.71/1.51      inference(demodulation,[status(thm)],[c_8961,c_8965]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_9,plain,
% 7.71/1.51      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.71/1.51      inference(cnf_transformation,[],[f123]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8968,plain,
% 7.71/1.51      ( k1_relat_1(sK3) = sK1
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.71/1.51      inference(demodulation,[status(thm)],[c_8967,c_9]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_12716,plain,
% 7.71/1.51      ( k2_funct_1(sK3) = sK2 ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_8476,c_53,c_56,c_57,c_58,c_43,c_164,c_168,c_1707,
% 7.71/1.51                 c_2647,c_2840,c_3155,c_3335,c_8897,c_8968]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_12722,plain,
% 7.71/1.51      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 7.71/1.51      inference(demodulation,[status(thm)],[c_12716,c_8965]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_14772,plain,
% 7.71/1.51      ( k2_funct_1(sK2) = sK3
% 7.71/1.51      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
% 7.71/1.51      | k2_relat_1(sK3) != k1_relat_1(sK2)
% 7.71/1.51      | v2_funct_1(sK2) != iProver_top
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_funct_1(sK2) != iProver_top
% 7.71/1.51      | v1_relat_1(sK3) != iProver_top
% 7.71/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_12722,c_1588]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_44,negated_conjecture,
% 7.71/1.51      ( v2_funct_1(sK2) ),
% 7.71/1.51      inference(cnf_transformation,[],[f118]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1573,plain,
% 7.71/1.51      ( v2_funct_1(sK2) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3846,plain,
% 7.71/1.51      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 7.71/1.51      | v1_funct_1(sK2) != iProver_top
% 7.71/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1573,c_1589]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_4001,plain,
% 7.71/1.51      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_3846,c_53,c_3155]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3643,plain,
% 7.71/1.51      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.71/1.51      | sK1 = k1_xboole_0
% 7.71/1.51      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.71/1.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.71/1.51      | v2_funct_1(sK2) != iProver_top
% 7.71/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_46,c_1574]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_42,negated_conjecture,
% 7.71/1.51      ( k1_xboole_0 != sK1 ),
% 7.71/1.51      inference(cnf_transformation,[],[f120]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1668,plain,
% 7.71/1.51      ( ~ v1_funct_2(X0,X1,sK1)
% 7.71/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.71/1.51      | ~ v2_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | k2_relset_1(X1,sK1,X0) != sK1
% 7.71/1.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.71/1.51      | k1_xboole_0 = sK1 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_40]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1806,plain,
% 7.71/1.51      ( ~ v1_funct_2(sK2,X0,sK1)
% 7.71/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 7.71/1.51      | ~ v2_funct_1(sK2)
% 7.71/1.51      | ~ v1_funct_1(sK2)
% 7.71/1.51      | k2_relset_1(X0,sK1,sK2) != sK1
% 7.71/1.51      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 7.71/1.51      | k1_xboole_0 = sK1 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_1668]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1931,plain,
% 7.71/1.51      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.71/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.71/1.51      | ~ v2_funct_1(sK2)
% 7.71/1.51      | ~ v1_funct_1(sK2)
% 7.71/1.51      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.71/1.51      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.71/1.51      | k1_xboole_0 = sK1 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_1806]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3856,plain,
% 7.71/1.51      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_3643,c_52,c_51,c_50,c_46,c_44,c_42,c_1931]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_4003,plain,
% 7.71/1.51      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 7.71/1.51      inference(light_normalisation,[status(thm)],[c_4001,c_3856]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_4004,plain,
% 7.71/1.51      ( k1_relat_1(sK2) = sK0 ),
% 7.71/1.51      inference(demodulation,[status(thm)],[c_4003,c_9]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_14783,plain,
% 7.71/1.51      ( k2_funct_1(sK2) = sK3
% 7.71/1.51      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 7.71/1.51      | sK0 != sK0
% 7.71/1.51      | v2_funct_1(sK2) != iProver_top
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_funct_1(sK2) != iProver_top
% 7.71/1.51      | v1_relat_1(sK3) != iProver_top
% 7.71/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.71/1.51      inference(light_normalisation,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_14772,c_2748,c_2749,c_4004]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_14784,plain,
% 7.71/1.51      ( k2_funct_1(sK2) = sK3
% 7.71/1.51      | v2_funct_1(sK2) != iProver_top
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top
% 7.71/1.51      | v1_funct_1(sK2) != iProver_top
% 7.71/1.51      | v1_relat_1(sK3) != iProver_top
% 7.71/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.71/1.51      inference(equality_resolution_simp,[status(thm)],[c_14783]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_41,negated_conjecture,
% 7.71/1.51      ( k2_funct_1(sK2) != sK3 ),
% 7.71/1.51      inference(cnf_transformation,[],[f121]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_60,plain,
% 7.71/1.51      ( v2_funct_1(sK2) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(contradiction,plain,
% 7.71/1.51      ( $false ),
% 7.71/1.51      inference(minisat,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_14784,c_3155,c_2840,c_2647,c_41,c_60,c_58,c_56,c_53]) ).
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.71/1.51  
% 7.71/1.51  ------                               Statistics
% 7.71/1.51  
% 7.71/1.51  ------ General
% 7.71/1.51  
% 7.71/1.51  abstr_ref_over_cycles:                  0
% 7.71/1.51  abstr_ref_under_cycles:                 0
% 7.71/1.51  gc_basic_clause_elim:                   0
% 7.71/1.51  forced_gc_time:                         0
% 7.71/1.51  parsing_time:                           0.014
% 7.71/1.51  unif_index_cands_time:                  0.
% 7.71/1.51  unif_index_add_time:                    0.
% 7.71/1.51  orderings_time:                         0.
% 7.71/1.51  out_proof_time:                         0.015
% 7.71/1.51  total_time:                             0.617
% 7.71/1.51  num_of_symbols:                         53
% 7.71/1.51  num_of_terms:                           21811
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing
% 7.71/1.51  
% 7.71/1.51  num_of_splits:                          0
% 7.71/1.51  num_of_split_atoms:                     0
% 7.71/1.51  num_of_reused_defs:                     0
% 7.71/1.51  num_eq_ax_congr_red:                    2
% 7.71/1.51  num_of_sem_filtered_clauses:            1
% 7.71/1.51  num_of_subtypes:                        0
% 7.71/1.51  monotx_restored_types:                  0
% 7.71/1.51  sat_num_of_epr_types:                   0
% 7.71/1.51  sat_num_of_non_cyclic_types:            0
% 7.71/1.51  sat_guarded_non_collapsed_types:        0
% 7.71/1.51  num_pure_diseq_elim:                    0
% 7.71/1.51  simp_replaced_by:                       0
% 7.71/1.51  res_preprocessed:                       226
% 7.71/1.51  prep_upred:                             0
% 7.71/1.51  prep_unflattend:                        12
% 7.71/1.51  smt_new_axioms:                         0
% 7.71/1.51  pred_elim_cands:                        6
% 7.71/1.51  pred_elim:                              2
% 7.71/1.51  pred_elim_cl:                           3
% 7.71/1.51  pred_elim_cycles:                       4
% 7.71/1.51  merged_defs:                            0
% 7.71/1.51  merged_defs_ncl:                        0
% 7.71/1.51  bin_hyper_res:                          0
% 7.71/1.51  prep_cycles:                            4
% 7.71/1.51  pred_elim_time:                         0.006
% 7.71/1.51  splitting_time:                         0.
% 7.71/1.51  sem_filter_time:                        0.
% 7.71/1.51  monotx_time:                            0.001
% 7.71/1.51  subtype_inf_time:                       0.
% 7.71/1.51  
% 7.71/1.51  ------ Problem properties
% 7.71/1.51  
% 7.71/1.51  clauses:                                47
% 7.71/1.51  conjectures:                            11
% 7.71/1.51  epr:                                    9
% 7.71/1.51  horn:                                   43
% 7.71/1.51  ground:                                 12
% 7.71/1.51  unary:                                  17
% 7.71/1.51  binary:                                 2
% 7.71/1.51  lits:                                   182
% 7.71/1.51  lits_eq:                                38
% 7.71/1.51  fd_pure:                                0
% 7.71/1.51  fd_pseudo:                              0
% 7.71/1.51  fd_cond:                                4
% 7.71/1.51  fd_pseudo_cond:                         2
% 7.71/1.51  ac_symbols:                             0
% 7.71/1.51  
% 7.71/1.51  ------ Propositional Solver
% 7.71/1.51  
% 7.71/1.51  prop_solver_calls:                      31
% 7.71/1.51  prop_fast_solver_calls:                 2533
% 7.71/1.51  smt_solver_calls:                       0
% 7.71/1.51  smt_fast_solver_calls:                  0
% 7.71/1.51  prop_num_of_clauses:                    7502
% 7.71/1.51  prop_preprocess_simplified:             15813
% 7.71/1.51  prop_fo_subsumed:                       215
% 7.71/1.51  prop_solver_time:                       0.
% 7.71/1.51  smt_solver_time:                        0.
% 7.71/1.51  smt_fast_solver_time:                   0.
% 7.71/1.51  prop_fast_solver_time:                  0.
% 7.71/1.51  prop_unsat_core_time:                   0.001
% 7.71/1.51  
% 7.71/1.51  ------ QBF
% 7.71/1.51  
% 7.71/1.51  qbf_q_res:                              0
% 7.71/1.51  qbf_num_tautologies:                    0
% 7.71/1.51  qbf_prep_cycles:                        0
% 7.71/1.51  
% 7.71/1.51  ------ BMC1
% 7.71/1.51  
% 7.71/1.51  bmc1_current_bound:                     -1
% 7.71/1.51  bmc1_last_solved_bound:                 -1
% 7.71/1.51  bmc1_unsat_core_size:                   -1
% 7.71/1.51  bmc1_unsat_core_parents_size:           -1
% 7.71/1.51  bmc1_merge_next_fun:                    0
% 7.71/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.71/1.51  
% 7.71/1.51  ------ Instantiation
% 7.71/1.51  
% 7.71/1.51  inst_num_of_clauses:                    2027
% 7.71/1.51  inst_num_in_passive:                    190
% 7.71/1.51  inst_num_in_active:                     830
% 7.71/1.51  inst_num_in_unprocessed:                1007
% 7.71/1.51  inst_num_of_loops:                      930
% 7.71/1.51  inst_num_of_learning_restarts:          0
% 7.71/1.51  inst_num_moves_active_passive:          98
% 7.71/1.51  inst_lit_activity:                      0
% 7.71/1.51  inst_lit_activity_moves:                1
% 7.71/1.51  inst_num_tautologies:                   0
% 7.71/1.51  inst_num_prop_implied:                  0
% 7.71/1.51  inst_num_existing_simplified:           0
% 7.71/1.51  inst_num_eq_res_simplified:             0
% 7.71/1.51  inst_num_child_elim:                    0
% 7.71/1.51  inst_num_of_dismatching_blockings:      403
% 7.71/1.51  inst_num_of_non_proper_insts:           1920
% 7.71/1.51  inst_num_of_duplicates:                 0
% 7.71/1.51  inst_inst_num_from_inst_to_res:         0
% 7.71/1.51  inst_dismatching_checking_time:         0.
% 7.71/1.51  
% 7.71/1.51  ------ Resolution
% 7.71/1.51  
% 7.71/1.51  res_num_of_clauses:                     0
% 7.71/1.51  res_num_in_passive:                     0
% 7.71/1.51  res_num_in_active:                      0
% 7.71/1.51  res_num_of_loops:                       230
% 7.71/1.51  res_forward_subset_subsumed:            128
% 7.71/1.51  res_backward_subset_subsumed:           0
% 7.71/1.51  res_forward_subsumed:                   0
% 7.71/1.51  res_backward_subsumed:                  0
% 7.71/1.51  res_forward_subsumption_resolution:     2
% 7.71/1.51  res_backward_subsumption_resolution:    0
% 7.71/1.51  res_clause_to_clause_subsumption:       877
% 7.71/1.51  res_orphan_elimination:                 0
% 7.71/1.51  res_tautology_del:                      64
% 7.71/1.51  res_num_eq_res_simplified:              1
% 7.71/1.51  res_num_sel_changes:                    0
% 7.71/1.51  res_moves_from_active_to_pass:          0
% 7.71/1.51  
% 7.71/1.51  ------ Superposition
% 7.71/1.51  
% 7.71/1.51  sup_time_total:                         0.
% 7.71/1.51  sup_time_generating:                    0.
% 7.71/1.51  sup_time_sim_full:                      0.
% 7.71/1.51  sup_time_sim_immed:                     0.
% 7.71/1.51  
% 7.71/1.51  sup_num_of_clauses:                     380
% 7.71/1.51  sup_num_in_active:                      147
% 7.71/1.51  sup_num_in_passive:                     233
% 7.71/1.51  sup_num_of_loops:                       185
% 7.71/1.51  sup_fw_superposition:                   223
% 7.71/1.51  sup_bw_superposition:                   260
% 7.71/1.51  sup_immediate_simplified:               206
% 7.71/1.51  sup_given_eliminated:                   0
% 7.71/1.51  comparisons_done:                       0
% 7.71/1.51  comparisons_avoided:                    4
% 7.71/1.51  
% 7.71/1.51  ------ Simplifications
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  sim_fw_subset_subsumed:                 30
% 7.71/1.51  sim_bw_subset_subsumed:                 30
% 7.71/1.51  sim_fw_subsumed:                        30
% 7.71/1.51  sim_bw_subsumed:                        2
% 7.71/1.51  sim_fw_subsumption_res:                 0
% 7.71/1.51  sim_bw_subsumption_res:                 0
% 7.71/1.51  sim_tautology_del:                      0
% 7.71/1.51  sim_eq_tautology_del:                   54
% 7.71/1.51  sim_eq_res_simp:                        3
% 7.71/1.51  sim_fw_demodulated:                     36
% 7.71/1.51  sim_bw_demodulated:                     21
% 7.71/1.51  sim_light_normalised:                   153
% 7.71/1.51  sim_joinable_taut:                      0
% 7.71/1.51  sim_joinable_simp:                      0
% 7.71/1.51  sim_ac_normalised:                      0
% 7.71/1.51  sim_smt_subsumption:                    0
% 7.71/1.51  
%------------------------------------------------------------------------------
