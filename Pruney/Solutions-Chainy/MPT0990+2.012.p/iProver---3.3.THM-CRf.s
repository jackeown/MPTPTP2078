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
% DateTime   : Thu Dec  3 12:02:58 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :  215 (2031 expanded)
%              Number of clauses        :  121 ( 550 expanded)
%              Number of leaves         :   23 ( 525 expanded)
%              Depth                    :   21
%              Number of atoms          :  923 (18262 expanded)
%              Number of equality atoms :  412 (6524 expanded)
%              Maximal formula depth    :   16 (   6 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
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
    inference(flattening,[],[f58])).

fof(f67,plain,(
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

fof(f66,plain,
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

fof(f68,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f59,f67,f66])).

fof(f113,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f68])).

fof(f116,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f68])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f114,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f68])).

fof(f111,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f118,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f68])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f82,f100])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f117,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f68])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

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
    inference(flattening,[],[f50])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f112,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f115,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f14,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f120,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f68])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f60])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f125,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f119,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f77,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f80,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
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
    inference(flattening,[],[f56])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f121,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f68])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f20])).

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
    inference(flattening,[],[f52])).

fof(f104,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f83,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f122,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_50,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2133,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_47,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2136,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2146,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7646,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2136,c_2146])).

cnf(c_49,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_56,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_7877,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7646,c_56])).

cnf(c_7878,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7877])).

cnf(c_7889,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2133,c_7878])).

cnf(c_52,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2858,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3568,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2858])).

cnf(c_4016,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3568])).

cnf(c_5675,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4016])).

cnf(c_8153,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7889,c_52,c_50,c_49,c_47,c_5675])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2166,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_20,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_45,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_703,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_45])).

cnf(c_704,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_29,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_712,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_704,c_29])).

cnf(c_2127,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_3528,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2166,c_2127])).

cnf(c_8156,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | r1_tarski(k5_relat_1(sK2,sK3),k2_zfmisc_1(sK0,sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8153,c_3528])).

cnf(c_53,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_55,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_58,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_8157,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8153,c_2127])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2149,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10090,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8153,c_2149])).

cnf(c_12011,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8156,c_53,c_55,c_56,c_58,c_8157,c_10090])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2160,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k2_funct_1(X1) = X0
    | v2_funct_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12023,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_12011,c_2160])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2156,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3820,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2133,c_2156])).

cnf(c_46,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_3822,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3820,c_46])).

cnf(c_3819,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2136,c_2156])).

cnf(c_31,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_716,plain,
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
    inference(resolution_lifted,[status(thm)],[c_31,c_45])).

cnf(c_717,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_716])).

cnf(c_814,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_717])).

cnf(c_2126,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_814])).

cnf(c_2824,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2126])).

cnf(c_51,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_54,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_48,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_57,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_3175,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2824,c_53,c_54,c_55,c_56,c_57,c_58])).

cnf(c_3825,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3819,c_3175])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2150,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6644,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2136,c_2150])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2157,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3938,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2136,c_2157])).

cnf(c_6656,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6644,c_3938])).

cnf(c_43,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_172,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_176,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1152,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2741,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_2742,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2741])).

cnf(c_6788,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6656,c_57,c_43,c_172,c_176,c_2742])).

cnf(c_12033,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | sK1 != sK1
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12023,c_3822,c_3825,c_6788])).

cnf(c_12034,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12033])).

cnf(c_44,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_60,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2632,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2633,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2632])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2638,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2639,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2638])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2652,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2653,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2652])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2665,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2666,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2665])).

cnf(c_2668,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2669,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2668])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2138,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_6481,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_46,c_2138])).

cnf(c_42,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_2878,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_3543,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2878])).

cnf(c_3954,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3543])).

cnf(c_6733,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6481,c_52,c_51,c_50,c_46,c_44,c_42,c_3954])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v2_funct_1(X1)
    | v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2161,plain,
    ( v2_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7584,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6733,c_2161])).

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
    inference(cnf_transformation,[],[f104])).

cnf(c_2144,plain,
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

cnf(c_11104,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_46,c_2144])).

cnf(c_11194,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11104,c_53,c_54,c_55])).

cnf(c_11195,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11194])).

cnf(c_11204,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8153,c_11195])).

cnf(c_11354,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11204,c_56,c_57,c_58,c_43,c_172,c_176,c_2742])).

cnf(c_11355,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_11354])).

cnf(c_12014,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12011,c_11355])).

cnf(c_14298,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12034,c_53,c_55,c_56,c_58,c_60,c_2633,c_2639,c_2653,c_2666,c_2669,c_7584,c_12014])).

cnf(c_12130,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12014,c_53,c_55,c_60,c_2633,c_2639,c_2653,c_2669,c_7584])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2159,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12135,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12130,c_2159])).

cnf(c_12322,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12135,c_56,c_58,c_2666])).

cnf(c_14301,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_14298,c_12322])).

cnf(c_41,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f122])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14301,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.41/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/1.52  
% 6.41/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.41/1.52  
% 6.41/1.52  ------  iProver source info
% 6.41/1.52  
% 6.41/1.52  git: date: 2020-06-30 10:37:57 +0100
% 6.41/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.41/1.52  git: non_committed_changes: false
% 6.41/1.52  git: last_make_outside_of_git: false
% 6.41/1.52  
% 6.41/1.52  ------ 
% 6.41/1.52  
% 6.41/1.52  ------ Input Options
% 6.41/1.52  
% 6.41/1.52  --out_options                           all
% 6.41/1.52  --tptp_safe_out                         true
% 6.41/1.52  --problem_path                          ""
% 6.41/1.52  --include_path                          ""
% 6.41/1.52  --clausifier                            res/vclausify_rel
% 6.41/1.52  --clausifier_options                    --mode clausify
% 6.41/1.52  --stdin                                 false
% 6.41/1.52  --stats_out                             all
% 6.41/1.52  
% 6.41/1.52  ------ General Options
% 6.41/1.52  
% 6.41/1.52  --fof                                   false
% 6.41/1.52  --time_out_real                         305.
% 6.41/1.52  --time_out_virtual                      -1.
% 6.41/1.52  --symbol_type_check                     false
% 6.41/1.52  --clausify_out                          false
% 6.41/1.52  --sig_cnt_out                           false
% 6.41/1.52  --trig_cnt_out                          false
% 6.41/1.52  --trig_cnt_out_tolerance                1.
% 6.41/1.52  --trig_cnt_out_sk_spl                   false
% 6.41/1.52  --abstr_cl_out                          false
% 6.41/1.52  
% 6.41/1.52  ------ Global Options
% 6.41/1.52  
% 6.41/1.52  --schedule                              default
% 6.41/1.52  --add_important_lit                     false
% 6.41/1.52  --prop_solver_per_cl                    1000
% 6.41/1.52  --min_unsat_core                        false
% 6.41/1.52  --soft_assumptions                      false
% 6.41/1.52  --soft_lemma_size                       3
% 6.41/1.52  --prop_impl_unit_size                   0
% 6.41/1.52  --prop_impl_unit                        []
% 6.41/1.52  --share_sel_clauses                     true
% 6.41/1.52  --reset_solvers                         false
% 6.41/1.52  --bc_imp_inh                            [conj_cone]
% 6.41/1.52  --conj_cone_tolerance                   3.
% 6.41/1.52  --extra_neg_conj                        none
% 6.41/1.52  --large_theory_mode                     true
% 6.41/1.52  --prolific_symb_bound                   200
% 6.41/1.52  --lt_threshold                          2000
% 6.41/1.52  --clause_weak_htbl                      true
% 6.41/1.52  --gc_record_bc_elim                     false
% 6.41/1.52  
% 6.41/1.52  ------ Preprocessing Options
% 6.41/1.52  
% 6.41/1.52  --preprocessing_flag                    true
% 6.41/1.52  --time_out_prep_mult                    0.1
% 6.41/1.52  --splitting_mode                        input
% 6.41/1.52  --splitting_grd                         true
% 6.41/1.52  --splitting_cvd                         false
% 6.41/1.52  --splitting_cvd_svl                     false
% 6.41/1.52  --splitting_nvd                         32
% 6.41/1.52  --sub_typing                            true
% 6.41/1.52  --prep_gs_sim                           true
% 6.41/1.52  --prep_unflatten                        true
% 6.41/1.52  --prep_res_sim                          true
% 6.41/1.52  --prep_upred                            true
% 6.41/1.52  --prep_sem_filter                       exhaustive
% 6.41/1.52  --prep_sem_filter_out                   false
% 6.41/1.52  --pred_elim                             true
% 6.41/1.52  --res_sim_input                         true
% 6.41/1.52  --eq_ax_congr_red                       true
% 6.41/1.52  --pure_diseq_elim                       true
% 6.41/1.52  --brand_transform                       false
% 6.41/1.52  --non_eq_to_eq                          false
% 6.41/1.52  --prep_def_merge                        true
% 6.41/1.52  --prep_def_merge_prop_impl              false
% 6.41/1.52  --prep_def_merge_mbd                    true
% 6.41/1.52  --prep_def_merge_tr_red                 false
% 6.41/1.52  --prep_def_merge_tr_cl                  false
% 6.41/1.52  --smt_preprocessing                     true
% 6.41/1.52  --smt_ac_axioms                         fast
% 6.41/1.52  --preprocessed_out                      false
% 6.41/1.52  --preprocessed_stats                    false
% 6.41/1.52  
% 6.41/1.52  ------ Abstraction refinement Options
% 6.41/1.52  
% 6.41/1.52  --abstr_ref                             []
% 6.41/1.52  --abstr_ref_prep                        false
% 6.41/1.52  --abstr_ref_until_sat                   false
% 6.41/1.52  --abstr_ref_sig_restrict                funpre
% 6.41/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 6.41/1.52  --abstr_ref_under                       []
% 6.41/1.52  
% 6.41/1.52  ------ SAT Options
% 6.41/1.52  
% 6.41/1.52  --sat_mode                              false
% 6.41/1.52  --sat_fm_restart_options                ""
% 6.41/1.52  --sat_gr_def                            false
% 6.41/1.52  --sat_epr_types                         true
% 6.41/1.52  --sat_non_cyclic_types                  false
% 6.41/1.52  --sat_finite_models                     false
% 6.41/1.52  --sat_fm_lemmas                         false
% 6.41/1.52  --sat_fm_prep                           false
% 6.41/1.52  --sat_fm_uc_incr                        true
% 6.41/1.52  --sat_out_model                         small
% 6.41/1.52  --sat_out_clauses                       false
% 6.41/1.52  
% 6.41/1.52  ------ QBF Options
% 6.41/1.52  
% 6.41/1.52  --qbf_mode                              false
% 6.41/1.52  --qbf_elim_univ                         false
% 6.41/1.52  --qbf_dom_inst                          none
% 6.41/1.52  --qbf_dom_pre_inst                      false
% 6.41/1.52  --qbf_sk_in                             false
% 6.41/1.52  --qbf_pred_elim                         true
% 6.41/1.52  --qbf_split                             512
% 6.41/1.52  
% 6.41/1.52  ------ BMC1 Options
% 6.41/1.52  
% 6.41/1.52  --bmc1_incremental                      false
% 6.41/1.52  --bmc1_axioms                           reachable_all
% 6.41/1.52  --bmc1_min_bound                        0
% 6.41/1.52  --bmc1_max_bound                        -1
% 6.41/1.52  --bmc1_max_bound_default                -1
% 6.41/1.52  --bmc1_symbol_reachability              true
% 6.41/1.52  --bmc1_property_lemmas                  false
% 6.41/1.52  --bmc1_k_induction                      false
% 6.41/1.52  --bmc1_non_equiv_states                 false
% 6.41/1.52  --bmc1_deadlock                         false
% 6.41/1.52  --bmc1_ucm                              false
% 6.41/1.52  --bmc1_add_unsat_core                   none
% 6.41/1.52  --bmc1_unsat_core_children              false
% 6.41/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 6.41/1.52  --bmc1_out_stat                         full
% 6.41/1.52  --bmc1_ground_init                      false
% 6.41/1.52  --bmc1_pre_inst_next_state              false
% 6.41/1.52  --bmc1_pre_inst_state                   false
% 6.41/1.52  --bmc1_pre_inst_reach_state             false
% 6.41/1.52  --bmc1_out_unsat_core                   false
% 6.41/1.52  --bmc1_aig_witness_out                  false
% 6.41/1.52  --bmc1_verbose                          false
% 6.41/1.52  --bmc1_dump_clauses_tptp                false
% 6.41/1.52  --bmc1_dump_unsat_core_tptp             false
% 6.41/1.52  --bmc1_dump_file                        -
% 6.41/1.52  --bmc1_ucm_expand_uc_limit              128
% 6.41/1.52  --bmc1_ucm_n_expand_iterations          6
% 6.41/1.52  --bmc1_ucm_extend_mode                  1
% 6.41/1.52  --bmc1_ucm_init_mode                    2
% 6.41/1.52  --bmc1_ucm_cone_mode                    none
% 6.41/1.52  --bmc1_ucm_reduced_relation_type        0
% 6.41/1.52  --bmc1_ucm_relax_model                  4
% 6.41/1.52  --bmc1_ucm_full_tr_after_sat            true
% 6.41/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 6.41/1.52  --bmc1_ucm_layered_model                none
% 6.41/1.52  --bmc1_ucm_max_lemma_size               10
% 6.41/1.52  
% 6.41/1.52  ------ AIG Options
% 6.41/1.52  
% 6.41/1.52  --aig_mode                              false
% 6.41/1.52  
% 6.41/1.52  ------ Instantiation Options
% 6.41/1.52  
% 6.41/1.52  --instantiation_flag                    true
% 6.41/1.52  --inst_sos_flag                         false
% 6.41/1.52  --inst_sos_phase                        true
% 6.41/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.41/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.41/1.52  --inst_lit_sel_side                     num_symb
% 6.41/1.52  --inst_solver_per_active                1400
% 6.41/1.52  --inst_solver_calls_frac                1.
% 6.41/1.52  --inst_passive_queue_type               priority_queues
% 6.41/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.41/1.52  --inst_passive_queues_freq              [25;2]
% 6.41/1.52  --inst_dismatching                      true
% 6.41/1.52  --inst_eager_unprocessed_to_passive     true
% 6.41/1.52  --inst_prop_sim_given                   true
% 6.41/1.52  --inst_prop_sim_new                     false
% 6.41/1.52  --inst_subs_new                         false
% 6.41/1.52  --inst_eq_res_simp                      false
% 6.41/1.52  --inst_subs_given                       false
% 6.41/1.52  --inst_orphan_elimination               true
% 6.41/1.52  --inst_learning_loop_flag               true
% 6.41/1.52  --inst_learning_start                   3000
% 6.41/1.52  --inst_learning_factor                  2
% 6.41/1.52  --inst_start_prop_sim_after_learn       3
% 6.41/1.52  --inst_sel_renew                        solver
% 6.41/1.52  --inst_lit_activity_flag                true
% 6.41/1.52  --inst_restr_to_given                   false
% 6.41/1.52  --inst_activity_threshold               500
% 6.41/1.52  --inst_out_proof                        true
% 6.41/1.52  
% 6.41/1.52  ------ Resolution Options
% 6.41/1.52  
% 6.41/1.52  --resolution_flag                       true
% 6.41/1.52  --res_lit_sel                           adaptive
% 6.41/1.52  --res_lit_sel_side                      none
% 6.41/1.52  --res_ordering                          kbo
% 6.41/1.52  --res_to_prop_solver                    active
% 6.41/1.52  --res_prop_simpl_new                    false
% 6.41/1.52  --res_prop_simpl_given                  true
% 6.41/1.52  --res_passive_queue_type                priority_queues
% 6.41/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.41/1.52  --res_passive_queues_freq               [15;5]
% 6.41/1.52  --res_forward_subs                      full
% 6.41/1.52  --res_backward_subs                     full
% 6.41/1.52  --res_forward_subs_resolution           true
% 6.41/1.52  --res_backward_subs_resolution          true
% 6.41/1.52  --res_orphan_elimination                true
% 6.41/1.52  --res_time_limit                        2.
% 6.41/1.52  --res_out_proof                         true
% 6.41/1.52  
% 6.41/1.52  ------ Superposition Options
% 6.41/1.52  
% 6.41/1.52  --superposition_flag                    true
% 6.41/1.52  --sup_passive_queue_type                priority_queues
% 6.41/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.41/1.52  --sup_passive_queues_freq               [8;1;4]
% 6.41/1.52  --demod_completeness_check              fast
% 6.41/1.52  --demod_use_ground                      true
% 6.41/1.52  --sup_to_prop_solver                    passive
% 6.41/1.52  --sup_prop_simpl_new                    true
% 6.41/1.52  --sup_prop_simpl_given                  true
% 6.41/1.52  --sup_fun_splitting                     false
% 6.41/1.52  --sup_smt_interval                      50000
% 6.41/1.52  
% 6.41/1.52  ------ Superposition Simplification Setup
% 6.41/1.52  
% 6.41/1.52  --sup_indices_passive                   []
% 6.41/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 6.41/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.52  --sup_full_bw                           [BwDemod]
% 6.41/1.52  --sup_immed_triv                        [TrivRules]
% 6.41/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.41/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.52  --sup_immed_bw_main                     []
% 6.41/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 6.41/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.52  
% 6.41/1.52  ------ Combination Options
% 6.41/1.52  
% 6.41/1.52  --comb_res_mult                         3
% 6.41/1.52  --comb_sup_mult                         2
% 6.41/1.52  --comb_inst_mult                        10
% 6.41/1.52  
% 6.41/1.52  ------ Debug Options
% 6.41/1.52  
% 6.41/1.52  --dbg_backtrace                         false
% 6.41/1.52  --dbg_dump_prop_clauses                 false
% 6.41/1.52  --dbg_dump_prop_clauses_file            -
% 6.41/1.52  --dbg_out_stat                          false
% 6.41/1.52  ------ Parsing...
% 6.41/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.41/1.52  
% 6.41/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.41/1.52  
% 6.41/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.41/1.52  
% 6.41/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.41/1.52  ------ Proving...
% 6.41/1.52  ------ Problem Properties 
% 6.41/1.52  
% 6.41/1.52  
% 6.41/1.52  clauses                                 47
% 6.41/1.52  conjectures                             11
% 6.41/1.52  EPR                                     9
% 6.41/1.52  Horn                                    39
% 6.41/1.52  unary                                   13
% 6.41/1.52  binary                                  7
% 6.41/1.52  lits                                    178
% 6.41/1.52  lits eq                                 40
% 6.41/1.52  fd_pure                                 0
% 6.41/1.52  fd_pseudo                               0
% 6.41/1.52  fd_cond                                 7
% 6.41/1.52  fd_pseudo_cond                          2
% 6.41/1.52  AC symbols                              0
% 6.41/1.52  
% 6.41/1.52  ------ Schedule dynamic 5 is on 
% 6.41/1.52  
% 6.41/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.41/1.52  
% 6.41/1.52  
% 6.41/1.52  ------ 
% 6.41/1.52  Current options:
% 6.41/1.52  ------ 
% 6.41/1.52  
% 6.41/1.52  ------ Input Options
% 6.41/1.52  
% 6.41/1.52  --out_options                           all
% 6.41/1.52  --tptp_safe_out                         true
% 6.41/1.52  --problem_path                          ""
% 6.41/1.52  --include_path                          ""
% 6.41/1.52  --clausifier                            res/vclausify_rel
% 6.41/1.52  --clausifier_options                    --mode clausify
% 6.41/1.52  --stdin                                 false
% 6.41/1.52  --stats_out                             all
% 6.41/1.52  
% 6.41/1.52  ------ General Options
% 6.41/1.52  
% 6.41/1.52  --fof                                   false
% 6.41/1.52  --time_out_real                         305.
% 6.41/1.52  --time_out_virtual                      -1.
% 6.41/1.52  --symbol_type_check                     false
% 6.41/1.52  --clausify_out                          false
% 6.41/1.52  --sig_cnt_out                           false
% 6.41/1.52  --trig_cnt_out                          false
% 6.41/1.52  --trig_cnt_out_tolerance                1.
% 6.41/1.52  --trig_cnt_out_sk_spl                   false
% 6.41/1.52  --abstr_cl_out                          false
% 6.41/1.52  
% 6.41/1.52  ------ Global Options
% 6.41/1.52  
% 6.41/1.52  --schedule                              default
% 6.41/1.52  --add_important_lit                     false
% 6.41/1.52  --prop_solver_per_cl                    1000
% 6.41/1.52  --min_unsat_core                        false
% 6.41/1.52  --soft_assumptions                      false
% 6.41/1.52  --soft_lemma_size                       3
% 6.41/1.52  --prop_impl_unit_size                   0
% 6.41/1.52  --prop_impl_unit                        []
% 6.41/1.52  --share_sel_clauses                     true
% 6.41/1.52  --reset_solvers                         false
% 6.41/1.52  --bc_imp_inh                            [conj_cone]
% 6.41/1.52  --conj_cone_tolerance                   3.
% 6.41/1.52  --extra_neg_conj                        none
% 6.41/1.52  --large_theory_mode                     true
% 6.41/1.52  --prolific_symb_bound                   200
% 6.41/1.52  --lt_threshold                          2000
% 6.41/1.52  --clause_weak_htbl                      true
% 6.41/1.52  --gc_record_bc_elim                     false
% 6.41/1.52  
% 6.41/1.52  ------ Preprocessing Options
% 6.41/1.52  
% 6.41/1.52  --preprocessing_flag                    true
% 6.41/1.52  --time_out_prep_mult                    0.1
% 6.41/1.52  --splitting_mode                        input
% 6.41/1.52  --splitting_grd                         true
% 6.41/1.52  --splitting_cvd                         false
% 6.41/1.52  --splitting_cvd_svl                     false
% 6.41/1.52  --splitting_nvd                         32
% 6.41/1.52  --sub_typing                            true
% 6.41/1.52  --prep_gs_sim                           true
% 6.41/1.52  --prep_unflatten                        true
% 6.41/1.52  --prep_res_sim                          true
% 6.41/1.52  --prep_upred                            true
% 6.41/1.52  --prep_sem_filter                       exhaustive
% 6.41/1.52  --prep_sem_filter_out                   false
% 6.41/1.52  --pred_elim                             true
% 6.41/1.52  --res_sim_input                         true
% 6.41/1.52  --eq_ax_congr_red                       true
% 6.41/1.52  --pure_diseq_elim                       true
% 6.41/1.52  --brand_transform                       false
% 6.41/1.52  --non_eq_to_eq                          false
% 6.41/1.52  --prep_def_merge                        true
% 6.41/1.52  --prep_def_merge_prop_impl              false
% 6.41/1.52  --prep_def_merge_mbd                    true
% 6.41/1.52  --prep_def_merge_tr_red                 false
% 6.41/1.52  --prep_def_merge_tr_cl                  false
% 6.41/1.52  --smt_preprocessing                     true
% 6.41/1.52  --smt_ac_axioms                         fast
% 6.41/1.52  --preprocessed_out                      false
% 6.41/1.52  --preprocessed_stats                    false
% 6.41/1.52  
% 6.41/1.52  ------ Abstraction refinement Options
% 6.41/1.52  
% 6.41/1.52  --abstr_ref                             []
% 6.41/1.52  --abstr_ref_prep                        false
% 6.41/1.52  --abstr_ref_until_sat                   false
% 6.41/1.52  --abstr_ref_sig_restrict                funpre
% 6.41/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 6.41/1.52  --abstr_ref_under                       []
% 6.41/1.52  
% 6.41/1.52  ------ SAT Options
% 6.41/1.52  
% 6.41/1.52  --sat_mode                              false
% 6.41/1.52  --sat_fm_restart_options                ""
% 6.41/1.52  --sat_gr_def                            false
% 6.41/1.52  --sat_epr_types                         true
% 6.41/1.52  --sat_non_cyclic_types                  false
% 6.41/1.52  --sat_finite_models                     false
% 6.41/1.52  --sat_fm_lemmas                         false
% 6.41/1.52  --sat_fm_prep                           false
% 6.41/1.52  --sat_fm_uc_incr                        true
% 6.41/1.52  --sat_out_model                         small
% 6.41/1.52  --sat_out_clauses                       false
% 6.41/1.52  
% 6.41/1.52  ------ QBF Options
% 6.41/1.52  
% 6.41/1.52  --qbf_mode                              false
% 6.41/1.52  --qbf_elim_univ                         false
% 6.41/1.52  --qbf_dom_inst                          none
% 6.41/1.52  --qbf_dom_pre_inst                      false
% 6.41/1.52  --qbf_sk_in                             false
% 6.41/1.52  --qbf_pred_elim                         true
% 6.41/1.52  --qbf_split                             512
% 6.41/1.52  
% 6.41/1.52  ------ BMC1 Options
% 6.41/1.52  
% 6.41/1.52  --bmc1_incremental                      false
% 6.41/1.52  --bmc1_axioms                           reachable_all
% 6.41/1.52  --bmc1_min_bound                        0
% 6.41/1.52  --bmc1_max_bound                        -1
% 6.41/1.52  --bmc1_max_bound_default                -1
% 6.41/1.52  --bmc1_symbol_reachability              true
% 6.41/1.52  --bmc1_property_lemmas                  false
% 6.41/1.52  --bmc1_k_induction                      false
% 6.41/1.52  --bmc1_non_equiv_states                 false
% 6.41/1.52  --bmc1_deadlock                         false
% 6.41/1.52  --bmc1_ucm                              false
% 6.41/1.52  --bmc1_add_unsat_core                   none
% 6.41/1.52  --bmc1_unsat_core_children              false
% 6.41/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 6.41/1.52  --bmc1_out_stat                         full
% 6.41/1.52  --bmc1_ground_init                      false
% 6.41/1.52  --bmc1_pre_inst_next_state              false
% 6.41/1.52  --bmc1_pre_inst_state                   false
% 6.41/1.52  --bmc1_pre_inst_reach_state             false
% 6.41/1.52  --bmc1_out_unsat_core                   false
% 6.41/1.52  --bmc1_aig_witness_out                  false
% 6.41/1.52  --bmc1_verbose                          false
% 6.41/1.52  --bmc1_dump_clauses_tptp                false
% 6.41/1.52  --bmc1_dump_unsat_core_tptp             false
% 6.41/1.52  --bmc1_dump_file                        -
% 6.41/1.52  --bmc1_ucm_expand_uc_limit              128
% 6.41/1.52  --bmc1_ucm_n_expand_iterations          6
% 6.41/1.52  --bmc1_ucm_extend_mode                  1
% 6.41/1.52  --bmc1_ucm_init_mode                    2
% 6.41/1.52  --bmc1_ucm_cone_mode                    none
% 6.41/1.52  --bmc1_ucm_reduced_relation_type        0
% 6.41/1.52  --bmc1_ucm_relax_model                  4
% 6.41/1.52  --bmc1_ucm_full_tr_after_sat            true
% 6.41/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 6.41/1.52  --bmc1_ucm_layered_model                none
% 6.41/1.52  --bmc1_ucm_max_lemma_size               10
% 6.41/1.52  
% 6.41/1.52  ------ AIG Options
% 6.41/1.52  
% 6.41/1.52  --aig_mode                              false
% 6.41/1.52  
% 6.41/1.52  ------ Instantiation Options
% 6.41/1.52  
% 6.41/1.52  --instantiation_flag                    true
% 6.41/1.52  --inst_sos_flag                         false
% 6.41/1.52  --inst_sos_phase                        true
% 6.41/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.41/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.41/1.52  --inst_lit_sel_side                     none
% 6.41/1.52  --inst_solver_per_active                1400
% 6.41/1.52  --inst_solver_calls_frac                1.
% 6.41/1.52  --inst_passive_queue_type               priority_queues
% 6.41/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.41/1.52  --inst_passive_queues_freq              [25;2]
% 6.41/1.52  --inst_dismatching                      true
% 6.41/1.52  --inst_eager_unprocessed_to_passive     true
% 6.41/1.52  --inst_prop_sim_given                   true
% 6.41/1.52  --inst_prop_sim_new                     false
% 6.41/1.52  --inst_subs_new                         false
% 6.41/1.52  --inst_eq_res_simp                      false
% 6.41/1.52  --inst_subs_given                       false
% 6.41/1.52  --inst_orphan_elimination               true
% 6.41/1.52  --inst_learning_loop_flag               true
% 6.41/1.52  --inst_learning_start                   3000
% 6.41/1.52  --inst_learning_factor                  2
% 6.41/1.52  --inst_start_prop_sim_after_learn       3
% 6.41/1.52  --inst_sel_renew                        solver
% 6.41/1.52  --inst_lit_activity_flag                true
% 6.41/1.52  --inst_restr_to_given                   false
% 6.41/1.52  --inst_activity_threshold               500
% 6.41/1.52  --inst_out_proof                        true
% 6.41/1.52  
% 6.41/1.52  ------ Resolution Options
% 6.41/1.52  
% 6.41/1.52  --resolution_flag                       false
% 6.41/1.52  --res_lit_sel                           adaptive
% 6.41/1.52  --res_lit_sel_side                      none
% 6.41/1.52  --res_ordering                          kbo
% 6.41/1.52  --res_to_prop_solver                    active
% 6.41/1.52  --res_prop_simpl_new                    false
% 6.41/1.52  --res_prop_simpl_given                  true
% 6.41/1.52  --res_passive_queue_type                priority_queues
% 6.41/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.41/1.52  --res_passive_queues_freq               [15;5]
% 6.41/1.52  --res_forward_subs                      full
% 6.41/1.52  --res_backward_subs                     full
% 6.41/1.52  --res_forward_subs_resolution           true
% 6.41/1.52  --res_backward_subs_resolution          true
% 6.41/1.52  --res_orphan_elimination                true
% 6.41/1.52  --res_time_limit                        2.
% 6.41/1.52  --res_out_proof                         true
% 6.41/1.52  
% 6.41/1.52  ------ Superposition Options
% 6.41/1.52  
% 6.41/1.52  --superposition_flag                    true
% 6.41/1.52  --sup_passive_queue_type                priority_queues
% 6.41/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.41/1.52  --sup_passive_queues_freq               [8;1;4]
% 6.41/1.52  --demod_completeness_check              fast
% 6.41/1.52  --demod_use_ground                      true
% 6.41/1.52  --sup_to_prop_solver                    passive
% 6.41/1.52  --sup_prop_simpl_new                    true
% 6.41/1.52  --sup_prop_simpl_given                  true
% 6.41/1.52  --sup_fun_splitting                     false
% 6.41/1.52  --sup_smt_interval                      50000
% 6.41/1.52  
% 6.41/1.52  ------ Superposition Simplification Setup
% 6.41/1.52  
% 6.41/1.52  --sup_indices_passive                   []
% 6.41/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 6.41/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.52  --sup_full_bw                           [BwDemod]
% 6.41/1.52  --sup_immed_triv                        [TrivRules]
% 6.41/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.41/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.52  --sup_immed_bw_main                     []
% 6.41/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 6.41/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.52  
% 6.41/1.52  ------ Combination Options
% 6.41/1.52  
% 6.41/1.52  --comb_res_mult                         3
% 6.41/1.52  --comb_sup_mult                         2
% 6.41/1.52  --comb_inst_mult                        10
% 6.41/1.52  
% 6.41/1.52  ------ Debug Options
% 6.41/1.52  
% 6.41/1.52  --dbg_backtrace                         false
% 6.41/1.52  --dbg_dump_prop_clauses                 false
% 6.41/1.52  --dbg_dump_prop_clauses_file            -
% 6.41/1.52  --dbg_out_stat                          false
% 6.41/1.52  
% 6.41/1.52  
% 6.41/1.52  
% 6.41/1.52  
% 6.41/1.52  ------ Proving...
% 6.41/1.52  
% 6.41/1.52  
% 6.41/1.52  % SZS status Theorem for theBenchmark.p
% 6.41/1.52  
% 6.41/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 6.41/1.52  
% 6.41/1.52  fof(f23,conjecture,(
% 6.41/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f24,negated_conjecture,(
% 6.41/1.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 6.41/1.52    inference(negated_conjecture,[],[f23])).
% 6.41/1.52  
% 6.41/1.52  fof(f58,plain,(
% 6.41/1.52    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 6.41/1.52    inference(ennf_transformation,[],[f24])).
% 6.41/1.52  
% 6.41/1.52  fof(f59,plain,(
% 6.41/1.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 6.41/1.52    inference(flattening,[],[f58])).
% 6.41/1.52  
% 6.41/1.52  fof(f67,plain,(
% 6.41/1.52    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 6.41/1.52    introduced(choice_axiom,[])).
% 6.41/1.52  
% 6.41/1.52  fof(f66,plain,(
% 6.41/1.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 6.41/1.52    introduced(choice_axiom,[])).
% 6.41/1.52  
% 6.41/1.52  fof(f68,plain,(
% 6.41/1.52    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 6.41/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f59,f67,f66])).
% 6.41/1.52  
% 6.41/1.52  fof(f113,plain,(
% 6.41/1.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 6.41/1.52    inference(cnf_transformation,[],[f68])).
% 6.41/1.52  
% 6.41/1.52  fof(f116,plain,(
% 6.41/1.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 6.41/1.52    inference(cnf_transformation,[],[f68])).
% 6.41/1.52  
% 6.41/1.52  fof(f17,axiom,(
% 6.41/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f48,plain,(
% 6.41/1.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.41/1.52    inference(ennf_transformation,[],[f17])).
% 6.41/1.52  
% 6.41/1.52  fof(f49,plain,(
% 6.41/1.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.41/1.52    inference(flattening,[],[f48])).
% 6.41/1.52  
% 6.41/1.52  fof(f99,plain,(
% 6.41/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f49])).
% 6.41/1.52  
% 6.41/1.52  fof(f114,plain,(
% 6.41/1.52    v1_funct_1(sK3)),
% 6.41/1.52    inference(cnf_transformation,[],[f68])).
% 6.41/1.52  
% 6.41/1.52  fof(f111,plain,(
% 6.41/1.52    v1_funct_1(sK2)),
% 6.41/1.52    inference(cnf_transformation,[],[f68])).
% 6.41/1.52  
% 6.41/1.52  fof(f2,axiom,(
% 6.41/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f62,plain,(
% 6.41/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.41/1.52    inference(nnf_transformation,[],[f2])).
% 6.41/1.52  
% 6.41/1.52  fof(f73,plain,(
% 6.41/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f62])).
% 6.41/1.52  
% 6.41/1.52  fof(f13,axiom,(
% 6.41/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f42,plain,(
% 6.41/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.41/1.52    inference(ennf_transformation,[],[f13])).
% 6.41/1.52  
% 6.41/1.52  fof(f43,plain,(
% 6.41/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.52    inference(flattening,[],[f42])).
% 6.41/1.52  
% 6.41/1.52  fof(f64,plain,(
% 6.41/1.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.52    inference(nnf_transformation,[],[f43])).
% 6.41/1.52  
% 6.41/1.52  fof(f88,plain,(
% 6.41/1.52    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.41/1.52    inference(cnf_transformation,[],[f64])).
% 6.41/1.52  
% 6.41/1.52  fof(f118,plain,(
% 6.41/1.52    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 6.41/1.52    inference(cnf_transformation,[],[f68])).
% 6.41/1.52  
% 6.41/1.52  fof(f16,axiom,(
% 6.41/1.52    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f25,plain,(
% 6.41/1.52    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 6.41/1.52    inference(pure_predicate_removal,[],[f16])).
% 6.41/1.52  
% 6.41/1.52  fof(f98,plain,(
% 6.41/1.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.41/1.52    inference(cnf_transformation,[],[f25])).
% 6.41/1.52  
% 6.41/1.52  fof(f15,axiom,(
% 6.41/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f46,plain,(
% 6.41/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.41/1.52    inference(ennf_transformation,[],[f15])).
% 6.41/1.52  
% 6.41/1.52  fof(f47,plain,(
% 6.41/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.41/1.52    inference(flattening,[],[f46])).
% 6.41/1.52  
% 6.41/1.52  fof(f97,plain,(
% 6.41/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f47])).
% 6.41/1.52  
% 6.41/1.52  fof(f7,axiom,(
% 6.41/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f34,plain,(
% 6.41/1.52    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.41/1.52    inference(ennf_transformation,[],[f7])).
% 6.41/1.52  
% 6.41/1.52  fof(f35,plain,(
% 6.41/1.52    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.41/1.52    inference(flattening,[],[f34])).
% 6.41/1.52  
% 6.41/1.52  fof(f82,plain,(
% 6.41/1.52    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f35])).
% 6.41/1.52  
% 6.41/1.52  fof(f18,axiom,(
% 6.41/1.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f100,plain,(
% 6.41/1.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f18])).
% 6.41/1.52  
% 6.41/1.52  fof(f123,plain,(
% 6.41/1.52    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.41/1.52    inference(definition_unfolding,[],[f82,f100])).
% 6.41/1.52  
% 6.41/1.52  fof(f12,axiom,(
% 6.41/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f41,plain,(
% 6.41/1.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.52    inference(ennf_transformation,[],[f12])).
% 6.41/1.52  
% 6.41/1.52  fof(f87,plain,(
% 6.41/1.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.41/1.52    inference(cnf_transformation,[],[f41])).
% 6.41/1.52  
% 6.41/1.52  fof(f117,plain,(
% 6.41/1.52    k2_relset_1(sK0,sK1,sK2) = sK1),
% 6.41/1.52    inference(cnf_transformation,[],[f68])).
% 6.41/1.52  
% 6.41/1.52  fof(f19,axiom,(
% 6.41/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f50,plain,(
% 6.41/1.52    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.41/1.52    inference(ennf_transformation,[],[f19])).
% 6.41/1.52  
% 6.41/1.52  fof(f51,plain,(
% 6.41/1.52    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.41/1.52    inference(flattening,[],[f50])).
% 6.41/1.52  
% 6.41/1.52  fof(f101,plain,(
% 6.41/1.52    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f51])).
% 6.41/1.52  
% 6.41/1.52  fof(f112,plain,(
% 6.41/1.52    v1_funct_2(sK2,sK0,sK1)),
% 6.41/1.52    inference(cnf_transformation,[],[f68])).
% 6.41/1.52  
% 6.41/1.52  fof(f115,plain,(
% 6.41/1.52    v1_funct_2(sK3,sK1,sK0)),
% 6.41/1.52    inference(cnf_transformation,[],[f68])).
% 6.41/1.52  
% 6.41/1.52  fof(f14,axiom,(
% 6.41/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f44,plain,(
% 6.41/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.52    inference(ennf_transformation,[],[f14])).
% 6.41/1.52  
% 6.41/1.52  fof(f45,plain,(
% 6.41/1.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.52    inference(flattening,[],[f44])).
% 6.41/1.52  
% 6.41/1.52  fof(f65,plain,(
% 6.41/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.52    inference(nnf_transformation,[],[f45])).
% 6.41/1.52  
% 6.41/1.52  fof(f90,plain,(
% 6.41/1.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.41/1.52    inference(cnf_transformation,[],[f65])).
% 6.41/1.52  
% 6.41/1.52  fof(f11,axiom,(
% 6.41/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f40,plain,(
% 6.41/1.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.52    inference(ennf_transformation,[],[f11])).
% 6.41/1.52  
% 6.41/1.52  fof(f86,plain,(
% 6.41/1.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.41/1.52    inference(cnf_transformation,[],[f40])).
% 6.41/1.52  
% 6.41/1.52  fof(f120,plain,(
% 6.41/1.52    k1_xboole_0 != sK0),
% 6.41/1.52    inference(cnf_transformation,[],[f68])).
% 6.41/1.52  
% 6.41/1.52  fof(f1,axiom,(
% 6.41/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.53  
% 6.41/1.53  fof(f60,plain,(
% 6.41/1.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.41/1.53    inference(nnf_transformation,[],[f1])).
% 6.41/1.53  
% 6.41/1.53  fof(f61,plain,(
% 6.41/1.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.41/1.53    inference(flattening,[],[f60])).
% 6.41/1.53  
% 6.41/1.53  fof(f69,plain,(
% 6.41/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.41/1.53    inference(cnf_transformation,[],[f61])).
% 6.41/1.53  
% 6.41/1.53  fof(f125,plain,(
% 6.41/1.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.41/1.53    inference(equality_resolution,[],[f69])).
% 6.41/1.53  
% 6.41/1.53  fof(f71,plain,(
% 6.41/1.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.41/1.53    inference(cnf_transformation,[],[f61])).
% 6.41/1.53  
% 6.41/1.53  fof(f119,plain,(
% 6.41/1.53    v2_funct_1(sK2)),
% 6.41/1.53    inference(cnf_transformation,[],[f68])).
% 6.41/1.53  
% 6.41/1.53  fof(f4,axiom,(
% 6.41/1.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 6.41/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.53  
% 6.41/1.53  fof(f28,plain,(
% 6.41/1.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.41/1.53    inference(ennf_transformation,[],[f4])).
% 6.41/1.53  
% 6.41/1.53  fof(f29,plain,(
% 6.41/1.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.41/1.53    inference(flattening,[],[f28])).
% 6.41/1.53  
% 6.41/1.53  fof(f77,plain,(
% 6.41/1.53    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.41/1.53    inference(cnf_transformation,[],[f29])).
% 6.41/1.53  
% 6.41/1.53  fof(f76,plain,(
% 6.41/1.53    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.41/1.53    inference(cnf_transformation,[],[f29])).
% 6.41/1.53  
% 6.41/1.53  fof(f5,axiom,(
% 6.41/1.53    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 6.41/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.53  
% 6.41/1.53  fof(f30,plain,(
% 6.41/1.53    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.41/1.53    inference(ennf_transformation,[],[f5])).
% 6.41/1.53  
% 6.41/1.53  fof(f31,plain,(
% 6.41/1.53    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.41/1.53    inference(flattening,[],[f30])).
% 6.41/1.53  
% 6.41/1.53  fof(f80,plain,(
% 6.41/1.53    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.41/1.53    inference(cnf_transformation,[],[f31])).
% 6.41/1.53  
% 6.41/1.53  fof(f9,axiom,(
% 6.41/1.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.41/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.53  
% 6.41/1.53  fof(f38,plain,(
% 6.41/1.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.53    inference(ennf_transformation,[],[f9])).
% 6.41/1.53  
% 6.41/1.53  fof(f84,plain,(
% 6.41/1.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.41/1.53    inference(cnf_transformation,[],[f38])).
% 6.41/1.53  
% 6.41/1.53  fof(f22,axiom,(
% 6.41/1.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 6.41/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.53  
% 6.41/1.53  fof(f56,plain,(
% 6.41/1.53    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.41/1.53    inference(ennf_transformation,[],[f22])).
% 6.41/1.53  
% 6.41/1.53  fof(f57,plain,(
% 6.41/1.53    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.41/1.53    inference(flattening,[],[f56])).
% 6.41/1.53  
% 6.41/1.53  fof(f109,plain,(
% 6.41/1.53    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.41/1.53    inference(cnf_transformation,[],[f57])).
% 6.41/1.53  
% 6.41/1.53  fof(f121,plain,(
% 6.41/1.53    k1_xboole_0 != sK1),
% 6.41/1.53    inference(cnf_transformation,[],[f68])).
% 6.41/1.53  
% 6.41/1.53  fof(f6,axiom,(
% 6.41/1.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 6.41/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.53  
% 6.41/1.53  fof(f32,plain,(
% 6.41/1.53    ! [X0] : (! [X1] : ((v2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.41/1.53    inference(ennf_transformation,[],[f6])).
% 6.41/1.53  
% 6.41/1.53  fof(f33,plain,(
% 6.41/1.53    ! [X0] : (! [X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.41/1.53    inference(flattening,[],[f32])).
% 6.41/1.53  
% 6.41/1.53  fof(f81,plain,(
% 6.41/1.53    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.41/1.53    inference(cnf_transformation,[],[f33])).
% 6.41/1.53  
% 6.41/1.53  fof(f20,axiom,(
% 6.41/1.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 6.41/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.53  
% 6.41/1.53  fof(f52,plain,(
% 6.41/1.53    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 6.41/1.53    inference(ennf_transformation,[],[f20])).
% 6.41/1.53  
% 6.41/1.53  fof(f53,plain,(
% 6.41/1.53    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 6.41/1.53    inference(flattening,[],[f52])).
% 6.41/1.53  
% 6.41/1.53  fof(f104,plain,(
% 6.41/1.53    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 6.41/1.53    inference(cnf_transformation,[],[f53])).
% 6.41/1.53  
% 6.41/1.53  fof(f8,axiom,(
% 6.41/1.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 6.41/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.53  
% 6.41/1.53  fof(f36,plain,(
% 6.41/1.53    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.41/1.53    inference(ennf_transformation,[],[f8])).
% 6.41/1.53  
% 6.41/1.53  fof(f37,plain,(
% 6.41/1.53    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.41/1.53    inference(flattening,[],[f36])).
% 6.41/1.53  
% 6.41/1.53  fof(f83,plain,(
% 6.41/1.53    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.41/1.53    inference(cnf_transformation,[],[f37])).
% 6.41/1.53  
% 6.41/1.53  fof(f122,plain,(
% 6.41/1.53    k2_funct_1(sK2) != sK3),
% 6.41/1.53    inference(cnf_transformation,[],[f68])).
% 6.41/1.53  
% 6.41/1.53  cnf(c_50,negated_conjecture,
% 6.41/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 6.41/1.53      inference(cnf_transformation,[],[f113]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2133,plain,
% 6.41/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_47,negated_conjecture,
% 6.41/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 6.41/1.53      inference(cnf_transformation,[],[f116]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2136,plain,
% 6.41/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_30,plain,
% 6.41/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 6.41/1.53      | ~ v1_funct_1(X0)
% 6.41/1.53      | ~ v1_funct_1(X3)
% 6.41/1.53      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f99]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2146,plain,
% 6.41/1.53      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 6.41/1.53      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 6.41/1.53      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.41/1.53      | v1_funct_1(X5) != iProver_top
% 6.41/1.53      | v1_funct_1(X4) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_7646,plain,
% 6.41/1.53      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 6.41/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.41/1.53      | v1_funct_1(X2) != iProver_top
% 6.41/1.53      | v1_funct_1(sK3) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_2136,c_2146]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_49,negated_conjecture,
% 6.41/1.53      ( v1_funct_1(sK3) ),
% 6.41/1.53      inference(cnf_transformation,[],[f114]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_56,plain,
% 6.41/1.53      ( v1_funct_1(sK3) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_7877,plain,
% 6.41/1.53      ( v1_funct_1(X2) != iProver_top
% 6.41/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.41/1.53      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 6.41/1.53      inference(global_propositional_subsumption,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_7646,c_56]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_7878,plain,
% 6.41/1.53      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 6.41/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.41/1.53      | v1_funct_1(X2) != iProver_top ),
% 6.41/1.53      inference(renaming,[status(thm)],[c_7877]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_7889,plain,
% 6.41/1.53      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 6.41/1.53      | v1_funct_1(sK2) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_2133,c_7878]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_52,negated_conjecture,
% 6.41/1.53      ( v1_funct_1(sK2) ),
% 6.41/1.53      inference(cnf_transformation,[],[f111]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2858,plain,
% 6.41/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 6.41/1.53      | ~ v1_funct_1(X0)
% 6.41/1.53      | ~ v1_funct_1(sK3)
% 6.41/1.53      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_30]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3568,plain,
% 6.41/1.53      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.41/1.53      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 6.41/1.53      | ~ v1_funct_1(sK3)
% 6.41/1.53      | ~ v1_funct_1(sK2)
% 6.41/1.53      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_2858]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_4016,plain,
% 6.41/1.53      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 6.41/1.53      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.41/1.53      | ~ v1_funct_1(sK3)
% 6.41/1.53      | ~ v1_funct_1(sK2)
% 6.41/1.53      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_3568]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_5675,plain,
% 6.41/1.53      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 6.41/1.53      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.41/1.53      | ~ v1_funct_1(sK3)
% 6.41/1.53      | ~ v1_funct_1(sK2)
% 6.41/1.53      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_4016]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_8153,plain,
% 6.41/1.53      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 6.41/1.53      inference(global_propositional_subsumption,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_7889,c_52,c_50,c_49,c_47,c_5675]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3,plain,
% 6.41/1.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.41/1.53      inference(cnf_transformation,[],[f73]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2166,plain,
% 6.41/1.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 6.41/1.53      | r1_tarski(X0,X1) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_20,plain,
% 6.41/1.53      ( ~ r2_relset_1(X0,X1,X2,X3)
% 6.41/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.41/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.41/1.53      | X3 = X2 ),
% 6.41/1.53      inference(cnf_transformation,[],[f88]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_45,negated_conjecture,
% 6.41/1.53      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 6.41/1.53      inference(cnf_transformation,[],[f118]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_703,plain,
% 6.41/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | X3 = X0
% 6.41/1.53      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 6.41/1.53      | k6_partfun1(sK0) != X3
% 6.41/1.53      | sK0 != X2
% 6.41/1.53      | sK0 != X1 ),
% 6.41/1.53      inference(resolution_lifted,[status(thm)],[c_20,c_45]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_704,plain,
% 6.41/1.53      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.41/1.53      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.41/1.53      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 6.41/1.53      inference(unflattening,[status(thm)],[c_703]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_29,plain,
% 6.41/1.53      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 6.41/1.53      inference(cnf_transformation,[],[f98]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_712,plain,
% 6.41/1.53      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.41/1.53      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 6.41/1.53      inference(forward_subsumption_resolution,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_704,c_29]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2127,plain,
% 6.41/1.53      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 6.41/1.53      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3528,plain,
% 6.41/1.53      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 6.41/1.53      | r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0)) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_2166,c_2127]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_8156,plain,
% 6.41/1.53      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 6.41/1.53      | r1_tarski(k5_relat_1(sK2,sK3),k2_zfmisc_1(sK0,sK0)) != iProver_top ),
% 6.41/1.53      inference(demodulation,[status(thm)],[c_8153,c_3528]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_53,plain,
% 6.41/1.53      ( v1_funct_1(sK2) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_55,plain,
% 6.41/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_58,plain,
% 6.41/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_8157,plain,
% 6.41/1.53      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 6.41/1.53      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 6.41/1.53      inference(demodulation,[status(thm)],[c_8153,c_2127]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_27,plain,
% 6.41/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 6.41/1.53      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.41/1.53      | ~ v1_funct_1(X0)
% 6.41/1.53      | ~ v1_funct_1(X3) ),
% 6.41/1.53      inference(cnf_transformation,[],[f97]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2149,plain,
% 6.41/1.53      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.41/1.53      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 6.41/1.53      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 6.41/1.53      | v1_funct_1(X0) != iProver_top
% 6.41/1.53      | v1_funct_1(X3) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_10090,plain,
% 6.41/1.53      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 6.41/1.53      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 6.41/1.53      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 6.41/1.53      | v1_funct_1(sK3) != iProver_top
% 6.41/1.53      | v1_funct_1(sK2) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_8153,c_2149]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_12011,plain,
% 6.41/1.53      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 6.41/1.53      inference(global_propositional_subsumption,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_8156,c_53,c_55,c_56,c_58,c_8157,c_10090]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_13,plain,
% 6.41/1.53      ( ~ v2_funct_1(X0)
% 6.41/1.53      | ~ v1_funct_1(X0)
% 6.41/1.53      | ~ v1_funct_1(X1)
% 6.41/1.53      | ~ v1_relat_1(X1)
% 6.41/1.53      | ~ v1_relat_1(X0)
% 6.41/1.53      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 6.41/1.53      | k1_relat_1(X0) != k2_relat_1(X1)
% 6.41/1.53      | k2_funct_1(X0) = X1 ),
% 6.41/1.53      inference(cnf_transformation,[],[f123]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2160,plain,
% 6.41/1.53      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 6.41/1.53      | k1_relat_1(X1) != k2_relat_1(X0)
% 6.41/1.53      | k2_funct_1(X1) = X0
% 6.41/1.53      | v2_funct_1(X1) != iProver_top
% 6.41/1.53      | v1_funct_1(X1) != iProver_top
% 6.41/1.53      | v1_funct_1(X0) != iProver_top
% 6.41/1.53      | v1_relat_1(X1) != iProver_top
% 6.41/1.53      | v1_relat_1(X0) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_12023,plain,
% 6.41/1.53      ( k1_relat_1(sK3) != k2_relat_1(sK2)
% 6.41/1.53      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 6.41/1.53      | k2_funct_1(sK3) = sK2
% 6.41/1.53      | v2_funct_1(sK3) != iProver_top
% 6.41/1.53      | v1_funct_1(sK3) != iProver_top
% 6.41/1.53      | v1_funct_1(sK2) != iProver_top
% 6.41/1.53      | v1_relat_1(sK3) != iProver_top
% 6.41/1.53      | v1_relat_1(sK2) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_12011,c_2160]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_18,plain,
% 6.41/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f87]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2156,plain,
% 6.41/1.53      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 6.41/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3820,plain,
% 6.41/1.53      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_2133,c_2156]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_46,negated_conjecture,
% 6.41/1.53      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 6.41/1.53      inference(cnf_transformation,[],[f117]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3822,plain,
% 6.41/1.53      ( k2_relat_1(sK2) = sK1 ),
% 6.41/1.53      inference(light_normalisation,[status(thm)],[c_3820,c_46]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3819,plain,
% 6.41/1.53      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_2136,c_2156]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_31,plain,
% 6.41/1.53      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 6.41/1.53      | ~ v1_funct_2(X3,X1,X0)
% 6.41/1.53      | ~ v1_funct_2(X2,X0,X1)
% 6.41/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 6.41/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.41/1.53      | ~ v1_funct_1(X2)
% 6.41/1.53      | ~ v1_funct_1(X3)
% 6.41/1.53      | k2_relset_1(X1,X0,X3) = X0 ),
% 6.41/1.53      inference(cnf_transformation,[],[f101]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_716,plain,
% 6.41/1.53      ( ~ v1_funct_2(X0,X1,X2)
% 6.41/1.53      | ~ v1_funct_2(X3,X2,X1)
% 6.41/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 6.41/1.53      | ~ v1_funct_1(X3)
% 6.41/1.53      | ~ v1_funct_1(X0)
% 6.41/1.53      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 6.41/1.53      | k2_relset_1(X2,X1,X3) = X1
% 6.41/1.53      | k6_partfun1(X1) != k6_partfun1(sK0)
% 6.41/1.53      | sK0 != X1 ),
% 6.41/1.53      inference(resolution_lifted,[status(thm)],[c_31,c_45]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_717,plain,
% 6.41/1.53      ( ~ v1_funct_2(X0,X1,sK0)
% 6.41/1.53      | ~ v1_funct_2(X2,sK0,X1)
% 6.41/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 6.41/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 6.41/1.53      | ~ v1_funct_1(X2)
% 6.41/1.53      | ~ v1_funct_1(X0)
% 6.41/1.53      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 6.41/1.53      | k2_relset_1(X1,sK0,X0) = sK0
% 6.41/1.53      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 6.41/1.53      inference(unflattening,[status(thm)],[c_716]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_814,plain,
% 6.41/1.53      ( ~ v1_funct_2(X0,X1,sK0)
% 6.41/1.53      | ~ v1_funct_2(X2,sK0,X1)
% 6.41/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 6.41/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 6.41/1.53      | ~ v1_funct_1(X0)
% 6.41/1.53      | ~ v1_funct_1(X2)
% 6.41/1.53      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 6.41/1.53      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 6.41/1.53      inference(equality_resolution_simp,[status(thm)],[c_717]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2126,plain,
% 6.41/1.53      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 6.41/1.53      | k2_relset_1(X0,sK0,X2) = sK0
% 6.41/1.53      | v1_funct_2(X2,X0,sK0) != iProver_top
% 6.41/1.53      | v1_funct_2(X1,sK0,X0) != iProver_top
% 6.41/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 6.41/1.53      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 6.41/1.53      | v1_funct_1(X2) != iProver_top
% 6.41/1.53      | v1_funct_1(X1) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_814]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2824,plain,
% 6.41/1.53      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 6.41/1.53      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 6.41/1.53      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 6.41/1.53      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 6.41/1.53      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 6.41/1.53      | v1_funct_1(sK3) != iProver_top
% 6.41/1.53      | v1_funct_1(sK2) != iProver_top ),
% 6.41/1.53      inference(equality_resolution,[status(thm)],[c_2126]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_51,negated_conjecture,
% 6.41/1.53      ( v1_funct_2(sK2,sK0,sK1) ),
% 6.41/1.53      inference(cnf_transformation,[],[f112]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_54,plain,
% 6.41/1.53      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_48,negated_conjecture,
% 6.41/1.53      ( v1_funct_2(sK3,sK1,sK0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f115]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_57,plain,
% 6.41/1.53      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3175,plain,
% 6.41/1.53      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 6.41/1.53      inference(global_propositional_subsumption,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_2824,c_53,c_54,c_55,c_56,c_57,c_58]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3825,plain,
% 6.41/1.53      ( k2_relat_1(sK3) = sK0 ),
% 6.41/1.53      inference(light_normalisation,[status(thm)],[c_3819,c_3175]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_26,plain,
% 6.41/1.53      ( ~ v1_funct_2(X0,X1,X2)
% 6.41/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | k1_relset_1(X1,X2,X0) = X1
% 6.41/1.53      | k1_xboole_0 = X2 ),
% 6.41/1.53      inference(cnf_transformation,[],[f90]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2150,plain,
% 6.41/1.53      ( k1_relset_1(X0,X1,X2) = X0
% 6.41/1.53      | k1_xboole_0 = X1
% 6.41/1.53      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.41/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_6644,plain,
% 6.41/1.53      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 6.41/1.53      | sK0 = k1_xboole_0
% 6.41/1.53      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_2136,c_2150]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_17,plain,
% 6.41/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f86]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2157,plain,
% 6.41/1.53      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.41/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3938,plain,
% 6.41/1.53      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_2136,c_2157]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_6656,plain,
% 6.41/1.53      ( k1_relat_1(sK3) = sK1
% 6.41/1.53      | sK0 = k1_xboole_0
% 6.41/1.53      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 6.41/1.53      inference(demodulation,[status(thm)],[c_6644,c_3938]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_43,negated_conjecture,
% 6.41/1.53      ( k1_xboole_0 != sK0 ),
% 6.41/1.53      inference(cnf_transformation,[],[f120]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2,plain,
% 6.41/1.53      ( r1_tarski(X0,X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f125]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_172,plain,
% 6.41/1.53      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_2]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_0,plain,
% 6.41/1.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 6.41/1.53      inference(cnf_transformation,[],[f71]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_176,plain,
% 6.41/1.53      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 6.41/1.53      | k1_xboole_0 = k1_xboole_0 ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_0]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1152,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2741,plain,
% 6.41/1.53      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_1152]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2742,plain,
% 6.41/1.53      ( sK0 != k1_xboole_0
% 6.41/1.53      | k1_xboole_0 = sK0
% 6.41/1.53      | k1_xboole_0 != k1_xboole_0 ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_2741]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_6788,plain,
% 6.41/1.53      ( k1_relat_1(sK3) = sK1 ),
% 6.41/1.53      inference(global_propositional_subsumption,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_6656,c_57,c_43,c_172,c_176,c_2742]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_12033,plain,
% 6.41/1.53      ( k6_partfun1(sK0) != k6_partfun1(sK0)
% 6.41/1.53      | k2_funct_1(sK3) = sK2
% 6.41/1.53      | sK1 != sK1
% 6.41/1.53      | v2_funct_1(sK3) != iProver_top
% 6.41/1.53      | v1_funct_1(sK3) != iProver_top
% 6.41/1.53      | v1_funct_1(sK2) != iProver_top
% 6.41/1.53      | v1_relat_1(sK3) != iProver_top
% 6.41/1.53      | v1_relat_1(sK2) != iProver_top ),
% 6.41/1.53      inference(light_normalisation,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_12023,c_3822,c_3825,c_6788]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_12034,plain,
% 6.41/1.53      ( k2_funct_1(sK3) = sK2
% 6.41/1.53      | v2_funct_1(sK3) != iProver_top
% 6.41/1.53      | v1_funct_1(sK3) != iProver_top
% 6.41/1.53      | v1_funct_1(sK2) != iProver_top
% 6.41/1.53      | v1_relat_1(sK3) != iProver_top
% 6.41/1.53      | v1_relat_1(sK2) != iProver_top ),
% 6.41/1.53      inference(equality_resolution_simp,[status(thm)],[c_12033]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_44,negated_conjecture,
% 6.41/1.53      ( v2_funct_1(sK2) ),
% 6.41/1.53      inference(cnf_transformation,[],[f119]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_60,plain,
% 6.41/1.53      ( v2_funct_1(sK2) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_7,plain,
% 6.41/1.53      ( ~ v1_funct_1(X0)
% 6.41/1.53      | v1_funct_1(k2_funct_1(X0))
% 6.41/1.53      | ~ v1_relat_1(X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f77]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2632,plain,
% 6.41/1.53      ( v1_funct_1(k2_funct_1(sK2))
% 6.41/1.53      | ~ v1_funct_1(sK2)
% 6.41/1.53      | ~ v1_relat_1(sK2) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_7]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2633,plain,
% 6.41/1.53      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 6.41/1.53      | v1_funct_1(sK2) != iProver_top
% 6.41/1.53      | v1_relat_1(sK2) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_2632]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_8,plain,
% 6.41/1.53      ( ~ v1_funct_1(X0)
% 6.41/1.53      | ~ v1_relat_1(X0)
% 6.41/1.53      | v1_relat_1(k2_funct_1(X0)) ),
% 6.41/1.53      inference(cnf_transformation,[],[f76]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2638,plain,
% 6.41/1.53      ( ~ v1_funct_1(sK2)
% 6.41/1.53      | v1_relat_1(k2_funct_1(sK2))
% 6.41/1.53      | ~ v1_relat_1(sK2) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_8]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2639,plain,
% 6.41/1.53      ( v1_funct_1(sK2) != iProver_top
% 6.41/1.53      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 6.41/1.53      | v1_relat_1(sK2) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_2638]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_9,plain,
% 6.41/1.53      ( ~ v2_funct_1(X0)
% 6.41/1.53      | v2_funct_1(k2_funct_1(X0))
% 6.41/1.53      | ~ v1_funct_1(X0)
% 6.41/1.53      | ~ v1_relat_1(X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f80]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2652,plain,
% 6.41/1.53      ( v2_funct_1(k2_funct_1(sK2))
% 6.41/1.53      | ~ v2_funct_1(sK2)
% 6.41/1.53      | ~ v1_funct_1(sK2)
% 6.41/1.53      | ~ v1_relat_1(sK2) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_9]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2653,plain,
% 6.41/1.53      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 6.41/1.53      | v2_funct_1(sK2) != iProver_top
% 6.41/1.53      | v1_funct_1(sK2) != iProver_top
% 6.41/1.53      | v1_relat_1(sK2) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_2652]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_15,plain,
% 6.41/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | v1_relat_1(X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f84]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2665,plain,
% 6.41/1.53      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 6.41/1.53      | v1_relat_1(sK3) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_15]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2666,plain,
% 6.41/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 6.41/1.53      | v1_relat_1(sK3) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_2665]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2668,plain,
% 6.41/1.53      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.41/1.53      | v1_relat_1(sK2) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_15]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2669,plain,
% 6.41/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 6.41/1.53      | v1_relat_1(sK2) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_2668]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_40,plain,
% 6.41/1.53      ( ~ v1_funct_2(X0,X1,X2)
% 6.41/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | ~ v2_funct_1(X0)
% 6.41/1.53      | ~ v1_funct_1(X0)
% 6.41/1.53      | k2_relset_1(X1,X2,X0) != X2
% 6.41/1.53      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 6.41/1.53      | k1_xboole_0 = X2 ),
% 6.41/1.53      inference(cnf_transformation,[],[f109]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2138,plain,
% 6.41/1.53      ( k2_relset_1(X0,X1,X2) != X1
% 6.41/1.53      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 6.41/1.53      | k1_xboole_0 = X1
% 6.41/1.53      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.41/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.41/1.53      | v2_funct_1(X2) != iProver_top
% 6.41/1.53      | v1_funct_1(X2) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_6481,plain,
% 6.41/1.53      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 6.41/1.53      | sK1 = k1_xboole_0
% 6.41/1.53      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 6.41/1.53      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 6.41/1.53      | v2_funct_1(sK2) != iProver_top
% 6.41/1.53      | v1_funct_1(sK2) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_46,c_2138]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_42,negated_conjecture,
% 6.41/1.53      ( k1_xboole_0 != sK1 ),
% 6.41/1.53      inference(cnf_transformation,[],[f121]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2878,plain,
% 6.41/1.53      ( ~ v1_funct_2(X0,X1,sK1)
% 6.41/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 6.41/1.53      | ~ v2_funct_1(X0)
% 6.41/1.53      | ~ v1_funct_1(X0)
% 6.41/1.53      | k2_relset_1(X1,sK1,X0) != sK1
% 6.41/1.53      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 6.41/1.53      | k1_xboole_0 = sK1 ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_40]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3543,plain,
% 6.41/1.53      ( ~ v1_funct_2(sK2,X0,sK1)
% 6.41/1.53      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 6.41/1.53      | ~ v2_funct_1(sK2)
% 6.41/1.53      | ~ v1_funct_1(sK2)
% 6.41/1.53      | k2_relset_1(X0,sK1,sK2) != sK1
% 6.41/1.53      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 6.41/1.53      | k1_xboole_0 = sK1 ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_2878]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3954,plain,
% 6.41/1.53      ( ~ v1_funct_2(sK2,sK0,sK1)
% 6.41/1.53      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.41/1.53      | ~ v2_funct_1(sK2)
% 6.41/1.53      | ~ v1_funct_1(sK2)
% 6.41/1.53      | k2_relset_1(sK0,sK1,sK2) != sK1
% 6.41/1.53      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 6.41/1.53      | k1_xboole_0 = sK1 ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_3543]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_6733,plain,
% 6.41/1.53      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 6.41/1.53      inference(global_propositional_subsumption,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_6481,c_52,c_51,c_50,c_46,c_44,c_42,c_3954]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_12,plain,
% 6.41/1.53      ( ~ v2_funct_1(X0)
% 6.41/1.53      | ~ v2_funct_1(X1)
% 6.41/1.53      | v2_funct_1(k5_relat_1(X0,X1))
% 6.41/1.53      | ~ v1_funct_1(X0)
% 6.41/1.53      | ~ v1_funct_1(X1)
% 6.41/1.53      | ~ v1_relat_1(X1)
% 6.41/1.53      | ~ v1_relat_1(X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f81]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2161,plain,
% 6.41/1.53      ( v2_funct_1(X0) != iProver_top
% 6.41/1.53      | v2_funct_1(X1) != iProver_top
% 6.41/1.53      | v2_funct_1(k5_relat_1(X0,X1)) = iProver_top
% 6.41/1.53      | v1_funct_1(X0) != iProver_top
% 6.41/1.53      | v1_funct_1(X1) != iProver_top
% 6.41/1.53      | v1_relat_1(X0) != iProver_top
% 6.41/1.53      | v1_relat_1(X1) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_7584,plain,
% 6.41/1.53      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top
% 6.41/1.53      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 6.41/1.53      | v2_funct_1(sK2) != iProver_top
% 6.41/1.53      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 6.41/1.53      | v1_funct_1(sK2) != iProver_top
% 6.41/1.53      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 6.41/1.53      | v1_relat_1(sK2) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_6733,c_2161]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_33,plain,
% 6.41/1.53      ( ~ v1_funct_2(X0,X1,X2)
% 6.41/1.53      | ~ v1_funct_2(X3,X4,X1)
% 6.41/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 6.41/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | v2_funct_1(X0)
% 6.41/1.53      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 6.41/1.53      | ~ v1_funct_1(X0)
% 6.41/1.53      | ~ v1_funct_1(X3)
% 6.41/1.53      | k2_relset_1(X4,X1,X3) != X1
% 6.41/1.53      | k1_xboole_0 = X2 ),
% 6.41/1.53      inference(cnf_transformation,[],[f104]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2144,plain,
% 6.41/1.53      ( k2_relset_1(X0,X1,X2) != X1
% 6.41/1.53      | k1_xboole_0 = X3
% 6.41/1.53      | v1_funct_2(X4,X1,X3) != iProver_top
% 6.41/1.53      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.41/1.53      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 6.41/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.41/1.53      | v2_funct_1(X4) = iProver_top
% 6.41/1.53      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 6.41/1.53      | v1_funct_1(X4) != iProver_top
% 6.41/1.53      | v1_funct_1(X2) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_11104,plain,
% 6.41/1.53      ( k1_xboole_0 = X0
% 6.41/1.53      | v1_funct_2(X1,sK1,X0) != iProver_top
% 6.41/1.53      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 6.41/1.53      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 6.41/1.53      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 6.41/1.53      | v2_funct_1(X1) = iProver_top
% 6.41/1.53      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 6.41/1.53      | v1_funct_1(X1) != iProver_top
% 6.41/1.53      | v1_funct_1(sK2) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_46,c_2144]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_11194,plain,
% 6.41/1.53      ( v1_funct_1(X1) != iProver_top
% 6.41/1.53      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 6.41/1.53      | v2_funct_1(X1) = iProver_top
% 6.41/1.53      | v1_funct_2(X1,sK1,X0) != iProver_top
% 6.41/1.53      | k1_xboole_0 = X0
% 6.41/1.53      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
% 6.41/1.53      inference(global_propositional_subsumption,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_11104,c_53,c_54,c_55]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_11195,plain,
% 6.41/1.53      ( k1_xboole_0 = X0
% 6.41/1.53      | v1_funct_2(X1,sK1,X0) != iProver_top
% 6.41/1.53      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 6.41/1.53      | v2_funct_1(X1) = iProver_top
% 6.41/1.53      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 6.41/1.53      | v1_funct_1(X1) != iProver_top ),
% 6.41/1.53      inference(renaming,[status(thm)],[c_11194]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_11204,plain,
% 6.41/1.53      ( sK0 = k1_xboole_0
% 6.41/1.53      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 6.41/1.53      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 6.41/1.53      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 6.41/1.53      | v2_funct_1(sK3) = iProver_top
% 6.41/1.53      | v1_funct_1(sK3) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_8153,c_11195]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_11354,plain,
% 6.41/1.53      ( v2_funct_1(sK3) = iProver_top
% 6.41/1.53      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
% 6.41/1.53      inference(global_propositional_subsumption,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_11204,c_56,c_57,c_58,c_43,c_172,c_176,c_2742]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_11355,plain,
% 6.41/1.53      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 6.41/1.53      | v2_funct_1(sK3) = iProver_top ),
% 6.41/1.53      inference(renaming,[status(thm)],[c_11354]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_12014,plain,
% 6.41/1.53      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 6.41/1.53      | v2_funct_1(sK3) = iProver_top ),
% 6.41/1.53      inference(demodulation,[status(thm)],[c_12011,c_11355]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_14298,plain,
% 6.41/1.53      ( k2_funct_1(sK3) = sK2 ),
% 6.41/1.53      inference(global_propositional_subsumption,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_12034,c_53,c_55,c_56,c_58,c_60,c_2633,c_2639,c_2653,
% 6.41/1.53                 c_2666,c_2669,c_7584,c_12014]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_12130,plain,
% 6.41/1.53      ( v2_funct_1(sK3) = iProver_top ),
% 6.41/1.53      inference(global_propositional_subsumption,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_12014,c_53,c_55,c_60,c_2633,c_2639,c_2653,c_2669,
% 6.41/1.53                 c_7584]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_14,plain,
% 6.41/1.53      ( ~ v2_funct_1(X0)
% 6.41/1.53      | ~ v1_funct_1(X0)
% 6.41/1.53      | ~ v1_relat_1(X0)
% 6.41/1.53      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 6.41/1.53      inference(cnf_transformation,[],[f83]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2159,plain,
% 6.41/1.53      ( k2_funct_1(k2_funct_1(X0)) = X0
% 6.41/1.53      | v2_funct_1(X0) != iProver_top
% 6.41/1.53      | v1_funct_1(X0) != iProver_top
% 6.41/1.53      | v1_relat_1(X0) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_12135,plain,
% 6.41/1.53      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 6.41/1.53      | v1_funct_1(sK3) != iProver_top
% 6.41/1.53      | v1_relat_1(sK3) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_12130,c_2159]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_12322,plain,
% 6.41/1.53      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 6.41/1.53      inference(global_propositional_subsumption,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_12135,c_56,c_58,c_2666]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_14301,plain,
% 6.41/1.53      ( k2_funct_1(sK2) = sK3 ),
% 6.41/1.53      inference(demodulation,[status(thm)],[c_14298,c_12322]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_41,negated_conjecture,
% 6.41/1.53      ( k2_funct_1(sK2) != sK3 ),
% 6.41/1.53      inference(cnf_transformation,[],[f122]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(contradiction,plain,
% 6.41/1.53      ( $false ),
% 6.41/1.53      inference(minisat,[status(thm)],[c_14301,c_41]) ).
% 6.41/1.53  
% 6.41/1.53  
% 6.41/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 6.41/1.53  
% 6.41/1.53  ------                               Statistics
% 6.41/1.53  
% 6.41/1.53  ------ General
% 6.41/1.53  
% 6.41/1.53  abstr_ref_over_cycles:                  0
% 6.41/1.53  abstr_ref_under_cycles:                 0
% 6.41/1.53  gc_basic_clause_elim:                   0
% 6.41/1.53  forced_gc_time:                         0
% 6.41/1.53  parsing_time:                           0.01
% 6.41/1.53  unif_index_cands_time:                  0.
% 6.41/1.53  unif_index_add_time:                    0.
% 6.41/1.53  orderings_time:                         0.
% 6.41/1.53  out_proof_time:                         0.017
% 6.41/1.53  total_time:                             0.566
% 6.41/1.53  num_of_symbols:                         54
% 6.41/1.53  num_of_terms:                           14278
% 6.41/1.53  
% 6.41/1.53  ------ Preprocessing
% 6.41/1.53  
% 6.41/1.53  num_of_splits:                          0
% 6.41/1.53  num_of_split_atoms:                     0
% 6.41/1.53  num_of_reused_defs:                     0
% 6.41/1.53  num_eq_ax_congr_red:                    17
% 6.41/1.53  num_of_sem_filtered_clauses:            1
% 6.41/1.53  num_of_subtypes:                        0
% 6.41/1.53  monotx_restored_types:                  0
% 6.41/1.53  sat_num_of_epr_types:                   0
% 6.41/1.53  sat_num_of_non_cyclic_types:            0
% 6.41/1.53  sat_guarded_non_collapsed_types:        0
% 6.41/1.53  num_pure_diseq_elim:                    0
% 6.41/1.53  simp_replaced_by:                       0
% 6.41/1.53  res_preprocessed:                       224
% 6.41/1.53  prep_upred:                             0
% 6.41/1.53  prep_unflattend:                        12
% 6.41/1.53  smt_new_axioms:                         0
% 6.41/1.53  pred_elim_cands:                        6
% 6.41/1.53  pred_elim:                              2
% 6.41/1.53  pred_elim_cl:                           3
% 6.41/1.53  pred_elim_cycles:                       4
% 6.41/1.53  merged_defs:                            8
% 6.41/1.53  merged_defs_ncl:                        0
% 6.41/1.53  bin_hyper_res:                          8
% 6.41/1.53  prep_cycles:                            4
% 6.41/1.53  pred_elim_time:                         0.003
% 6.41/1.53  splitting_time:                         0.
% 6.41/1.53  sem_filter_time:                        0.
% 6.41/1.53  monotx_time:                            0.011
% 6.41/1.53  subtype_inf_time:                       0.
% 6.41/1.53  
% 6.41/1.53  ------ Problem properties
% 6.41/1.53  
% 6.41/1.53  clauses:                                47
% 6.41/1.53  conjectures:                            11
% 6.41/1.53  epr:                                    9
% 6.41/1.53  horn:                                   39
% 6.41/1.53  ground:                                 12
% 6.41/1.53  unary:                                  13
% 6.41/1.53  binary:                                 7
% 6.41/1.53  lits:                                   178
% 6.41/1.53  lits_eq:                                40
% 6.41/1.53  fd_pure:                                0
% 6.41/1.53  fd_pseudo:                              0
% 6.41/1.53  fd_cond:                                7
% 6.41/1.53  fd_pseudo_cond:                         2
% 6.41/1.53  ac_symbols:                             0
% 6.41/1.53  
% 6.41/1.53  ------ Propositional Solver
% 6.41/1.53  
% 6.41/1.53  prop_solver_calls:                      27
% 6.41/1.53  prop_fast_solver_calls:                 2191
% 6.41/1.53  smt_solver_calls:                       0
% 6.41/1.53  smt_fast_solver_calls:                  0
% 6.41/1.53  prop_num_of_clauses:                    5280
% 6.41/1.53  prop_preprocess_simplified:             14399
% 6.41/1.53  prop_fo_subsumed:                       115
% 6.41/1.53  prop_solver_time:                       0.
% 6.41/1.53  smt_solver_time:                        0.
% 6.41/1.53  smt_fast_solver_time:                   0.
% 6.41/1.53  prop_fast_solver_time:                  0.
% 6.41/1.53  prop_unsat_core_time:                   0.
% 6.41/1.53  
% 6.41/1.53  ------ QBF
% 6.41/1.53  
% 6.41/1.53  qbf_q_res:                              0
% 6.41/1.53  qbf_num_tautologies:                    0
% 6.41/1.53  qbf_prep_cycles:                        0
% 6.41/1.53  
% 6.41/1.53  ------ BMC1
% 6.41/1.53  
% 6.41/1.53  bmc1_current_bound:                     -1
% 6.41/1.53  bmc1_last_solved_bound:                 -1
% 6.41/1.53  bmc1_unsat_core_size:                   -1
% 6.41/1.53  bmc1_unsat_core_parents_size:           -1
% 6.41/1.53  bmc1_merge_next_fun:                    0
% 6.41/1.53  bmc1_unsat_core_clauses_time:           0.
% 6.41/1.53  
% 6.41/1.53  ------ Instantiation
% 6.41/1.53  
% 6.41/1.53  inst_num_of_clauses:                    1363
% 6.41/1.53  inst_num_in_passive:                    323
% 6.41/1.53  inst_num_in_active:                     736
% 6.41/1.53  inst_num_in_unprocessed:                304
% 6.41/1.53  inst_num_of_loops:                      800
% 6.41/1.53  inst_num_of_learning_restarts:          0
% 6.41/1.53  inst_num_moves_active_passive:          64
% 6.41/1.53  inst_lit_activity:                      0
% 6.41/1.53  inst_lit_activity_moves:                1
% 6.41/1.53  inst_num_tautologies:                   0
% 6.41/1.53  inst_num_prop_implied:                  0
% 6.41/1.53  inst_num_existing_simplified:           0
% 6.41/1.53  inst_num_eq_res_simplified:             0
% 6.41/1.53  inst_num_child_elim:                    0
% 6.41/1.53  inst_num_of_dismatching_blockings:      443
% 6.41/1.53  inst_num_of_non_proper_insts:           1395
% 6.41/1.53  inst_num_of_duplicates:                 0
% 6.41/1.53  inst_inst_num_from_inst_to_res:         0
% 6.41/1.53  inst_dismatching_checking_time:         0.
% 6.41/1.53  
% 6.41/1.53  ------ Resolution
% 6.41/1.53  
% 6.41/1.53  res_num_of_clauses:                     0
% 6.41/1.53  res_num_in_passive:                     0
% 6.41/1.53  res_num_in_active:                      0
% 6.41/1.53  res_num_of_loops:                       228
% 6.41/1.53  res_forward_subset_subsumed:            94
% 6.41/1.53  res_backward_subset_subsumed:           0
% 6.41/1.53  res_forward_subsumed:                   0
% 6.41/1.53  res_backward_subsumed:                  0
% 6.41/1.53  res_forward_subsumption_resolution:     2
% 6.41/1.53  res_backward_subsumption_resolution:    0
% 6.41/1.53  res_clause_to_clause_subsumption:       537
% 6.41/1.53  res_orphan_elimination:                 0
% 6.41/1.53  res_tautology_del:                      45
% 6.41/1.53  res_num_eq_res_simplified:              1
% 6.41/1.53  res_num_sel_changes:                    0
% 6.41/1.53  res_moves_from_active_to_pass:          0
% 6.41/1.53  
% 6.41/1.53  ------ Superposition
% 6.41/1.53  
% 6.41/1.53  sup_time_total:                         0.
% 6.41/1.53  sup_time_generating:                    0.
% 6.41/1.53  sup_time_sim_full:                      0.
% 6.41/1.53  sup_time_sim_immed:                     0.
% 6.41/1.53  
% 6.41/1.53  sup_num_of_clauses:                     302
% 6.41/1.53  sup_num_in_active:                      147
% 6.41/1.53  sup_num_in_passive:                     155
% 6.41/1.53  sup_num_of_loops:                       159
% 6.41/1.53  sup_fw_superposition:                   169
% 6.41/1.53  sup_bw_superposition:                   191
% 6.41/1.53  sup_immediate_simplified:               63
% 6.41/1.53  sup_given_eliminated:                   0
% 6.41/1.53  comparisons_done:                       0
% 6.41/1.53  comparisons_avoided:                    0
% 6.41/1.53  
% 6.41/1.53  ------ Simplifications
% 6.41/1.53  
% 6.41/1.53  
% 6.41/1.53  sim_fw_subset_subsumed:                 25
% 6.41/1.53  sim_bw_subset_subsumed:                 3
% 6.41/1.53  sim_fw_subsumed:                        13
% 6.41/1.53  sim_bw_subsumed:                        0
% 6.41/1.53  sim_fw_subsumption_res:                 0
% 6.41/1.53  sim_bw_subsumption_res:                 0
% 6.41/1.53  sim_tautology_del:                      1
% 6.41/1.53  sim_eq_tautology_del:                   13
% 6.41/1.53  sim_eq_res_simp:                        1
% 6.41/1.53  sim_fw_demodulated:                     10
% 6.41/1.53  sim_bw_demodulated:                     11
% 6.41/1.53  sim_light_normalised:                   22
% 6.41/1.53  sim_joinable_taut:                      0
% 6.41/1.53  sim_joinable_simp:                      0
% 6.41/1.53  sim_ac_normalised:                      0
% 6.41/1.53  sim_smt_subsumption:                    0
% 6.41/1.53  
%------------------------------------------------------------------------------
