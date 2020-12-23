%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:11 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  212 (2553 expanded)
%              Number of clauses        :  125 ( 725 expanded)
%              Number of leaves         :   23 ( 658 expanded)
%              Depth                    :   23
%              Number of atoms          :  869 (20963 expanded)
%              Number of equality atoms :  432 (7544 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

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

fof(f60,plain,(
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
     => ( k2_funct_1(X2) != sK4
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
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
          ( k2_funct_1(sK3) != X3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & v2_funct_1(sK3)
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & k2_relset_1(sK1,sK2,sK3) = sK2
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( k2_funct_1(sK3) != sK4
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & v2_funct_1(sK3)
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f55,f60,f59])).

fof(f104,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f99,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f61])).

fof(f100,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f102,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f61])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f61])).

fof(f21,axiom,(
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

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f21])).

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
    inference(flattening,[],[f50])).

fof(f93,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f101,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f106,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f61])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f111,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f71,f89])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f74,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f80,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f77,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f20,axiom,(
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

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f20])).

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
    inference(flattening,[],[f48])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f76,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f110,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f66,f89])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f79,f89])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f108,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_38,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_38])).

cnf(c_483,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_25,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_491,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_483,c_25])).

cnf(c_1403,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1691,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2329,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1403,c_45,c_43,c_42,c_40,c_491,c_1691])).

cnf(c_39,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f93])).

cnf(c_1416,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1438,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1437,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2512,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1438,c_1437])).

cnf(c_6841,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | o_0_0_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1416,c_2512])).

cnf(c_6843,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_6841])).

cnf(c_46,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_47,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_48,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_6856,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | o_0_0_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6843,c_46,c_47,c_48])).

cnf(c_6857,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6856])).

cnf(c_6862,plain,
    ( sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2329,c_6857])).

cnf(c_49,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_50,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_51,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1519,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_800,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1580,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_1880,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | sK1 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_8,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2896,plain,
    ( v2_funct_1(k6_partfun1(sK1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2897,plain,
    ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2896])).

cnf(c_6965,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6862,c_49,c_50,c_51,c_36,c_0,c_1519,c_1880,c_2897])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1430,plain,
    ( v2_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1424,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3604,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(X0))) = k2_funct_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1430,c_1424])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_113,plain,
    ( v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_116,plain,
    ( v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8760,plain,
    ( v1_funct_1(X0) != iProver_top
    | k2_funct_1(k2_funct_1(k2_funct_1(X0))) = k2_funct_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3604,c_113,c_116])).

cnf(c_8761,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(X0))) = k2_funct_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8760])).

cnf(c_8767,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_funct_1(k2_funct_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1430,c_8761])).

cnf(c_12371,plain,
    ( v1_funct_1(X0) != iProver_top
    | k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_funct_1(k2_funct_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8767,c_113,c_116])).

cnf(c_12372,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_funct_1(k2_funct_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12371])).

cnf(c_12380,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK4)))) = k2_funct_1(k2_funct_1(sK4))
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6965,c_12372])).

cnf(c_6973,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6965,c_1424])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1564,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1852,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_1853,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1852])).

cnf(c_3977,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k2_funct_1(k2_funct_1(sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3978,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3977])).

cnf(c_7247,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6973,c_49,c_50,c_51,c_36,c_0,c_1519,c_1853,c_1880,c_2897,c_3978,c_6862])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1426,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4844,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1430,c_1426])).

cnf(c_11519,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4844,c_113,c_116])).

cnf(c_11520,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11519])).

cnf(c_11528,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(sK4)),k2_funct_1(sK4))) = k2_relat_1(k2_funct_1(sK4))
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6965,c_11520])).

cnf(c_27,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_495,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_496,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_587,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_496])).

cnf(c_1402,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_1901,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1402])).

cnf(c_2336,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1901,c_46,c_47,c_48,c_49,c_50,c_51])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1412,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2822,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | o_0_0_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1412,c_2512])).

cnf(c_2827,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2336,c_2822])).

cnf(c_3468,plain,
    ( v2_funct_1(sK4) != iProver_top
    | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2827,c_49,c_50,c_51,c_36,c_0,c_1519,c_1880])).

cnf(c_3469,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | v2_funct_1(sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_3468])).

cnf(c_6975,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
    inference(superposition,[status(thm)],[c_6965,c_3469])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1429,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6971,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6965,c_1429])).

cnf(c_7253,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6971,c_49,c_51,c_1853])).

cnf(c_11529,plain,
    ( k1_relat_1(k6_partfun1(sK2)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11528,c_6975,c_7247,c_7253])).

cnf(c_5,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_11530,plain,
    ( k1_relat_1(sK4) = sK2
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11529,c_5])).

cnf(c_11542,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11530,c_49,c_51,c_1853])).

cnf(c_1407,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_1410,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1418,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5017,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1410,c_1418])).

cnf(c_5216,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5017,c_49])).

cnf(c_5217,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5216])).

cnf(c_5225,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_5217])).

cnf(c_5226,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5225,c_2329])).

cnf(c_5340,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5226,c_46])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1425,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5342,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(sK4)) != k6_partfun1(sK1)
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5340,c_1425])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1422,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2879,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1407,c_1422])).

cnf(c_2880,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2879,c_39])).

cnf(c_2878,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1410,c_1422])).

cnf(c_2881,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2878,c_2336])).

cnf(c_5343,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5342,c_2880,c_2881])).

cnf(c_5344,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5343])).

cnf(c_2220,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2221,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2220])).

cnf(c_8624,plain,
    ( k1_relat_1(sK4) != sK2
    | k2_funct_1(sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5344,c_46,c_48,c_49,c_50,c_51,c_36,c_0,c_1519,c_1853,c_1880,c_2221,c_2897,c_6862])).

cnf(c_8625,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2 ),
    inference(renaming,[status(thm)],[c_8624])).

cnf(c_11544,plain,
    ( k2_funct_1(sK4) = sK3
    | sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_11542,c_8625])).

cnf(c_11546,plain,
    ( k2_funct_1(sK4) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_11544])).

cnf(c_12381,plain,
    ( k2_funct_1(sK3) = sK4
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12380,c_7247,c_11546])).

cnf(c_34,negated_conjecture,
    ( k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f108])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12381,c_1853,c_34,c_51,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.72/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/0.99  
% 3.72/0.99  ------  iProver source info
% 3.72/0.99  
% 3.72/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.72/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/0.99  git: non_committed_changes: false
% 3.72/0.99  git: last_make_outside_of_git: false
% 3.72/0.99  
% 3.72/0.99  ------ 
% 3.72/0.99  
% 3.72/0.99  ------ Input Options
% 3.72/0.99  
% 3.72/0.99  --out_options                           all
% 3.72/0.99  --tptp_safe_out                         true
% 3.72/0.99  --problem_path                          ""
% 3.72/0.99  --include_path                          ""
% 3.72/0.99  --clausifier                            res/vclausify_rel
% 3.72/0.99  --clausifier_options                    ""
% 3.72/0.99  --stdin                                 false
% 3.72/0.99  --stats_out                             all
% 3.72/0.99  
% 3.72/0.99  ------ General Options
% 3.72/0.99  
% 3.72/0.99  --fof                                   false
% 3.72/0.99  --time_out_real                         305.
% 3.72/0.99  --time_out_virtual                      -1.
% 3.72/0.99  --symbol_type_check                     false
% 3.72/0.99  --clausify_out                          false
% 3.72/0.99  --sig_cnt_out                           false
% 3.72/0.99  --trig_cnt_out                          false
% 3.72/0.99  --trig_cnt_out_tolerance                1.
% 3.72/0.99  --trig_cnt_out_sk_spl                   false
% 3.72/0.99  --abstr_cl_out                          false
% 3.72/0.99  
% 3.72/0.99  ------ Global Options
% 3.72/0.99  
% 3.72/0.99  --schedule                              default
% 3.72/0.99  --add_important_lit                     false
% 3.72/0.99  --prop_solver_per_cl                    1000
% 3.72/0.99  --min_unsat_core                        false
% 3.72/0.99  --soft_assumptions                      false
% 3.72/0.99  --soft_lemma_size                       3
% 3.72/0.99  --prop_impl_unit_size                   0
% 3.72/0.99  --prop_impl_unit                        []
% 3.72/0.99  --share_sel_clauses                     true
% 3.72/0.99  --reset_solvers                         false
% 3.72/0.99  --bc_imp_inh                            [conj_cone]
% 3.72/0.99  --conj_cone_tolerance                   3.
% 3.72/0.99  --extra_neg_conj                        none
% 3.72/0.99  --large_theory_mode                     true
% 3.72/0.99  --prolific_symb_bound                   200
% 3.72/0.99  --lt_threshold                          2000
% 3.72/0.99  --clause_weak_htbl                      true
% 3.72/0.99  --gc_record_bc_elim                     false
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing Options
% 3.72/0.99  
% 3.72/0.99  --preprocessing_flag                    true
% 3.72/0.99  --time_out_prep_mult                    0.1
% 3.72/0.99  --splitting_mode                        input
% 3.72/0.99  --splitting_grd                         true
% 3.72/0.99  --splitting_cvd                         false
% 3.72/0.99  --splitting_cvd_svl                     false
% 3.72/0.99  --splitting_nvd                         32
% 3.72/0.99  --sub_typing                            true
% 3.72/0.99  --prep_gs_sim                           true
% 3.72/0.99  --prep_unflatten                        true
% 3.72/0.99  --prep_res_sim                          true
% 3.72/0.99  --prep_upred                            true
% 3.72/0.99  --prep_sem_filter                       exhaustive
% 3.72/0.99  --prep_sem_filter_out                   false
% 3.72/0.99  --pred_elim                             true
% 3.72/0.99  --res_sim_input                         true
% 3.72/0.99  --eq_ax_congr_red                       true
% 3.72/0.99  --pure_diseq_elim                       true
% 3.72/0.99  --brand_transform                       false
% 3.72/0.99  --non_eq_to_eq                          false
% 3.72/0.99  --prep_def_merge                        true
% 3.72/0.99  --prep_def_merge_prop_impl              false
% 3.72/0.99  --prep_def_merge_mbd                    true
% 3.72/0.99  --prep_def_merge_tr_red                 false
% 3.72/0.99  --prep_def_merge_tr_cl                  false
% 3.72/0.99  --smt_preprocessing                     true
% 3.72/0.99  --smt_ac_axioms                         fast
% 3.72/0.99  --preprocessed_out                      false
% 3.72/0.99  --preprocessed_stats                    false
% 3.72/0.99  
% 3.72/0.99  ------ Abstraction refinement Options
% 3.72/0.99  
% 3.72/0.99  --abstr_ref                             []
% 3.72/0.99  --abstr_ref_prep                        false
% 3.72/0.99  --abstr_ref_until_sat                   false
% 3.72/0.99  --abstr_ref_sig_restrict                funpre
% 3.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/0.99  --abstr_ref_under                       []
% 3.72/0.99  
% 3.72/0.99  ------ SAT Options
% 3.72/0.99  
% 3.72/0.99  --sat_mode                              false
% 3.72/0.99  --sat_fm_restart_options                ""
% 3.72/0.99  --sat_gr_def                            false
% 3.72/0.99  --sat_epr_types                         true
% 3.72/0.99  --sat_non_cyclic_types                  false
% 3.72/0.99  --sat_finite_models                     false
% 3.72/0.99  --sat_fm_lemmas                         false
% 3.72/0.99  --sat_fm_prep                           false
% 3.72/0.99  --sat_fm_uc_incr                        true
% 3.72/0.99  --sat_out_model                         small
% 3.72/0.99  --sat_out_clauses                       false
% 3.72/0.99  
% 3.72/0.99  ------ QBF Options
% 3.72/0.99  
% 3.72/0.99  --qbf_mode                              false
% 3.72/0.99  --qbf_elim_univ                         false
% 3.72/0.99  --qbf_dom_inst                          none
% 3.72/0.99  --qbf_dom_pre_inst                      false
% 3.72/0.99  --qbf_sk_in                             false
% 3.72/0.99  --qbf_pred_elim                         true
% 3.72/0.99  --qbf_split                             512
% 3.72/0.99  
% 3.72/0.99  ------ BMC1 Options
% 3.72/0.99  
% 3.72/0.99  --bmc1_incremental                      false
% 3.72/0.99  --bmc1_axioms                           reachable_all
% 3.72/0.99  --bmc1_min_bound                        0
% 3.72/0.99  --bmc1_max_bound                        -1
% 3.72/0.99  --bmc1_max_bound_default                -1
% 3.72/0.99  --bmc1_symbol_reachability              true
% 3.72/0.99  --bmc1_property_lemmas                  false
% 3.72/0.99  --bmc1_k_induction                      false
% 3.72/0.99  --bmc1_non_equiv_states                 false
% 3.72/0.99  --bmc1_deadlock                         false
% 3.72/0.99  --bmc1_ucm                              false
% 3.72/0.99  --bmc1_add_unsat_core                   none
% 3.72/0.99  --bmc1_unsat_core_children              false
% 3.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/0.99  --bmc1_out_stat                         full
% 3.72/0.99  --bmc1_ground_init                      false
% 3.72/0.99  --bmc1_pre_inst_next_state              false
% 3.72/0.99  --bmc1_pre_inst_state                   false
% 3.72/0.99  --bmc1_pre_inst_reach_state             false
% 3.72/0.99  --bmc1_out_unsat_core                   false
% 3.72/0.99  --bmc1_aig_witness_out                  false
% 3.72/0.99  --bmc1_verbose                          false
% 3.72/0.99  --bmc1_dump_clauses_tptp                false
% 3.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.72/0.99  --bmc1_dump_file                        -
% 3.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.72/0.99  --bmc1_ucm_extend_mode                  1
% 3.72/0.99  --bmc1_ucm_init_mode                    2
% 3.72/0.99  --bmc1_ucm_cone_mode                    none
% 3.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.72/0.99  --bmc1_ucm_relax_model                  4
% 3.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/0.99  --bmc1_ucm_layered_model                none
% 3.72/0.99  --bmc1_ucm_max_lemma_size               10
% 3.72/0.99  
% 3.72/0.99  ------ AIG Options
% 3.72/0.99  
% 3.72/0.99  --aig_mode                              false
% 3.72/0.99  
% 3.72/0.99  ------ Instantiation Options
% 3.72/0.99  
% 3.72/0.99  --instantiation_flag                    true
% 3.72/0.99  --inst_sos_flag                         true
% 3.72/0.99  --inst_sos_phase                        true
% 3.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/0.99  --inst_lit_sel_side                     num_symb
% 3.72/0.99  --inst_solver_per_active                1400
% 3.72/0.99  --inst_solver_calls_frac                1.
% 3.72/0.99  --inst_passive_queue_type               priority_queues
% 3.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/0.99  --inst_passive_queues_freq              [25;2]
% 3.72/0.99  --inst_dismatching                      true
% 3.72/0.99  --inst_eager_unprocessed_to_passive     true
% 3.72/0.99  --inst_prop_sim_given                   true
% 3.72/0.99  --inst_prop_sim_new                     false
% 3.72/0.99  --inst_subs_new                         false
% 3.72/0.99  --inst_eq_res_simp                      false
% 3.72/0.99  --inst_subs_given                       false
% 3.72/0.99  --inst_orphan_elimination               true
% 3.72/0.99  --inst_learning_loop_flag               true
% 3.72/0.99  --inst_learning_start                   3000
% 3.72/0.99  --inst_learning_factor                  2
% 3.72/0.99  --inst_start_prop_sim_after_learn       3
% 3.72/0.99  --inst_sel_renew                        solver
% 3.72/0.99  --inst_lit_activity_flag                true
% 3.72/0.99  --inst_restr_to_given                   false
% 3.72/0.99  --inst_activity_threshold               500
% 3.72/0.99  --inst_out_proof                        true
% 3.72/0.99  
% 3.72/0.99  ------ Resolution Options
% 3.72/0.99  
% 3.72/0.99  --resolution_flag                       true
% 3.72/0.99  --res_lit_sel                           adaptive
% 3.72/0.99  --res_lit_sel_side                      none
% 3.72/0.99  --res_ordering                          kbo
% 3.72/0.99  --res_to_prop_solver                    active
% 3.72/0.99  --res_prop_simpl_new                    false
% 3.72/0.99  --res_prop_simpl_given                  true
% 3.72/0.99  --res_passive_queue_type                priority_queues
% 3.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/0.99  --res_passive_queues_freq               [15;5]
% 3.72/0.99  --res_forward_subs                      full
% 3.72/0.99  --res_backward_subs                     full
% 3.72/0.99  --res_forward_subs_resolution           true
% 3.72/0.99  --res_backward_subs_resolution          true
% 3.72/0.99  --res_orphan_elimination                true
% 3.72/0.99  --res_time_limit                        2.
% 3.72/0.99  --res_out_proof                         true
% 3.72/0.99  
% 3.72/0.99  ------ Superposition Options
% 3.72/0.99  
% 3.72/0.99  --superposition_flag                    true
% 3.72/0.99  --sup_passive_queue_type                priority_queues
% 3.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.72/0.99  --demod_completeness_check              fast
% 3.72/0.99  --demod_use_ground                      true
% 3.72/0.99  --sup_to_prop_solver                    passive
% 3.72/0.99  --sup_prop_simpl_new                    true
% 3.72/0.99  --sup_prop_simpl_given                  true
% 3.72/0.99  --sup_fun_splitting                     true
% 3.72/0.99  --sup_smt_interval                      50000
% 3.72/0.99  
% 3.72/0.99  ------ Superposition Simplification Setup
% 3.72/0.99  
% 3.72/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.72/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.72/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.72/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.72/0.99  --sup_immed_triv                        [TrivRules]
% 3.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.99  --sup_immed_bw_main                     []
% 3.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.99  --sup_input_bw                          []
% 3.72/0.99  
% 3.72/0.99  ------ Combination Options
% 3.72/0.99  
% 3.72/0.99  --comb_res_mult                         3
% 3.72/0.99  --comb_sup_mult                         2
% 3.72/0.99  --comb_inst_mult                        10
% 3.72/0.99  
% 3.72/0.99  ------ Debug Options
% 3.72/0.99  
% 3.72/0.99  --dbg_backtrace                         false
% 3.72/0.99  --dbg_dump_prop_clauses                 false
% 3.72/0.99  --dbg_dump_prop_clauses_file            -
% 3.72/0.99  --dbg_out_stat                          false
% 3.72/0.99  ------ Parsing...
% 3.72/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  ------ Proving...
% 3.72/0.99  ------ Problem Properties 
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  clauses                                 43
% 3.72/0.99  conjectures                             11
% 3.72/0.99  EPR                                     11
% 3.72/0.99  Horn                                    39
% 3.72/0.99  unary                                   18
% 3.72/0.99  binary                                  4
% 3.72/0.99  lits                                    150
% 3.72/0.99  lits eq                                 35
% 3.72/0.99  fd_pure                                 0
% 3.72/0.99  fd_pseudo                               0
% 3.72/0.99  fd_cond                                 5
% 3.72/0.99  fd_pseudo_cond                          2
% 3.72/0.99  AC symbols                              0
% 3.72/0.99  
% 3.72/0.99  ------ Schedule dynamic 5 is on 
% 3.72/0.99  
% 3.72/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ 
% 3.72/0.99  Current options:
% 3.72/0.99  ------ 
% 3.72/0.99  
% 3.72/0.99  ------ Input Options
% 3.72/0.99  
% 3.72/0.99  --out_options                           all
% 3.72/0.99  --tptp_safe_out                         true
% 3.72/0.99  --problem_path                          ""
% 3.72/0.99  --include_path                          ""
% 3.72/0.99  --clausifier                            res/vclausify_rel
% 3.72/0.99  --clausifier_options                    ""
% 3.72/0.99  --stdin                                 false
% 3.72/0.99  --stats_out                             all
% 3.72/0.99  
% 3.72/0.99  ------ General Options
% 3.72/0.99  
% 3.72/0.99  --fof                                   false
% 3.72/0.99  --time_out_real                         305.
% 3.72/0.99  --time_out_virtual                      -1.
% 3.72/0.99  --symbol_type_check                     false
% 3.72/0.99  --clausify_out                          false
% 3.72/0.99  --sig_cnt_out                           false
% 3.72/0.99  --trig_cnt_out                          false
% 3.72/0.99  --trig_cnt_out_tolerance                1.
% 3.72/0.99  --trig_cnt_out_sk_spl                   false
% 3.72/0.99  --abstr_cl_out                          false
% 3.72/0.99  
% 3.72/0.99  ------ Global Options
% 3.72/0.99  
% 3.72/0.99  --schedule                              default
% 3.72/0.99  --add_important_lit                     false
% 3.72/0.99  --prop_solver_per_cl                    1000
% 3.72/0.99  --min_unsat_core                        false
% 3.72/0.99  --soft_assumptions                      false
% 3.72/0.99  --soft_lemma_size                       3
% 3.72/0.99  --prop_impl_unit_size                   0
% 3.72/0.99  --prop_impl_unit                        []
% 3.72/0.99  --share_sel_clauses                     true
% 3.72/0.99  --reset_solvers                         false
% 3.72/0.99  --bc_imp_inh                            [conj_cone]
% 3.72/0.99  --conj_cone_tolerance                   3.
% 3.72/0.99  --extra_neg_conj                        none
% 3.72/0.99  --large_theory_mode                     true
% 3.72/0.99  --prolific_symb_bound                   200
% 3.72/0.99  --lt_threshold                          2000
% 3.72/0.99  --clause_weak_htbl                      true
% 3.72/0.99  --gc_record_bc_elim                     false
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing Options
% 3.72/0.99  
% 3.72/0.99  --preprocessing_flag                    true
% 3.72/0.99  --time_out_prep_mult                    0.1
% 3.72/0.99  --splitting_mode                        input
% 3.72/0.99  --splitting_grd                         true
% 3.72/0.99  --splitting_cvd                         false
% 3.72/0.99  --splitting_cvd_svl                     false
% 3.72/0.99  --splitting_nvd                         32
% 3.72/0.99  --sub_typing                            true
% 3.72/0.99  --prep_gs_sim                           true
% 3.72/0.99  --prep_unflatten                        true
% 3.72/0.99  --prep_res_sim                          true
% 3.72/0.99  --prep_upred                            true
% 3.72/0.99  --prep_sem_filter                       exhaustive
% 3.72/0.99  --prep_sem_filter_out                   false
% 3.72/0.99  --pred_elim                             true
% 3.72/0.99  --res_sim_input                         true
% 3.72/0.99  --eq_ax_congr_red                       true
% 3.72/0.99  --pure_diseq_elim                       true
% 3.72/0.99  --brand_transform                       false
% 3.72/0.99  --non_eq_to_eq                          false
% 3.72/0.99  --prep_def_merge                        true
% 3.72/0.99  --prep_def_merge_prop_impl              false
% 3.72/0.99  --prep_def_merge_mbd                    true
% 3.72/0.99  --prep_def_merge_tr_red                 false
% 3.72/0.99  --prep_def_merge_tr_cl                  false
% 3.72/0.99  --smt_preprocessing                     true
% 3.72/0.99  --smt_ac_axioms                         fast
% 3.72/0.99  --preprocessed_out                      false
% 3.72/0.99  --preprocessed_stats                    false
% 3.72/0.99  
% 3.72/0.99  ------ Abstraction refinement Options
% 3.72/0.99  
% 3.72/0.99  --abstr_ref                             []
% 3.72/0.99  --abstr_ref_prep                        false
% 3.72/0.99  --abstr_ref_until_sat                   false
% 3.72/0.99  --abstr_ref_sig_restrict                funpre
% 3.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/0.99  --abstr_ref_under                       []
% 3.72/0.99  
% 3.72/0.99  ------ SAT Options
% 3.72/0.99  
% 3.72/0.99  --sat_mode                              false
% 3.72/0.99  --sat_fm_restart_options                ""
% 3.72/0.99  --sat_gr_def                            false
% 3.72/0.99  --sat_epr_types                         true
% 3.72/0.99  --sat_non_cyclic_types                  false
% 3.72/0.99  --sat_finite_models                     false
% 3.72/0.99  --sat_fm_lemmas                         false
% 3.72/0.99  --sat_fm_prep                           false
% 3.72/0.99  --sat_fm_uc_incr                        true
% 3.72/0.99  --sat_out_model                         small
% 3.72/0.99  --sat_out_clauses                       false
% 3.72/0.99  
% 3.72/0.99  ------ QBF Options
% 3.72/0.99  
% 3.72/0.99  --qbf_mode                              false
% 3.72/0.99  --qbf_elim_univ                         false
% 3.72/0.99  --qbf_dom_inst                          none
% 3.72/0.99  --qbf_dom_pre_inst                      false
% 3.72/0.99  --qbf_sk_in                             false
% 3.72/0.99  --qbf_pred_elim                         true
% 3.72/0.99  --qbf_split                             512
% 3.72/0.99  
% 3.72/0.99  ------ BMC1 Options
% 3.72/0.99  
% 3.72/0.99  --bmc1_incremental                      false
% 3.72/0.99  --bmc1_axioms                           reachable_all
% 3.72/0.99  --bmc1_min_bound                        0
% 3.72/0.99  --bmc1_max_bound                        -1
% 3.72/0.99  --bmc1_max_bound_default                -1
% 3.72/0.99  --bmc1_symbol_reachability              true
% 3.72/0.99  --bmc1_property_lemmas                  false
% 3.72/0.99  --bmc1_k_induction                      false
% 3.72/0.99  --bmc1_non_equiv_states                 false
% 3.72/0.99  --bmc1_deadlock                         false
% 3.72/0.99  --bmc1_ucm                              false
% 3.72/0.99  --bmc1_add_unsat_core                   none
% 3.72/0.99  --bmc1_unsat_core_children              false
% 3.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/0.99  --bmc1_out_stat                         full
% 3.72/0.99  --bmc1_ground_init                      false
% 3.72/0.99  --bmc1_pre_inst_next_state              false
% 3.72/0.99  --bmc1_pre_inst_state                   false
% 3.72/0.99  --bmc1_pre_inst_reach_state             false
% 3.72/0.99  --bmc1_out_unsat_core                   false
% 3.72/0.99  --bmc1_aig_witness_out                  false
% 3.72/0.99  --bmc1_verbose                          false
% 3.72/0.99  --bmc1_dump_clauses_tptp                false
% 3.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.72/0.99  --bmc1_dump_file                        -
% 3.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.72/0.99  --bmc1_ucm_extend_mode                  1
% 3.72/0.99  --bmc1_ucm_init_mode                    2
% 3.72/0.99  --bmc1_ucm_cone_mode                    none
% 3.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.72/0.99  --bmc1_ucm_relax_model                  4
% 3.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/0.99  --bmc1_ucm_layered_model                none
% 3.72/0.99  --bmc1_ucm_max_lemma_size               10
% 3.72/0.99  
% 3.72/0.99  ------ AIG Options
% 3.72/0.99  
% 3.72/0.99  --aig_mode                              false
% 3.72/0.99  
% 3.72/0.99  ------ Instantiation Options
% 3.72/0.99  
% 3.72/0.99  --instantiation_flag                    true
% 3.72/0.99  --inst_sos_flag                         true
% 3.72/0.99  --inst_sos_phase                        true
% 3.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/0.99  --inst_lit_sel_side                     none
% 3.72/0.99  --inst_solver_per_active                1400
% 3.72/0.99  --inst_solver_calls_frac                1.
% 3.72/0.99  --inst_passive_queue_type               priority_queues
% 3.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/0.99  --inst_passive_queues_freq              [25;2]
% 3.72/0.99  --inst_dismatching                      true
% 3.72/0.99  --inst_eager_unprocessed_to_passive     true
% 3.72/0.99  --inst_prop_sim_given                   true
% 3.72/0.99  --inst_prop_sim_new                     false
% 3.72/0.99  --inst_subs_new                         false
% 3.72/0.99  --inst_eq_res_simp                      false
% 3.72/0.99  --inst_subs_given                       false
% 3.72/0.99  --inst_orphan_elimination               true
% 3.72/0.99  --inst_learning_loop_flag               true
% 3.72/0.99  --inst_learning_start                   3000
% 3.72/0.99  --inst_learning_factor                  2
% 3.72/0.99  --inst_start_prop_sim_after_learn       3
% 3.72/0.99  --inst_sel_renew                        solver
% 3.72/0.99  --inst_lit_activity_flag                true
% 3.72/0.99  --inst_restr_to_given                   false
% 3.72/0.99  --inst_activity_threshold               500
% 3.72/0.99  --inst_out_proof                        true
% 3.72/0.99  
% 3.72/0.99  ------ Resolution Options
% 3.72/0.99  
% 3.72/0.99  --resolution_flag                       false
% 3.72/0.99  --res_lit_sel                           adaptive
% 3.72/0.99  --res_lit_sel_side                      none
% 3.72/0.99  --res_ordering                          kbo
% 3.72/0.99  --res_to_prop_solver                    active
% 3.72/0.99  --res_prop_simpl_new                    false
% 3.72/0.99  --res_prop_simpl_given                  true
% 3.72/0.99  --res_passive_queue_type                priority_queues
% 3.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/0.99  --res_passive_queues_freq               [15;5]
% 3.72/0.99  --res_forward_subs                      full
% 3.72/0.99  --res_backward_subs                     full
% 3.72/0.99  --res_forward_subs_resolution           true
% 3.72/0.99  --res_backward_subs_resolution          true
% 3.72/0.99  --res_orphan_elimination                true
% 3.72/0.99  --res_time_limit                        2.
% 3.72/0.99  --res_out_proof                         true
% 3.72/0.99  
% 3.72/0.99  ------ Superposition Options
% 3.72/0.99  
% 3.72/0.99  --superposition_flag                    true
% 3.72/0.99  --sup_passive_queue_type                priority_queues
% 3.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.72/0.99  --demod_completeness_check              fast
% 3.72/0.99  --demod_use_ground                      true
% 3.72/0.99  --sup_to_prop_solver                    passive
% 3.72/0.99  --sup_prop_simpl_new                    true
% 3.72/0.99  --sup_prop_simpl_given                  true
% 3.72/0.99  --sup_fun_splitting                     true
% 3.72/0.99  --sup_smt_interval                      50000
% 3.72/0.99  
% 3.72/0.99  ------ Superposition Simplification Setup
% 3.72/0.99  
% 3.72/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.72/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.72/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.72/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.72/0.99  --sup_immed_triv                        [TrivRules]
% 3.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.99  --sup_immed_bw_main                     []
% 3.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.99  --sup_input_bw                          []
% 3.72/0.99  
% 3.72/0.99  ------ Combination Options
% 3.72/0.99  
% 3.72/0.99  --comb_res_mult                         3
% 3.72/0.99  --comb_sup_mult                         2
% 3.72/0.99  --comb_inst_mult                        10
% 3.72/0.99  
% 3.72/0.99  ------ Debug Options
% 3.72/0.99  
% 3.72/0.99  --dbg_backtrace                         false
% 3.72/0.99  --dbg_dump_prop_clauses                 false
% 3.72/0.99  --dbg_dump_prop_clauses_file            -
% 3.72/0.99  --dbg_out_stat                          false
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  % SZS status Theorem for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  fof(f15,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f42,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.72/0.99    inference(ennf_transformation,[],[f15])).
% 3.72/0.99  
% 3.72/0.99  fof(f43,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.99    inference(flattening,[],[f42])).
% 3.72/0.99  
% 3.72/0.99  fof(f58,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.99    inference(nnf_transformation,[],[f43])).
% 3.72/0.99  
% 3.72/0.99  fof(f83,plain,(
% 3.72/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f58])).
% 3.72/0.99  
% 3.72/0.99  fof(f23,conjecture,(
% 3.72/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f24,negated_conjecture,(
% 3.72/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.72/0.99    inference(negated_conjecture,[],[f23])).
% 3.72/0.99  
% 3.72/0.99  fof(f54,plain,(
% 3.72/0.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.72/0.99    inference(ennf_transformation,[],[f24])).
% 3.72/0.99  
% 3.72/0.99  fof(f55,plain,(
% 3.72/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.72/0.99    inference(flattening,[],[f54])).
% 3.72/0.99  
% 3.72/0.99  fof(f60,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK4 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f59,plain,(
% 3.72/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f61,plain,(
% 3.72/0.99    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f55,f60,f59])).
% 3.72/0.99  
% 3.72/0.99  fof(f104,plain,(
% 3.72/0.99    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 3.72/0.99    inference(cnf_transformation,[],[f61])).
% 3.72/0.99  
% 3.72/0.99  fof(f17,axiom,(
% 3.72/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f25,plain,(
% 3.72/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.72/0.99    inference(pure_predicate_removal,[],[f17])).
% 3.72/0.99  
% 3.72/0.99  fof(f87,plain,(
% 3.72/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f25])).
% 3.72/0.99  
% 3.72/0.99  fof(f97,plain,(
% 3.72/0.99    v1_funct_1(sK3)),
% 3.72/0.99    inference(cnf_transformation,[],[f61])).
% 3.72/0.99  
% 3.72/0.99  fof(f99,plain,(
% 3.72/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.72/0.99    inference(cnf_transformation,[],[f61])).
% 3.72/0.99  
% 3.72/0.99  fof(f100,plain,(
% 3.72/0.99    v1_funct_1(sK4)),
% 3.72/0.99    inference(cnf_transformation,[],[f61])).
% 3.72/0.99  
% 3.72/0.99  fof(f102,plain,(
% 3.72/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.72/0.99    inference(cnf_transformation,[],[f61])).
% 3.72/0.99  
% 3.72/0.99  fof(f16,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f44,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.72/0.99    inference(ennf_transformation,[],[f16])).
% 3.72/0.99  
% 3.72/0.99  fof(f45,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.72/0.99    inference(flattening,[],[f44])).
% 3.72/0.99  
% 3.72/0.99  fof(f86,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f45])).
% 3.72/0.99  
% 3.72/0.99  fof(f103,plain,(
% 3.72/0.99    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.72/0.99    inference(cnf_transformation,[],[f61])).
% 3.72/0.99  
% 3.72/0.99  fof(f21,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f50,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.72/0.99    inference(ennf_transformation,[],[f21])).
% 3.72/0.99  
% 3.72/0.99  fof(f51,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.72/0.99    inference(flattening,[],[f50])).
% 3.72/0.99  
% 3.72/0.99  fof(f93,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f51])).
% 3.72/0.99  
% 3.72/0.99  fof(f1,axiom,(
% 3.72/0.99    v1_xboole_0(o_0_0_xboole_0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f62,plain,(
% 3.72/0.99    v1_xboole_0(o_0_0_xboole_0)),
% 3.72/0.99    inference(cnf_transformation,[],[f1])).
% 3.72/0.99  
% 3.72/0.99  fof(f2,axiom,(
% 3.72/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f26,plain,(
% 3.72/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.72/0.99    inference(ennf_transformation,[],[f2])).
% 3.72/0.99  
% 3.72/0.99  fof(f63,plain,(
% 3.72/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f26])).
% 3.72/0.99  
% 3.72/0.99  fof(f98,plain,(
% 3.72/0.99    v1_funct_2(sK3,sK1,sK2)),
% 3.72/0.99    inference(cnf_transformation,[],[f61])).
% 3.72/0.99  
% 3.72/0.99  fof(f101,plain,(
% 3.72/0.99    v1_funct_2(sK4,sK2,sK1)),
% 3.72/0.99    inference(cnf_transformation,[],[f61])).
% 3.72/0.99  
% 3.72/0.99  fof(f106,plain,(
% 3.72/0.99    k1_xboole_0 != sK1),
% 3.72/0.99    inference(cnf_transformation,[],[f61])).
% 3.72/0.99  
% 3.72/0.99  fof(f7,axiom,(
% 3.72/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f71,plain,(
% 3.72/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f7])).
% 3.72/0.99  
% 3.72/0.99  fof(f19,axiom,(
% 3.72/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f89,plain,(
% 3.72/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f19])).
% 3.72/0.99  
% 3.72/0.99  fof(f111,plain,(
% 3.72/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.72/0.99    inference(definition_unfolding,[],[f71,f89])).
% 3.72/0.99  
% 3.72/0.99  fof(f8,axiom,(
% 3.72/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f30,plain,(
% 3.72/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.72/0.99    inference(ennf_transformation,[],[f8])).
% 3.72/0.99  
% 3.72/0.99  fof(f31,plain,(
% 3.72/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/0.99    inference(flattening,[],[f30])).
% 3.72/0.99  
% 3.72/0.99  fof(f74,plain,(
% 3.72/0.99    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f31])).
% 3.72/0.99  
% 3.72/0.99  fof(f12,axiom,(
% 3.72/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f38,plain,(
% 3.72/0.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.72/0.99    inference(ennf_transformation,[],[f12])).
% 3.72/0.99  
% 3.72/0.99  fof(f39,plain,(
% 3.72/0.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/0.99    inference(flattening,[],[f38])).
% 3.72/0.99  
% 3.72/0.99  fof(f80,plain,(
% 3.72/0.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f39])).
% 3.72/0.99  
% 3.72/0.99  fof(f72,plain,(
% 3.72/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f31])).
% 3.72/0.99  
% 3.72/0.99  fof(f73,plain,(
% 3.72/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f31])).
% 3.72/0.99  
% 3.72/0.99  fof(f13,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f40,plain,(
% 3.72/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.99    inference(ennf_transformation,[],[f13])).
% 3.72/0.99  
% 3.72/0.99  fof(f81,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f40])).
% 3.72/0.99  
% 3.72/0.99  fof(f10,axiom,(
% 3.72/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f34,plain,(
% 3.72/0.99    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.72/0.99    inference(ennf_transformation,[],[f10])).
% 3.72/0.99  
% 3.72/0.99  fof(f35,plain,(
% 3.72/0.99    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/0.99    inference(flattening,[],[f34])).
% 3.72/0.99  
% 3.72/0.99  fof(f77,plain,(
% 3.72/0.99    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f35])).
% 3.72/0.99  
% 3.72/0.99  fof(f20,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f48,plain,(
% 3.72/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.72/0.99    inference(ennf_transformation,[],[f20])).
% 3.72/0.99  
% 3.72/0.99  fof(f49,plain,(
% 3.72/0.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.72/0.99    inference(flattening,[],[f48])).
% 3.72/0.99  
% 3.72/0.99  fof(f90,plain,(
% 3.72/0.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f49])).
% 3.72/0.99  
% 3.72/0.99  fof(f22,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f52,plain,(
% 3.72/0.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.72/0.99    inference(ennf_transformation,[],[f22])).
% 3.72/0.99  
% 3.72/0.99  fof(f53,plain,(
% 3.72/0.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.72/0.99    inference(flattening,[],[f52])).
% 3.72/0.99  
% 3.72/0.99  fof(f95,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f53])).
% 3.72/0.99  
% 3.72/0.99  fof(f9,axiom,(
% 3.72/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f32,plain,(
% 3.72/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.72/0.99    inference(ennf_transformation,[],[f9])).
% 3.72/0.99  
% 3.72/0.99  fof(f33,plain,(
% 3.72/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/0.99    inference(flattening,[],[f32])).
% 3.72/0.99  
% 3.72/0.99  fof(f76,plain,(
% 3.72/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f33])).
% 3.72/0.99  
% 3.72/0.99  fof(f5,axiom,(
% 3.72/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f66,plain,(
% 3.72/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.72/0.99    inference(cnf_transformation,[],[f5])).
% 3.72/0.99  
% 3.72/0.99  fof(f110,plain,(
% 3.72/0.99    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.72/0.99    inference(definition_unfolding,[],[f66,f89])).
% 3.72/0.99  
% 3.72/0.99  fof(f18,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f46,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.72/0.99    inference(ennf_transformation,[],[f18])).
% 3.72/0.99  
% 3.72/0.99  fof(f47,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.72/0.99    inference(flattening,[],[f46])).
% 3.72/0.99  
% 3.72/0.99  fof(f88,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f47])).
% 3.72/0.99  
% 3.72/0.99  fof(f11,axiom,(
% 3.72/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f36,plain,(
% 3.72/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.72/0.99    inference(ennf_transformation,[],[f11])).
% 3.72/0.99  
% 3.72/0.99  fof(f37,plain,(
% 3.72/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/0.99    inference(flattening,[],[f36])).
% 3.72/0.99  
% 3.72/0.99  fof(f79,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f37])).
% 3.72/0.99  
% 3.72/0.99  fof(f113,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f79,f89])).
% 3.72/0.99  
% 3.72/0.99  fof(f14,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f41,plain,(
% 3.72/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.99    inference(ennf_transformation,[],[f14])).
% 3.72/0.99  
% 3.72/0.99  fof(f82,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f41])).
% 3.72/0.99  
% 3.72/0.99  fof(f108,plain,(
% 3.72/0.99    k2_funct_1(sK3) != sK4),
% 3.72/0.99    inference(cnf_transformation,[],[f61])).
% 3.72/0.99  
% 3.72/0.99  cnf(c_22,plain,
% 3.72/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.72/0.99      | X3 = X2 ),
% 3.72/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_38,negated_conjecture,
% 3.72/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_482,plain,
% 3.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | X3 = X0
% 3.72/0.99      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 3.72/0.99      | k6_partfun1(sK1) != X3
% 3.72/0.99      | sK1 != X2
% 3.72/0.99      | sK1 != X1 ),
% 3.72/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_38]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_483,plain,
% 3.72/0.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.72/0.99      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.72/0.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.72/0.99      inference(unflattening,[status(thm)],[c_482]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_25,plain,
% 3.72/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.72/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_491,plain,
% 3.72/0.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.72/0.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.72/0.99      inference(forward_subsumption_resolution,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_483,c_25]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1403,plain,
% 3.72/0.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.72/0.99      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_45,negated_conjecture,
% 3.72/0.99      ( v1_funct_1(sK3) ),
% 3.72/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_43,negated_conjecture,
% 3.72/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.72/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_42,negated_conjecture,
% 3.72/0.99      ( v1_funct_1(sK4) ),
% 3.72/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_40,negated_conjecture,
% 3.72/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.72/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_23,plain,
% 3.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.72/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X3) ),
% 3.72/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1691,plain,
% 3.72/0.99      ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.72/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.72/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.72/0.99      | ~ v1_funct_1(sK4)
% 3.72/0.99      | ~ v1_funct_1(sK3) ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2329,plain,
% 3.72/0.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_1403,c_45,c_43,c_42,c_40,c_491,c_1691]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_39,negated_conjecture,
% 3.72/0.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.72/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_29,plain,
% 3.72/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.72/0.99      | ~ v1_funct_2(X3,X4,X1)
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | v2_funct_1(X0)
% 3.72/0.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X3)
% 3.72/0.99      | k2_relset_1(X4,X1,X3) != X1
% 3.72/0.99      | k1_xboole_0 = X2 ),
% 3.72/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1416,plain,
% 3.72/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.72/0.99      | k1_xboole_0 = X3
% 3.72/0.99      | v1_funct_2(X4,X1,X3) != iProver_top
% 3.72/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.72/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 3.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.99      | v2_funct_1(X4) = iProver_top
% 3.72/0.99      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 3.72/0.99      | v1_funct_1(X4) != iProver_top
% 3.72/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_0,plain,
% 3.72/0.99      ( v1_xboole_0(o_0_0_xboole_0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1438,plain,
% 3.72/0.99      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1,plain,
% 3.72/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1437,plain,
% 3.72/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2512,plain,
% 3.72/0.99      ( k1_xboole_0 = o_0_0_xboole_0 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1438,c_1437]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6841,plain,
% 3.72/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.72/0.99      | o_0_0_xboole_0 = X3
% 3.72/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.72/0.99      | v1_funct_2(X4,X1,X3) != iProver_top
% 3.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 3.72/0.99      | v2_funct_1(X4) = iProver_top
% 3.72/0.99      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 3.72/0.99      | v1_funct_1(X2) != iProver_top
% 3.72/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_1416,c_2512]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6843,plain,
% 3.72/0.99      ( o_0_0_xboole_0 = X0
% 3.72/0.99      | v1_funct_2(X1,sK2,X0) != iProver_top
% 3.72/0.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.72/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 3.72/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.72/0.99      | v2_funct_1(X1) = iProver_top
% 3.72/0.99      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 3.72/0.99      | v1_funct_1(X1) != iProver_top
% 3.72/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_39,c_6841]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_46,plain,
% 3.72/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_44,negated_conjecture,
% 3.72/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.72/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_47,plain,
% 3.72/0.99      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_48,plain,
% 3.72/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6856,plain,
% 3.72/0.99      ( v1_funct_1(X1) != iProver_top
% 3.72/0.99      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 3.72/0.99      | v2_funct_1(X1) = iProver_top
% 3.72/0.99      | v1_funct_2(X1,sK2,X0) != iProver_top
% 3.72/0.99      | o_0_0_xboole_0 = X0
% 3.72/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_6843,c_46,c_47,c_48]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6857,plain,
% 3.72/0.99      ( o_0_0_xboole_0 = X0
% 3.72/0.99      | v1_funct_2(X1,sK2,X0) != iProver_top
% 3.72/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 3.72/0.99      | v2_funct_1(X1) = iProver_top
% 3.72/0.99      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 3.72/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_6856]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6862,plain,
% 3.72/0.99      ( sK1 = o_0_0_xboole_0
% 3.72/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.72/0.99      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 3.72/0.99      | v2_funct_1(sK4) = iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2329,c_6857]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_49,plain,
% 3.72/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_41,negated_conjecture,
% 3.72/0.99      ( v1_funct_2(sK4,sK2,sK1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_50,plain,
% 3.72/0.99      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_51,plain,
% 3.72/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_36,negated_conjecture,
% 3.72/0.99      ( k1_xboole_0 != sK1 ),
% 3.72/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1519,plain,
% 3.72/0.99      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_800,plain,
% 3.72/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.72/0.99      theory(equality) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1580,plain,
% 3.72/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_800]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1880,plain,
% 3.72/0.99      ( v1_xboole_0(sK1)
% 3.72/0.99      | ~ v1_xboole_0(o_0_0_xboole_0)
% 3.72/0.99      | sK1 != o_0_0_xboole_0 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_1580]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8,plain,
% 3.72/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2896,plain,
% 3.72/0.99      ( v2_funct_1(k6_partfun1(sK1)) ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2897,plain,
% 3.72/0.99      ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2896]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6965,plain,
% 3.72/0.99      ( v2_funct_1(sK4) = iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_6862,c_49,c_50,c_51,c_36,c_0,c_1519,c_1880,c_2897]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_10,plain,
% 3.72/0.99      ( ~ v2_funct_1(X0)
% 3.72/0.99      | v2_funct_1(k2_funct_1(X0))
% 3.72/0.99      | ~ v1_relat_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1430,plain,
% 3.72/0.99      ( v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v2_funct_1(k2_funct_1(X0)) = iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top
% 3.72/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_18,plain,
% 3.72/0.99      ( ~ v2_funct_1(X0)
% 3.72/0.99      | ~ v1_relat_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1424,plain,
% 3.72/0.99      ( k2_funct_1(k2_funct_1(X0)) = X0
% 3.72/0.99      | v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top
% 3.72/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3604,plain,
% 3.72/0.99      ( k2_funct_1(k2_funct_1(k2_funct_1(X0))) = k2_funct_1(X0)
% 3.72/0.99      | v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(k2_funct_1(X0)) != iProver_top
% 3.72/0.99      | v1_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_funct_1(k2_funct_1(X0)) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1430,c_1424]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_12,plain,
% 3.72/0.99      ( ~ v2_funct_1(X0)
% 3.72/0.99      | ~ v1_relat_1(X0)
% 3.72/0.99      | v1_relat_1(k2_funct_1(X0))
% 3.72/0.99      | ~ v1_funct_1(X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_113,plain,
% 3.72/0.99      ( v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top
% 3.72/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_11,plain,
% 3.72/0.99      ( ~ v2_funct_1(X0)
% 3.72/0.99      | ~ v1_relat_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | v1_funct_1(k2_funct_1(X0)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_116,plain,
% 3.72/0.99      ( v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top
% 3.72/0.99      | v1_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8760,plain,
% 3.72/0.99      ( v1_funct_1(X0) != iProver_top
% 3.72/0.99      | k2_funct_1(k2_funct_1(k2_funct_1(X0))) = k2_funct_1(X0)
% 3.72/0.99      | v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_3604,c_113,c_116]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8761,plain,
% 3.72/0.99      ( k2_funct_1(k2_funct_1(k2_funct_1(X0))) = k2_funct_1(X0)
% 3.72/0.99      | v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top
% 3.72/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_8760]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8767,plain,
% 3.72/0.99      ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_funct_1(k2_funct_1(X0))
% 3.72/0.99      | v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(k2_funct_1(X0)) != iProver_top
% 3.72/0.99      | v1_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_funct_1(k2_funct_1(X0)) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1430,c_8761]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_12371,plain,
% 3.72/0.99      ( v1_funct_1(X0) != iProver_top
% 3.72/0.99      | k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_funct_1(k2_funct_1(X0))
% 3.72/0.99      | v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_8767,c_113,c_116]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_12372,plain,
% 3.72/0.99      ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_funct_1(k2_funct_1(X0))
% 3.72/0.99      | v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top
% 3.72/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_12371]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_12380,plain,
% 3.72/0.99      ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK4)))) = k2_funct_1(k2_funct_1(sK4))
% 3.72/0.99      | v1_relat_1(sK4) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_6965,c_12372]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6973,plain,
% 3.72/0.99      ( k2_funct_1(k2_funct_1(sK4)) = sK4
% 3.72/0.99      | v1_relat_1(sK4) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_6965,c_1424]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_19,plain,
% 3.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | v1_relat_1(X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1564,plain,
% 3.72/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.72/0.99      | v1_relat_1(sK4) ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1852,plain,
% 3.72/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.72/0.99      | v1_relat_1(sK4) ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_1564]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1853,plain,
% 3.72/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.72/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1852]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3977,plain,
% 3.72/0.99      ( ~ v2_funct_1(sK4)
% 3.72/0.99      | ~ v1_relat_1(sK4)
% 3.72/0.99      | ~ v1_funct_1(sK4)
% 3.72/0.99      | k2_funct_1(k2_funct_1(sK4)) = sK4 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3978,plain,
% 3.72/0.99      ( k2_funct_1(k2_funct_1(sK4)) = sK4
% 3.72/0.99      | v2_funct_1(sK4) != iProver_top
% 3.72/0.99      | v1_relat_1(sK4) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_3977]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7247,plain,
% 3.72/0.99      ( k2_funct_1(k2_funct_1(sK4)) = sK4 ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_6973,c_49,c_50,c_51,c_36,c_0,c_1519,c_1853,c_1880,
% 3.72/0.99                 c_2897,c_3978,c_6862]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_16,plain,
% 3.72/0.99      ( ~ v2_funct_1(X0)
% 3.72/0.99      | ~ v1_relat_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1426,plain,
% 3.72/0.99      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
% 3.72/0.99      | v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top
% 3.72/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4844,plain,
% 3.72/0.99      ( k1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
% 3.72/0.99      | v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(k2_funct_1(X0)) != iProver_top
% 3.72/0.99      | v1_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_funct_1(k2_funct_1(X0)) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1430,c_1426]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_11519,plain,
% 3.72/0.99      ( v1_funct_1(X0) != iProver_top
% 3.72/0.99      | k1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
% 3.72/0.99      | v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_4844,c_113,c_116]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_11520,plain,
% 3.72/0.99      ( k1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
% 3.72/0.99      | v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top
% 3.72/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_11519]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_11528,plain,
% 3.72/0.99      ( k1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(sK4)),k2_funct_1(sK4))) = k2_relat_1(k2_funct_1(sK4))
% 3.72/0.99      | v1_relat_1(sK4) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_6965,c_11520]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_27,plain,
% 3.72/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.72/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.72/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.72/0.99      | ~ v1_funct_1(X2)
% 3.72/0.99      | ~ v1_funct_1(X3)
% 3.72/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_495,plain,
% 3.72/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.72/0.99      | ~ v1_funct_2(X3,X2,X1)
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X3)
% 3.72/0.99      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.72/0.99      | k2_relset_1(X1,X2,X0) = X2
% 3.72/0.99      | k6_partfun1(X2) != k6_partfun1(sK1)
% 3.72/0.99      | sK1 != X2 ),
% 3.72/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_496,plain,
% 3.72/0.99      ( ~ v1_funct_2(X0,X1,sK1)
% 3.72/0.99      | ~ v1_funct_2(X2,sK1,X1)
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X2)
% 3.72/0.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.72/0.99      | k2_relset_1(X1,sK1,X0) = sK1
% 3.72/0.99      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 3.72/0.99      inference(unflattening,[status(thm)],[c_495]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_587,plain,
% 3.72/0.99      ( ~ v1_funct_2(X0,X1,sK1)
% 3.72/0.99      | ~ v1_funct_2(X2,sK1,X1)
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X2)
% 3.72/0.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.72/0.99      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 3.72/0.99      inference(equality_resolution_simp,[status(thm)],[c_496]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1402,plain,
% 3.72/0.99      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.72/0.99      | k2_relset_1(X0,sK1,X2) = sK1
% 3.72/0.99      | v1_funct_2(X2,X0,sK1) != iProver_top
% 3.72/0.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.72/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.72/0.99      | v1_funct_1(X2) != iProver_top
% 3.72/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1901,plain,
% 3.72/0.99      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 3.72/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.72/0.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.72/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top
% 3.72/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.72/0.99      inference(equality_resolution,[status(thm)],[c_1402]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2336,plain,
% 3.72/0.99      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_1901,c_46,c_47,c_48,c_49,c_50,c_51]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_33,plain,
% 3.72/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ v2_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.72/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.72/0.99      | k1_xboole_0 = X2 ),
% 3.72/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1412,plain,
% 3.72/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.72/0.99      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 3.72/0.99      | k1_xboole_0 = X1
% 3.72/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.99      | v2_funct_1(X2) != iProver_top
% 3.72/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2822,plain,
% 3.72/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.72/0.99      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 3.72/0.99      | o_0_0_xboole_0 = X1
% 3.72/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.99      | v2_funct_1(X2) != iProver_top
% 3.72/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_1412,c_2512]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2827,plain,
% 3.72/0.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 3.72/0.99      | sK1 = o_0_0_xboole_0
% 3.72/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.72/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.72/0.99      | v2_funct_1(sK4) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2336,c_2822]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3468,plain,
% 3.72/0.99      ( v2_funct_1(sK4) != iProver_top
% 3.72/0.99      | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_2827,c_49,c_50,c_51,c_36,c_0,c_1519,c_1880]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3469,plain,
% 3.72/0.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 3.72/0.99      | v2_funct_1(sK4) != iProver_top ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_3468]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6975,plain,
% 3.72/0.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_6965,c_3469]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_13,plain,
% 3.72/0.99      ( ~ v2_funct_1(X0)
% 3.72/0.99      | ~ v1_relat_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1429,plain,
% 3.72/0.99      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.72/0.99      | v2_funct_1(X0) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top
% 3.72/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_6971,plain,
% 3.72/0.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 3.72/0.99      | v1_relat_1(sK4) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_6965,c_1429]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7253,plain,
% 3.72/0.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_6971,c_49,c_51,c_1853]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_11529,plain,
% 3.72/0.99      ( k1_relat_1(k6_partfun1(sK2)) = k1_relat_1(sK4)
% 3.72/0.99      | v1_relat_1(sK4) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.72/0.99      inference(light_normalisation,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_11528,c_6975,c_7247,c_7253]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5,plain,
% 3.72/0.99      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_11530,plain,
% 3.72/0.99      ( k1_relat_1(sK4) = sK2
% 3.72/0.99      | v1_relat_1(sK4) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_11529,c_5]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_11542,plain,
% 3.72/0.99      ( k1_relat_1(sK4) = sK2 ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_11530,c_49,c_51,c_1853]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1407,plain,
% 3.72/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1410,plain,
% 3.72/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_26,plain,
% 3.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X3)
% 3.72/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1418,plain,
% 3.72/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.72/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.72/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.99      | v1_funct_1(X5) != iProver_top
% 3.72/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5017,plain,
% 3.72/0.99      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 3.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.99      | v1_funct_1(X2) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1410,c_1418]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5216,plain,
% 3.72/0.99      ( v1_funct_1(X2) != iProver_top
% 3.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.99      | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_5017,c_49]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5217,plain,
% 3.72/0.99      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 3.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.72/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_5216]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5225,plain,
% 3.72/0.99      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
% 3.72/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1407,c_5217]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5226,plain,
% 3.72/0.99      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
% 3.72/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.72/0.99      inference(light_normalisation,[status(thm)],[c_5225,c_2329]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5340,plain,
% 3.72/0.99      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_5226,c_46]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_17,plain,
% 3.72/0.99      ( ~ v2_funct_1(X0)
% 3.72/0.99      | ~ v1_relat_1(X0)
% 3.72/0.99      | ~ v1_relat_1(X1)
% 3.72/0.99      | ~ v1_funct_1(X0)
% 3.72/0.99      | ~ v1_funct_1(X1)
% 3.72/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 3.72/0.99      | k2_funct_1(X0) = X1
% 3.72/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1425,plain,
% 3.72/0.99      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.72/0.99      | k2_funct_1(X1) = X0
% 3.72/0.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.72/0.99      | v2_funct_1(X1) != iProver_top
% 3.72/0.99      | v1_relat_1(X1) != iProver_top
% 3.72/0.99      | v1_relat_1(X0) != iProver_top
% 3.72/0.99      | v1_funct_1(X1) != iProver_top
% 3.72/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5342,plain,
% 3.72/0.99      ( k2_funct_1(sK4) = sK3
% 3.72/0.99      | k1_relat_1(sK4) != k2_relat_1(sK3)
% 3.72/0.99      | k6_partfun1(k2_relat_1(sK4)) != k6_partfun1(sK1)
% 3.72/0.99      | v2_funct_1(sK4) != iProver_top
% 3.72/0.99      | v1_relat_1(sK4) != iProver_top
% 3.72/0.99      | v1_relat_1(sK3) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top
% 3.72/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_5340,c_1425]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_20,plain,
% 3.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1422,plain,
% 3.72/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.72/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2879,plain,
% 3.72/0.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1407,c_1422]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2880,plain,
% 3.72/0.99      ( k2_relat_1(sK3) = sK2 ),
% 3.72/0.99      inference(light_normalisation,[status(thm)],[c_2879,c_39]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2878,plain,
% 3.72/0.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1410,c_1422]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2881,plain,
% 3.72/0.99      ( k2_relat_1(sK4) = sK1 ),
% 3.72/0.99      inference(light_normalisation,[status(thm)],[c_2878,c_2336]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5343,plain,
% 3.72/0.99      ( k2_funct_1(sK4) = sK3
% 3.72/0.99      | k1_relat_1(sK4) != sK2
% 3.72/0.99      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 3.72/0.99      | v2_funct_1(sK4) != iProver_top
% 3.72/0.99      | v1_relat_1(sK4) != iProver_top
% 3.72/0.99      | v1_relat_1(sK3) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top
% 3.72/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.72/0.99      inference(light_normalisation,[status(thm)],[c_5342,c_2880,c_2881]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_5344,plain,
% 3.72/0.99      ( k2_funct_1(sK4) = sK3
% 3.72/0.99      | k1_relat_1(sK4) != sK2
% 3.72/0.99      | v2_funct_1(sK4) != iProver_top
% 3.72/0.99      | v1_relat_1(sK4) != iProver_top
% 3.72/0.99      | v1_relat_1(sK3) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top
% 3.72/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.72/0.99      inference(equality_resolution_simp,[status(thm)],[c_5343]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2220,plain,
% 3.72/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.72/0.99      | v1_relat_1(sK3) ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2221,plain,
% 3.72/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.72/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2220]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8624,plain,
% 3.72/0.99      ( k1_relat_1(sK4) != sK2 | k2_funct_1(sK4) = sK3 ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_5344,c_46,c_48,c_49,c_50,c_51,c_36,c_0,c_1519,c_1853,
% 3.72/0.99                 c_1880,c_2221,c_2897,c_6862]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8625,plain,
% 3.72/0.99      ( k2_funct_1(sK4) = sK3 | k1_relat_1(sK4) != sK2 ),
% 3.72/0.99      inference(renaming,[status(thm)],[c_8624]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_11544,plain,
% 3.72/0.99      ( k2_funct_1(sK4) = sK3 | sK2 != sK2 ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_11542,c_8625]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_11546,plain,
% 3.72/0.99      ( k2_funct_1(sK4) = sK3 ),
% 3.72/0.99      inference(equality_resolution_simp,[status(thm)],[c_11544]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_12381,plain,
% 3.72/0.99      ( k2_funct_1(sK3) = sK4
% 3.72/0.99      | v1_relat_1(sK4) != iProver_top
% 3.72/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.72/0.99      inference(light_normalisation,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_12380,c_7247,c_11546]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_34,negated_conjecture,
% 3.72/0.99      ( k2_funct_1(sK3) != sK4 ),
% 3.72/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(contradiction,plain,
% 3.72/0.99      ( $false ),
% 3.72/0.99      inference(minisat,[status(thm)],[c_12381,c_1853,c_34,c_51,c_49]) ).
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  ------                               Statistics
% 3.72/0.99  
% 3.72/0.99  ------ General
% 3.72/0.99  
% 3.72/0.99  abstr_ref_over_cycles:                  0
% 3.72/0.99  abstr_ref_under_cycles:                 0
% 3.72/0.99  gc_basic_clause_elim:                   0
% 3.72/0.99  forced_gc_time:                         0
% 3.72/0.99  parsing_time:                           0.011
% 3.72/0.99  unif_index_cands_time:                  0.
% 3.72/0.99  unif_index_add_time:                    0.
% 3.72/0.99  orderings_time:                         0.
% 3.72/0.99  out_proof_time:                         0.015
% 3.72/0.99  total_time:                             0.501
% 3.72/0.99  num_of_symbols:                         54
% 3.72/0.99  num_of_terms:                           16804
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing
% 3.72/0.99  
% 3.72/0.99  num_of_splits:                          0
% 3.72/0.99  num_of_split_atoms:                     0
% 3.72/0.99  num_of_reused_defs:                     0
% 3.72/0.99  num_eq_ax_congr_red:                    0
% 3.72/0.99  num_of_sem_filtered_clauses:            1
% 3.72/0.99  num_of_subtypes:                        0
% 3.72/0.99  monotx_restored_types:                  0
% 3.72/0.99  sat_num_of_epr_types:                   0
% 3.72/0.99  sat_num_of_non_cyclic_types:            0
% 3.72/0.99  sat_guarded_non_collapsed_types:        0
% 3.72/0.99  num_pure_diseq_elim:                    0
% 3.72/0.99  simp_replaced_by:                       0
% 3.72/0.99  res_preprocessed:                       208
% 3.72/0.99  prep_upred:                             0
% 3.72/0.99  prep_unflattend:                        12
% 3.72/0.99  smt_new_axioms:                         0
% 3.72/0.99  pred_elim_cands:                        6
% 3.72/0.99  pred_elim:                              1
% 3.72/0.99  pred_elim_cl:                           1
% 3.72/0.99  pred_elim_cycles:                       3
% 3.72/0.99  merged_defs:                            0
% 3.72/0.99  merged_defs_ncl:                        0
% 3.72/0.99  bin_hyper_res:                          0
% 3.72/0.99  prep_cycles:                            4
% 3.72/0.99  pred_elim_time:                         0.006
% 3.72/0.99  splitting_time:                         0.
% 3.72/0.99  sem_filter_time:                        0.
% 3.72/0.99  monotx_time:                            0.001
% 3.72/0.99  subtype_inf_time:                       0.
% 3.72/0.99  
% 3.72/0.99  ------ Problem properties
% 3.72/0.99  
% 3.72/0.99  clauses:                                43
% 3.72/0.99  conjectures:                            11
% 3.72/0.99  epr:                                    11
% 3.72/0.99  horn:                                   39
% 3.72/0.99  ground:                                 14
% 3.72/0.99  unary:                                  18
% 3.72/0.99  binary:                                 4
% 3.72/0.99  lits:                                   150
% 3.72/0.99  lits_eq:                                35
% 3.72/0.99  fd_pure:                                0
% 3.72/0.99  fd_pseudo:                              0
% 3.72/0.99  fd_cond:                                5
% 3.72/0.99  fd_pseudo_cond:                         2
% 3.72/0.99  ac_symbols:                             0
% 3.72/0.99  
% 3.72/0.99  ------ Propositional Solver
% 3.72/0.99  
% 3.72/0.99  prop_solver_calls:                      31
% 3.72/0.99  prop_fast_solver_calls:                 2225
% 3.72/0.99  smt_solver_calls:                       0
% 3.72/0.99  smt_fast_solver_calls:                  0
% 3.72/0.99  prop_num_of_clauses:                    5866
% 3.72/0.99  prop_preprocess_simplified:             13634
% 3.72/0.99  prop_fo_subsumed:                       198
% 3.72/0.99  prop_solver_time:                       0.
% 3.72/0.99  smt_solver_time:                        0.
% 3.72/0.99  smt_fast_solver_time:                   0.
% 3.72/0.99  prop_fast_solver_time:                  0.
% 3.72/0.99  prop_unsat_core_time:                   0.
% 3.72/0.99  
% 3.72/0.99  ------ QBF
% 3.72/0.99  
% 3.72/0.99  qbf_q_res:                              0
% 3.72/0.99  qbf_num_tautologies:                    0
% 3.72/0.99  qbf_prep_cycles:                        0
% 3.72/0.99  
% 3.72/0.99  ------ BMC1
% 3.72/0.99  
% 3.72/0.99  bmc1_current_bound:                     -1
% 3.72/0.99  bmc1_last_solved_bound:                 -1
% 3.72/0.99  bmc1_unsat_core_size:                   -1
% 3.72/0.99  bmc1_unsat_core_parents_size:           -1
% 3.72/0.99  bmc1_merge_next_fun:                    0
% 3.72/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.72/0.99  
% 3.72/0.99  ------ Instantiation
% 3.72/0.99  
% 3.72/0.99  inst_num_of_clauses:                    1402
% 3.72/0.99  inst_num_in_passive:                    264
% 3.72/0.99  inst_num_in_active:                     812
% 3.72/0.99  inst_num_in_unprocessed:                326
% 3.72/0.99  inst_num_of_loops:                      900
% 3.72/0.99  inst_num_of_learning_restarts:          0
% 3.72/0.99  inst_num_moves_active_passive:          86
% 3.72/0.99  inst_lit_activity:                      0
% 3.72/0.99  inst_lit_activity_moves:                1
% 3.72/0.99  inst_num_tautologies:                   0
% 3.72/0.99  inst_num_prop_implied:                  0
% 3.72/0.99  inst_num_existing_simplified:           0
% 3.72/0.99  inst_num_eq_res_simplified:             0
% 3.72/0.99  inst_num_child_elim:                    0
% 3.72/0.99  inst_num_of_dismatching_blockings:      427
% 3.72/0.99  inst_num_of_non_proper_insts:           1389
% 3.72/0.99  inst_num_of_duplicates:                 0
% 3.72/0.99  inst_inst_num_from_inst_to_res:         0
% 3.72/0.99  inst_dismatching_checking_time:         0.
% 3.72/0.99  
% 3.72/0.99  ------ Resolution
% 3.72/0.99  
% 3.72/0.99  res_num_of_clauses:                     0
% 3.72/0.99  res_num_in_passive:                     0
% 3.72/0.99  res_num_in_active:                      0
% 3.72/0.99  res_num_of_loops:                       212
% 3.72/0.99  res_forward_subset_subsumed:            68
% 3.72/0.99  res_backward_subset_subsumed:           0
% 3.72/0.99  res_forward_subsumed:                   0
% 3.72/0.99  res_backward_subsumed:                  0
% 3.72/0.99  res_forward_subsumption_resolution:     2
% 3.72/0.99  res_backward_subsumption_resolution:    0
% 3.72/0.99  res_clause_to_clause_subsumption:       661
% 3.72/0.99  res_orphan_elimination:                 0
% 3.72/0.99  res_tautology_del:                      40
% 3.72/0.99  res_num_eq_res_simplified:              1
% 3.72/0.99  res_num_sel_changes:                    0
% 3.72/0.99  res_moves_from_active_to_pass:          0
% 3.72/0.99  
% 3.72/0.99  ------ Superposition
% 3.72/0.99  
% 3.72/0.99  sup_time_total:                         0.
% 3.72/0.99  sup_time_generating:                    0.
% 3.72/0.99  sup_time_sim_full:                      0.
% 3.72/0.99  sup_time_sim_immed:                     0.
% 3.72/0.99  
% 3.72/0.99  sup_num_of_clauses:                     319
% 3.72/0.99  sup_num_in_active:                      167
% 3.72/0.99  sup_num_in_passive:                     152
% 3.72/0.99  sup_num_of_loops:                       179
% 3.72/0.99  sup_fw_superposition:                   152
% 3.72/0.99  sup_bw_superposition:                   180
% 3.72/0.99  sup_immediate_simplified:               80
% 3.72/0.99  sup_given_eliminated:                   1
% 3.72/0.99  comparisons_done:                       0
% 3.72/0.99  comparisons_avoided:                    4
% 3.72/0.99  
% 3.72/0.99  ------ Simplifications
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  sim_fw_subset_subsumed:                 13
% 3.72/0.99  sim_bw_subset_subsumed:                 7
% 3.72/0.99  sim_fw_subsumed:                        7
% 3.72/0.99  sim_bw_subsumed:                        0
% 3.72/0.99  sim_fw_subsumption_res:                 0
% 3.72/0.99  sim_bw_subsumption_res:                 0
% 3.72/0.99  sim_tautology_del:                      0
% 3.72/0.99  sim_eq_tautology_del:                   22
% 3.72/0.99  sim_eq_res_simp:                        2
% 3.72/0.99  sim_fw_demodulated:                     18
% 3.72/0.99  sim_bw_demodulated:                     11
% 3.72/0.99  sim_light_normalised:                   56
% 3.72/0.99  sim_joinable_taut:                      0
% 3.72/0.99  sim_joinable_simp:                      0
% 3.72/0.99  sim_ac_normalised:                      0
% 3.72/0.99  sim_smt_subsumption:                    0
% 3.72/0.99  
%------------------------------------------------------------------------------
