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
% DateTime   : Thu Dec  3 12:03:18 EST 2020

% Result     : Theorem 31.90s
% Output     : CNFRefutation 31.90s
% Verified   : 
% Statistics : Number of formulae       :  265 (2421 expanded)
%              Number of clauses        :  170 ( 804 expanded)
%              Number of leaves         :   25 ( 536 expanded)
%              Depth                    :   29
%              Number of atoms          :  728 (15595 expanded)
%              Number of equality atoms :  350 (5926 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f26,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

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
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

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
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

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
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
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
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
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
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f55,f61,f60])).

fof(f98,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f62])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f96,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f62])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f52])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f97,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f48])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f100,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f21,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f95,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f77,f94])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f62])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f79,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f101,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f82,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f107,plain,(
    ! [X0] : k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f76,f94,f94])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f85,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f110,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f85,f94])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f109,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f78,f94])).

fof(f83,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f105,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f75,f94])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f104,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1188,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1203,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2848,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1203])).

cnf(c_44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_1593,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2208,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_2209,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2208])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2426,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2427,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2426])).

cnf(c_2957,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2848,c_44,c_2209,c_2427])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1186,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_2849,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_1203])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_1265,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1327,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_1531,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_1532,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1531])).

cnf(c_1658,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1659,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1658])).

cnf(c_2964,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2849,c_42,c_1532,c_1659])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1198,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4478,plain,
    ( k5_relat_1(sK2,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK2,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2964,c_1198])).

cnf(c_7524,plain,
    ( k5_relat_1(k5_relat_1(sK2,sK3),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2957,c_4478])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1189,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4707,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1189])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4817,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4707,c_43])).

cnf(c_4818,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4817])).

cnf(c_4826,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_4818])).

cnf(c_26,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_35,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_410,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_29,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_51,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_412,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_51])).

cnf(c_1183,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1257,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1839,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1183,c_40,c_39,c_38,c_37,c_51,c_410,c_1257])).

cnf(c_4827,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4826,c_1839])).

cnf(c_41,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_5383,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4827,c_41])).

cnf(c_7526,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7524,c_5383])).

cnf(c_15574,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,sK2)) = k5_relat_1(k6_partfun1(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_2964,c_7526])).

cnf(c_23,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_23,c_5])).

cnf(c_1184,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_1971,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_1184])).

cnf(c_2420,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1971,c_42,c_1532,c_1659])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1197,plain,
    ( k5_relat_1(k6_partfun1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3366,plain,
    ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2420,c_1197])).

cnf(c_1974,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1971])).

cnf(c_2708,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k6_partfun1(X0),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2710,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_2708])).

cnf(c_4081,plain,
    ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3366,c_39,c_1531,c_1658,c_1974,c_2710])).

cnf(c_15583,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_15574,c_4081])).

cnf(c_8,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1200,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_16070,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(k5_relat_1(sK3,sK2))) = iProver_top
    | v1_relat_1(k5_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_15583,c_1200])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1193,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2018,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1186,c_1193])).

cnf(c_36,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2019,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2018,c_36])).

cnf(c_16071,plain,
    ( r1_tarski(sK1,k2_relat_1(k5_relat_1(sK3,sK2))) = iProver_top
    | v1_relat_1(k5_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16070,c_2019])).

cnf(c_1201,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4708,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_1189])).

cnf(c_5085,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4708,c_41])).

cnf(c_5086,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5085])).

cnf(c_5093,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_5086])).

cnf(c_5104,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5093,c_43])).

cnf(c_1192,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5106,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5104,c_1192])).

cnf(c_10060,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5106,c_41,c_42,c_43,c_44])).

cnf(c_10064,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK2)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10060,c_1203])).

cnf(c_10444,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_10064])).

cnf(c_16074,plain,
    ( r1_tarski(sK1,k2_relat_1(k5_relat_1(sK3,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16071,c_42,c_1532,c_1659,c_10444])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_482,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_34])).

cnf(c_483,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_485,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_40])).

cnf(c_1178,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_2971,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2964,c_1178])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_454,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_34])).

cnf(c_455,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_457,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_455,c_40])).

cnf(c_1180,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_1695,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1180,c_40,c_39,c_455,c_1531,c_1658])).

cnf(c_2159,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2019,c_1695])).

cnf(c_3028,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2971,c_2159])).

cnf(c_3368,plain,
    ( k5_relat_1(k6_partfun1(X0),k4_relat_1(sK2)) = k4_relat_1(sK2)
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3028,c_1197])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1821,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1824,plain,
    ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1821])).

cnf(c_15202,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | k5_relat_1(k6_partfun1(X0),k4_relat_1(sK2)) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3368,c_42,c_1532,c_1659,c_1824])).

cnf(c_15203,plain,
    ( k5_relat_1(k6_partfun1(X0),k4_relat_1(sK2)) = k4_relat_1(sK2)
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15202])).

cnf(c_1190,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2847,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X0)) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_1203])).

cnf(c_4722,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_2847])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1199,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5812,plain,
    ( k5_relat_1(k4_relat_1(k6_partfun1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_partfun1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4722,c_1199])).

cnf(c_13,plain,
    ( k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_5817,plain,
    ( k5_relat_1(k6_partfun1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_partfun1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5812,c_13])).

cnf(c_6810,plain,
    ( k5_relat_1(k6_partfun1(X0),k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) ),
    inference(superposition,[status(thm)],[c_2964,c_5817])).

cnf(c_15208,plain,
    ( k4_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) = k4_relat_1(sK2)
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15203,c_6810])).

cnf(c_16080,plain,
    ( k4_relat_1(k5_relat_1(sK2,k6_partfun1(k2_relat_1(k5_relat_1(sK3,sK2))))) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_16074,c_15208])).

cnf(c_1202,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_16252,plain,
    ( v1_relat_1(k5_relat_1(sK2,k6_partfun1(k2_relat_1(k5_relat_1(sK3,sK2))))) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16080,c_1202])).

cnf(c_16499,plain,
    ( v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16252,c_42,c_1532,c_1659,c_1824])).

cnf(c_16513,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_16499,c_1198])).

cnf(c_119851,plain,
    ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),X0) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2964,c_16513])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_440,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_34])).

cnf(c_441,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_443,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_40])).

cnf(c_1181,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_1698,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1181,c_40,c_39,c_441,c_1531,c_1658])).

cnf(c_2158,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2019,c_1698])).

cnf(c_3027,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2971,c_2158])).

cnf(c_119874,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_119851,c_3027])).

cnf(c_120823,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2957,c_119874])).

cnf(c_1970,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1184])).

cnf(c_3365,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1970,c_1197])).

cnf(c_3766,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3365,c_44,c_2209,c_2427])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1196,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2009,plain,
    ( k5_relat_1(k4_relat_1(X0),k6_partfun1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1196])).

cnf(c_2968,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2)))) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2964,c_2009])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_468,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_34])).

cnf(c_469,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_471,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_40])).

cnf(c_1179,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_2970,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2964,c_1179])).

cnf(c_2972,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2970,c_2971])).

cnf(c_2974,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k4_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2968,c_2972])).

cnf(c_3482,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK3))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2957,c_1199])).

cnf(c_6361,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2964,c_3482])).

cnf(c_6365,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_6361,c_5383])).

cnf(c_6366,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_6365,c_13])).

cnf(c_6756,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k4_relat_1(sK2))) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6366,c_1200])).

cnf(c_6757,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6756,c_2972])).

cnf(c_11,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_6758,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6757,c_11])).

cnf(c_2561,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2568,plain,
    ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2561])).

cnf(c_7798,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6758,c_42,c_44,c_1532,c_1659,c_1824,c_2209,c_2427,c_2568])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1205,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2843,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2420,c_1205])).

cnf(c_7804,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_7798,c_2843])).

cnf(c_10228,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k4_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2974,c_2974,c_7804])).

cnf(c_120851,plain,
    ( k4_relat_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_120823,c_3766,c_5383,c_10228])).

cnf(c_31,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3031,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_2971,c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_120851,c_3031])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:05:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 31.90/4.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.90/4.52  
% 31.90/4.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.90/4.52  
% 31.90/4.52  ------  iProver source info
% 31.90/4.52  
% 31.90/4.52  git: date: 2020-06-30 10:37:57 +0100
% 31.90/4.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.90/4.52  git: non_committed_changes: false
% 31.90/4.52  git: last_make_outside_of_git: false
% 31.90/4.52  
% 31.90/4.52  ------ 
% 31.90/4.52  
% 31.90/4.52  ------ Input Options
% 31.90/4.52  
% 31.90/4.52  --out_options                           all
% 31.90/4.52  --tptp_safe_out                         true
% 31.90/4.52  --problem_path                          ""
% 31.90/4.52  --include_path                          ""
% 31.90/4.52  --clausifier                            res/vclausify_rel
% 31.90/4.52  --clausifier_options                    ""
% 31.90/4.52  --stdin                                 false
% 31.90/4.52  --stats_out                             all
% 31.90/4.52  
% 31.90/4.52  ------ General Options
% 31.90/4.52  
% 31.90/4.52  --fof                                   false
% 31.90/4.52  --time_out_real                         305.
% 31.90/4.52  --time_out_virtual                      -1.
% 31.90/4.52  --symbol_type_check                     false
% 31.90/4.52  --clausify_out                          false
% 31.90/4.52  --sig_cnt_out                           false
% 31.90/4.52  --trig_cnt_out                          false
% 31.90/4.52  --trig_cnt_out_tolerance                1.
% 31.90/4.52  --trig_cnt_out_sk_spl                   false
% 31.90/4.52  --abstr_cl_out                          false
% 31.90/4.52  
% 31.90/4.52  ------ Global Options
% 31.90/4.52  
% 31.90/4.52  --schedule                              default
% 31.90/4.52  --add_important_lit                     false
% 31.90/4.52  --prop_solver_per_cl                    1000
% 31.90/4.52  --min_unsat_core                        false
% 31.90/4.52  --soft_assumptions                      false
% 31.90/4.52  --soft_lemma_size                       3
% 31.90/4.52  --prop_impl_unit_size                   0
% 31.90/4.52  --prop_impl_unit                        []
% 31.90/4.52  --share_sel_clauses                     true
% 31.90/4.52  --reset_solvers                         false
% 31.90/4.52  --bc_imp_inh                            [conj_cone]
% 31.90/4.52  --conj_cone_tolerance                   3.
% 31.90/4.52  --extra_neg_conj                        none
% 31.90/4.52  --large_theory_mode                     true
% 31.90/4.52  --prolific_symb_bound                   200
% 31.90/4.52  --lt_threshold                          2000
% 31.90/4.52  --clause_weak_htbl                      true
% 31.90/4.52  --gc_record_bc_elim                     false
% 31.90/4.52  
% 31.90/4.52  ------ Preprocessing Options
% 31.90/4.52  
% 31.90/4.52  --preprocessing_flag                    true
% 31.90/4.52  --time_out_prep_mult                    0.1
% 31.90/4.52  --splitting_mode                        input
% 31.90/4.52  --splitting_grd                         true
% 31.90/4.52  --splitting_cvd                         false
% 31.90/4.52  --splitting_cvd_svl                     false
% 31.90/4.52  --splitting_nvd                         32
% 31.90/4.52  --sub_typing                            true
% 31.90/4.52  --prep_gs_sim                           true
% 31.90/4.52  --prep_unflatten                        true
% 31.90/4.52  --prep_res_sim                          true
% 31.90/4.52  --prep_upred                            true
% 31.90/4.52  --prep_sem_filter                       exhaustive
% 31.90/4.52  --prep_sem_filter_out                   false
% 31.90/4.52  --pred_elim                             true
% 31.90/4.52  --res_sim_input                         true
% 31.90/4.52  --eq_ax_congr_red                       true
% 31.90/4.52  --pure_diseq_elim                       true
% 31.90/4.52  --brand_transform                       false
% 31.90/4.52  --non_eq_to_eq                          false
% 31.90/4.52  --prep_def_merge                        true
% 31.90/4.52  --prep_def_merge_prop_impl              false
% 31.90/4.52  --prep_def_merge_mbd                    true
% 31.90/4.52  --prep_def_merge_tr_red                 false
% 31.90/4.52  --prep_def_merge_tr_cl                  false
% 31.90/4.52  --smt_preprocessing                     true
% 31.90/4.52  --smt_ac_axioms                         fast
% 31.90/4.52  --preprocessed_out                      false
% 31.90/4.52  --preprocessed_stats                    false
% 31.90/4.52  
% 31.90/4.52  ------ Abstraction refinement Options
% 31.90/4.52  
% 31.90/4.52  --abstr_ref                             []
% 31.90/4.52  --abstr_ref_prep                        false
% 31.90/4.52  --abstr_ref_until_sat                   false
% 31.90/4.52  --abstr_ref_sig_restrict                funpre
% 31.90/4.52  --abstr_ref_af_restrict_to_split_sk     false
% 31.90/4.52  --abstr_ref_under                       []
% 31.90/4.52  
% 31.90/4.52  ------ SAT Options
% 31.90/4.52  
% 31.90/4.52  --sat_mode                              false
% 31.90/4.52  --sat_fm_restart_options                ""
% 31.90/4.52  --sat_gr_def                            false
% 31.90/4.52  --sat_epr_types                         true
% 31.90/4.52  --sat_non_cyclic_types                  false
% 31.90/4.52  --sat_finite_models                     false
% 31.90/4.52  --sat_fm_lemmas                         false
% 31.90/4.52  --sat_fm_prep                           false
% 31.90/4.52  --sat_fm_uc_incr                        true
% 31.90/4.52  --sat_out_model                         small
% 31.90/4.52  --sat_out_clauses                       false
% 31.90/4.52  
% 31.90/4.52  ------ QBF Options
% 31.90/4.52  
% 31.90/4.52  --qbf_mode                              false
% 31.90/4.52  --qbf_elim_univ                         false
% 31.90/4.52  --qbf_dom_inst                          none
% 31.90/4.52  --qbf_dom_pre_inst                      false
% 31.90/4.52  --qbf_sk_in                             false
% 31.90/4.52  --qbf_pred_elim                         true
% 31.90/4.52  --qbf_split                             512
% 31.90/4.52  
% 31.90/4.52  ------ BMC1 Options
% 31.90/4.52  
% 31.90/4.52  --bmc1_incremental                      false
% 31.90/4.52  --bmc1_axioms                           reachable_all
% 31.90/4.52  --bmc1_min_bound                        0
% 31.90/4.52  --bmc1_max_bound                        -1
% 31.90/4.52  --bmc1_max_bound_default                -1
% 31.90/4.52  --bmc1_symbol_reachability              true
% 31.90/4.52  --bmc1_property_lemmas                  false
% 31.90/4.52  --bmc1_k_induction                      false
% 31.90/4.52  --bmc1_non_equiv_states                 false
% 31.90/4.52  --bmc1_deadlock                         false
% 31.90/4.52  --bmc1_ucm                              false
% 31.90/4.52  --bmc1_add_unsat_core                   none
% 31.90/4.52  --bmc1_unsat_core_children              false
% 31.90/4.52  --bmc1_unsat_core_extrapolate_axioms    false
% 31.90/4.52  --bmc1_out_stat                         full
% 31.90/4.52  --bmc1_ground_init                      false
% 31.90/4.52  --bmc1_pre_inst_next_state              false
% 31.90/4.52  --bmc1_pre_inst_state                   false
% 31.90/4.52  --bmc1_pre_inst_reach_state             false
% 31.90/4.52  --bmc1_out_unsat_core                   false
% 31.90/4.52  --bmc1_aig_witness_out                  false
% 31.90/4.52  --bmc1_verbose                          false
% 31.90/4.52  --bmc1_dump_clauses_tptp                false
% 31.90/4.52  --bmc1_dump_unsat_core_tptp             false
% 31.90/4.52  --bmc1_dump_file                        -
% 31.90/4.52  --bmc1_ucm_expand_uc_limit              128
% 31.90/4.52  --bmc1_ucm_n_expand_iterations          6
% 31.90/4.52  --bmc1_ucm_extend_mode                  1
% 31.90/4.52  --bmc1_ucm_init_mode                    2
% 31.90/4.52  --bmc1_ucm_cone_mode                    none
% 31.90/4.52  --bmc1_ucm_reduced_relation_type        0
% 31.90/4.52  --bmc1_ucm_relax_model                  4
% 31.90/4.52  --bmc1_ucm_full_tr_after_sat            true
% 31.90/4.52  --bmc1_ucm_expand_neg_assumptions       false
% 31.90/4.52  --bmc1_ucm_layered_model                none
% 31.90/4.52  --bmc1_ucm_max_lemma_size               10
% 31.90/4.52  
% 31.90/4.52  ------ AIG Options
% 31.90/4.52  
% 31.90/4.52  --aig_mode                              false
% 31.90/4.52  
% 31.90/4.52  ------ Instantiation Options
% 31.90/4.52  
% 31.90/4.52  --instantiation_flag                    true
% 31.90/4.52  --inst_sos_flag                         true
% 31.90/4.52  --inst_sos_phase                        true
% 31.90/4.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.90/4.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.90/4.52  --inst_lit_sel_side                     num_symb
% 31.90/4.52  --inst_solver_per_active                1400
% 31.90/4.52  --inst_solver_calls_frac                1.
% 31.90/4.52  --inst_passive_queue_type               priority_queues
% 31.90/4.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.90/4.52  --inst_passive_queues_freq              [25;2]
% 31.90/4.52  --inst_dismatching                      true
% 31.90/4.52  --inst_eager_unprocessed_to_passive     true
% 31.90/4.52  --inst_prop_sim_given                   true
% 31.90/4.52  --inst_prop_sim_new                     false
% 31.90/4.52  --inst_subs_new                         false
% 31.90/4.52  --inst_eq_res_simp                      false
% 31.90/4.52  --inst_subs_given                       false
% 31.90/4.52  --inst_orphan_elimination               true
% 31.90/4.52  --inst_learning_loop_flag               true
% 31.90/4.52  --inst_learning_start                   3000
% 31.90/4.52  --inst_learning_factor                  2
% 31.90/4.52  --inst_start_prop_sim_after_learn       3
% 31.90/4.52  --inst_sel_renew                        solver
% 31.90/4.52  --inst_lit_activity_flag                true
% 31.90/4.52  --inst_restr_to_given                   false
% 31.90/4.52  --inst_activity_threshold               500
% 31.90/4.52  --inst_out_proof                        true
% 31.90/4.52  
% 31.90/4.52  ------ Resolution Options
% 31.90/4.52  
% 31.90/4.52  --resolution_flag                       true
% 31.90/4.52  --res_lit_sel                           adaptive
% 31.90/4.52  --res_lit_sel_side                      none
% 31.90/4.52  --res_ordering                          kbo
% 31.90/4.52  --res_to_prop_solver                    active
% 31.90/4.52  --res_prop_simpl_new                    false
% 31.90/4.52  --res_prop_simpl_given                  true
% 31.90/4.52  --res_passive_queue_type                priority_queues
% 31.90/4.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.90/4.52  --res_passive_queues_freq               [15;5]
% 31.90/4.52  --res_forward_subs                      full
% 31.90/4.52  --res_backward_subs                     full
% 31.90/4.52  --res_forward_subs_resolution           true
% 31.90/4.52  --res_backward_subs_resolution          true
% 31.90/4.52  --res_orphan_elimination                true
% 31.90/4.52  --res_time_limit                        2.
% 31.90/4.52  --res_out_proof                         true
% 31.90/4.52  
% 31.90/4.52  ------ Superposition Options
% 31.90/4.52  
% 31.90/4.52  --superposition_flag                    true
% 31.90/4.52  --sup_passive_queue_type                priority_queues
% 31.90/4.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.90/4.52  --sup_passive_queues_freq               [8;1;4]
% 31.90/4.52  --demod_completeness_check              fast
% 31.90/4.52  --demod_use_ground                      true
% 31.90/4.52  --sup_to_prop_solver                    passive
% 31.90/4.52  --sup_prop_simpl_new                    true
% 31.90/4.52  --sup_prop_simpl_given                  true
% 31.90/4.52  --sup_fun_splitting                     true
% 31.90/4.52  --sup_smt_interval                      50000
% 31.90/4.52  
% 31.90/4.52  ------ Superposition Simplification Setup
% 31.90/4.52  
% 31.90/4.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.90/4.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.90/4.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.90/4.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.90/4.52  --sup_full_triv                         [TrivRules;PropSubs]
% 31.90/4.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.90/4.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.90/4.52  --sup_immed_triv                        [TrivRules]
% 31.90/4.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.90/4.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.90/4.52  --sup_immed_bw_main                     []
% 31.90/4.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.90/4.52  --sup_input_triv                        [Unflattening;TrivRules]
% 31.90/4.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.90/4.52  --sup_input_bw                          []
% 31.90/4.52  
% 31.90/4.52  ------ Combination Options
% 31.90/4.52  
% 31.90/4.52  --comb_res_mult                         3
% 31.90/4.52  --comb_sup_mult                         2
% 31.90/4.52  --comb_inst_mult                        10
% 31.90/4.52  
% 31.90/4.52  ------ Debug Options
% 31.90/4.52  
% 31.90/4.52  --dbg_backtrace                         false
% 31.90/4.52  --dbg_dump_prop_clauses                 false
% 31.90/4.52  --dbg_dump_prop_clauses_file            -
% 31.90/4.52  --dbg_out_stat                          false
% 31.90/4.52  ------ Parsing...
% 31.90/4.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.90/4.52  
% 31.90/4.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 31.90/4.52  
% 31.90/4.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.90/4.52  
% 31.90/4.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.90/4.52  ------ Proving...
% 31.90/4.52  ------ Problem Properties 
% 31.90/4.52  
% 31.90/4.52  
% 31.90/4.52  clauses                                 35
% 31.90/4.52  conjectures                             8
% 31.90/4.52  EPR                                     6
% 31.90/4.52  Horn                                    35
% 31.90/4.52  unary                                   14
% 31.90/4.52  binary                                  9
% 31.90/4.52  lits                                    75
% 31.90/4.52  lits eq                                 20
% 31.90/4.52  fd_pure                                 0
% 31.90/4.52  fd_pseudo                               0
% 31.90/4.52  fd_cond                                 0
% 31.90/4.52  fd_pseudo_cond                          1
% 31.90/4.52  AC symbols                              0
% 31.90/4.52  
% 31.90/4.52  ------ Schedule dynamic 5 is on 
% 31.90/4.52  
% 31.90/4.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.90/4.52  
% 31.90/4.52  
% 31.90/4.52  ------ 
% 31.90/4.52  Current options:
% 31.90/4.52  ------ 
% 31.90/4.52  
% 31.90/4.52  ------ Input Options
% 31.90/4.52  
% 31.90/4.52  --out_options                           all
% 31.90/4.52  --tptp_safe_out                         true
% 31.90/4.52  --problem_path                          ""
% 31.90/4.52  --include_path                          ""
% 31.90/4.52  --clausifier                            res/vclausify_rel
% 31.90/4.52  --clausifier_options                    ""
% 31.90/4.52  --stdin                                 false
% 31.90/4.52  --stats_out                             all
% 31.90/4.52  
% 31.90/4.52  ------ General Options
% 31.90/4.52  
% 31.90/4.52  --fof                                   false
% 31.90/4.52  --time_out_real                         305.
% 31.90/4.52  --time_out_virtual                      -1.
% 31.90/4.52  --symbol_type_check                     false
% 31.90/4.52  --clausify_out                          false
% 31.90/4.52  --sig_cnt_out                           false
% 31.90/4.52  --trig_cnt_out                          false
% 31.90/4.52  --trig_cnt_out_tolerance                1.
% 31.90/4.52  --trig_cnt_out_sk_spl                   false
% 31.90/4.52  --abstr_cl_out                          false
% 31.90/4.52  
% 31.90/4.52  ------ Global Options
% 31.90/4.52  
% 31.90/4.52  --schedule                              default
% 31.90/4.52  --add_important_lit                     false
% 31.90/4.52  --prop_solver_per_cl                    1000
% 31.90/4.52  --min_unsat_core                        false
% 31.90/4.52  --soft_assumptions                      false
% 31.90/4.52  --soft_lemma_size                       3
% 31.90/4.52  --prop_impl_unit_size                   0
% 31.90/4.52  --prop_impl_unit                        []
% 31.90/4.52  --share_sel_clauses                     true
% 31.90/4.52  --reset_solvers                         false
% 31.90/4.52  --bc_imp_inh                            [conj_cone]
% 31.90/4.52  --conj_cone_tolerance                   3.
% 31.90/4.52  --extra_neg_conj                        none
% 31.90/4.52  --large_theory_mode                     true
% 31.90/4.52  --prolific_symb_bound                   200
% 31.90/4.52  --lt_threshold                          2000
% 31.90/4.52  --clause_weak_htbl                      true
% 31.90/4.52  --gc_record_bc_elim                     false
% 31.90/4.52  
% 31.90/4.52  ------ Preprocessing Options
% 31.90/4.52  
% 31.90/4.52  --preprocessing_flag                    true
% 31.90/4.52  --time_out_prep_mult                    0.1
% 31.90/4.52  --splitting_mode                        input
% 31.90/4.52  --splitting_grd                         true
% 31.90/4.52  --splitting_cvd                         false
% 31.90/4.52  --splitting_cvd_svl                     false
% 31.90/4.52  --splitting_nvd                         32
% 31.90/4.52  --sub_typing                            true
% 31.90/4.52  --prep_gs_sim                           true
% 31.90/4.52  --prep_unflatten                        true
% 31.90/4.52  --prep_res_sim                          true
% 31.90/4.52  --prep_upred                            true
% 31.90/4.52  --prep_sem_filter                       exhaustive
% 31.90/4.52  --prep_sem_filter_out                   false
% 31.90/4.52  --pred_elim                             true
% 31.90/4.52  --res_sim_input                         true
% 31.90/4.52  --eq_ax_congr_red                       true
% 31.90/4.52  --pure_diseq_elim                       true
% 31.90/4.52  --brand_transform                       false
% 31.90/4.52  --non_eq_to_eq                          false
% 31.90/4.52  --prep_def_merge                        true
% 31.90/4.52  --prep_def_merge_prop_impl              false
% 31.90/4.52  --prep_def_merge_mbd                    true
% 31.90/4.52  --prep_def_merge_tr_red                 false
% 31.90/4.52  --prep_def_merge_tr_cl                  false
% 31.90/4.52  --smt_preprocessing                     true
% 31.90/4.52  --smt_ac_axioms                         fast
% 31.90/4.52  --preprocessed_out                      false
% 31.90/4.52  --preprocessed_stats                    false
% 31.90/4.52  
% 31.90/4.52  ------ Abstraction refinement Options
% 31.90/4.52  
% 31.90/4.52  --abstr_ref                             []
% 31.90/4.52  --abstr_ref_prep                        false
% 31.90/4.52  --abstr_ref_until_sat                   false
% 31.90/4.52  --abstr_ref_sig_restrict                funpre
% 31.90/4.52  --abstr_ref_af_restrict_to_split_sk     false
% 31.90/4.52  --abstr_ref_under                       []
% 31.90/4.52  
% 31.90/4.52  ------ SAT Options
% 31.90/4.52  
% 31.90/4.52  --sat_mode                              false
% 31.90/4.52  --sat_fm_restart_options                ""
% 31.90/4.52  --sat_gr_def                            false
% 31.90/4.52  --sat_epr_types                         true
% 31.90/4.52  --sat_non_cyclic_types                  false
% 31.90/4.52  --sat_finite_models                     false
% 31.90/4.52  --sat_fm_lemmas                         false
% 31.90/4.52  --sat_fm_prep                           false
% 31.90/4.52  --sat_fm_uc_incr                        true
% 31.90/4.52  --sat_out_model                         small
% 31.90/4.52  --sat_out_clauses                       false
% 31.90/4.52  
% 31.90/4.52  ------ QBF Options
% 31.90/4.52  
% 31.90/4.52  --qbf_mode                              false
% 31.90/4.52  --qbf_elim_univ                         false
% 31.90/4.52  --qbf_dom_inst                          none
% 31.90/4.52  --qbf_dom_pre_inst                      false
% 31.90/4.52  --qbf_sk_in                             false
% 31.90/4.52  --qbf_pred_elim                         true
% 31.90/4.52  --qbf_split                             512
% 31.90/4.52  
% 31.90/4.52  ------ BMC1 Options
% 31.90/4.52  
% 31.90/4.52  --bmc1_incremental                      false
% 31.90/4.52  --bmc1_axioms                           reachable_all
% 31.90/4.52  --bmc1_min_bound                        0
% 31.90/4.52  --bmc1_max_bound                        -1
% 31.90/4.52  --bmc1_max_bound_default                -1
% 31.90/4.52  --bmc1_symbol_reachability              true
% 31.90/4.52  --bmc1_property_lemmas                  false
% 31.90/4.52  --bmc1_k_induction                      false
% 31.90/4.52  --bmc1_non_equiv_states                 false
% 31.90/4.52  --bmc1_deadlock                         false
% 31.90/4.52  --bmc1_ucm                              false
% 31.90/4.52  --bmc1_add_unsat_core                   none
% 31.90/4.52  --bmc1_unsat_core_children              false
% 31.90/4.52  --bmc1_unsat_core_extrapolate_axioms    false
% 31.90/4.52  --bmc1_out_stat                         full
% 31.90/4.52  --bmc1_ground_init                      false
% 31.90/4.52  --bmc1_pre_inst_next_state              false
% 31.90/4.52  --bmc1_pre_inst_state                   false
% 31.90/4.52  --bmc1_pre_inst_reach_state             false
% 31.90/4.52  --bmc1_out_unsat_core                   false
% 31.90/4.52  --bmc1_aig_witness_out                  false
% 31.90/4.52  --bmc1_verbose                          false
% 31.90/4.52  --bmc1_dump_clauses_tptp                false
% 31.90/4.52  --bmc1_dump_unsat_core_tptp             false
% 31.90/4.52  --bmc1_dump_file                        -
% 31.90/4.52  --bmc1_ucm_expand_uc_limit              128
% 31.90/4.52  --bmc1_ucm_n_expand_iterations          6
% 31.90/4.52  --bmc1_ucm_extend_mode                  1
% 31.90/4.52  --bmc1_ucm_init_mode                    2
% 31.90/4.52  --bmc1_ucm_cone_mode                    none
% 31.90/4.52  --bmc1_ucm_reduced_relation_type        0
% 31.90/4.52  --bmc1_ucm_relax_model                  4
% 31.90/4.52  --bmc1_ucm_full_tr_after_sat            true
% 31.90/4.52  --bmc1_ucm_expand_neg_assumptions       false
% 31.90/4.52  --bmc1_ucm_layered_model                none
% 31.90/4.52  --bmc1_ucm_max_lemma_size               10
% 31.90/4.52  
% 31.90/4.52  ------ AIG Options
% 31.90/4.52  
% 31.90/4.52  --aig_mode                              false
% 31.90/4.52  
% 31.90/4.52  ------ Instantiation Options
% 31.90/4.52  
% 31.90/4.52  --instantiation_flag                    true
% 31.90/4.52  --inst_sos_flag                         true
% 31.90/4.52  --inst_sos_phase                        true
% 31.90/4.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.90/4.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.90/4.52  --inst_lit_sel_side                     none
% 31.90/4.52  --inst_solver_per_active                1400
% 31.90/4.52  --inst_solver_calls_frac                1.
% 31.90/4.52  --inst_passive_queue_type               priority_queues
% 31.90/4.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.90/4.52  --inst_passive_queues_freq              [25;2]
% 31.90/4.52  --inst_dismatching                      true
% 31.90/4.52  --inst_eager_unprocessed_to_passive     true
% 31.90/4.52  --inst_prop_sim_given                   true
% 31.90/4.52  --inst_prop_sim_new                     false
% 31.90/4.52  --inst_subs_new                         false
% 31.90/4.52  --inst_eq_res_simp                      false
% 31.90/4.52  --inst_subs_given                       false
% 31.90/4.52  --inst_orphan_elimination               true
% 31.90/4.52  --inst_learning_loop_flag               true
% 31.90/4.52  --inst_learning_start                   3000
% 31.90/4.52  --inst_learning_factor                  2
% 31.90/4.52  --inst_start_prop_sim_after_learn       3
% 31.90/4.52  --inst_sel_renew                        solver
% 31.90/4.52  --inst_lit_activity_flag                true
% 31.90/4.52  --inst_restr_to_given                   false
% 31.90/4.52  --inst_activity_threshold               500
% 31.90/4.52  --inst_out_proof                        true
% 31.90/4.52  
% 31.90/4.52  ------ Resolution Options
% 31.90/4.52  
% 31.90/4.52  --resolution_flag                       false
% 31.90/4.52  --res_lit_sel                           adaptive
% 31.90/4.52  --res_lit_sel_side                      none
% 31.90/4.52  --res_ordering                          kbo
% 31.90/4.52  --res_to_prop_solver                    active
% 31.90/4.52  --res_prop_simpl_new                    false
% 31.90/4.52  --res_prop_simpl_given                  true
% 31.90/4.52  --res_passive_queue_type                priority_queues
% 31.90/4.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.90/4.52  --res_passive_queues_freq               [15;5]
% 31.90/4.52  --res_forward_subs                      full
% 31.90/4.52  --res_backward_subs                     full
% 31.90/4.52  --res_forward_subs_resolution           true
% 31.90/4.52  --res_backward_subs_resolution          true
% 31.90/4.52  --res_orphan_elimination                true
% 31.90/4.52  --res_time_limit                        2.
% 31.90/4.52  --res_out_proof                         true
% 31.90/4.52  
% 31.90/4.52  ------ Superposition Options
% 31.90/4.52  
% 31.90/4.52  --superposition_flag                    true
% 31.90/4.52  --sup_passive_queue_type                priority_queues
% 31.90/4.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.90/4.52  --sup_passive_queues_freq               [8;1;4]
% 31.90/4.52  --demod_completeness_check              fast
% 31.90/4.52  --demod_use_ground                      true
% 31.90/4.52  --sup_to_prop_solver                    passive
% 31.90/4.52  --sup_prop_simpl_new                    true
% 31.90/4.52  --sup_prop_simpl_given                  true
% 31.90/4.52  --sup_fun_splitting                     true
% 31.90/4.52  --sup_smt_interval                      50000
% 31.90/4.52  
% 31.90/4.52  ------ Superposition Simplification Setup
% 31.90/4.52  
% 31.90/4.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.90/4.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.90/4.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.90/4.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.90/4.52  --sup_full_triv                         [TrivRules;PropSubs]
% 31.90/4.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.90/4.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.90/4.52  --sup_immed_triv                        [TrivRules]
% 31.90/4.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.90/4.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.90/4.52  --sup_immed_bw_main                     []
% 31.90/4.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.90/4.52  --sup_input_triv                        [Unflattening;TrivRules]
% 31.90/4.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.90/4.52  --sup_input_bw                          []
% 31.90/4.52  
% 31.90/4.52  ------ Combination Options
% 31.90/4.52  
% 31.90/4.52  --comb_res_mult                         3
% 31.90/4.52  --comb_sup_mult                         2
% 31.90/4.52  --comb_inst_mult                        10
% 31.90/4.52  
% 31.90/4.52  ------ Debug Options
% 31.90/4.52  
% 31.90/4.52  --dbg_backtrace                         false
% 31.90/4.52  --dbg_dump_prop_clauses                 false
% 31.90/4.52  --dbg_dump_prop_clauses_file            -
% 31.90/4.52  --dbg_out_stat                          false
% 31.90/4.52  
% 31.90/4.52  
% 31.90/4.52  
% 31.90/4.52  
% 31.90/4.52  ------ Proving...
% 31.90/4.52  
% 31.90/4.52  
% 31.90/4.52  % SZS status Theorem for theBenchmark.p
% 31.90/4.52  
% 31.90/4.52  % SZS output start CNFRefutation for theBenchmark.p
% 31.90/4.52  
% 31.90/4.52  fof(f24,conjecture,(
% 31.90/4.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f25,negated_conjecture,(
% 31.90/4.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 31.90/4.52    inference(negated_conjecture,[],[f24])).
% 31.90/4.52  
% 31.90/4.52  fof(f26,plain,(
% 31.90/4.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 31.90/4.52    inference(pure_predicate_removal,[],[f25])).
% 31.90/4.52  
% 31.90/4.52  fof(f54,plain,(
% 31.90/4.52    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 31.90/4.52    inference(ennf_transformation,[],[f26])).
% 31.90/4.52  
% 31.90/4.52  fof(f55,plain,(
% 31.90/4.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 31.90/4.52    inference(flattening,[],[f54])).
% 31.90/4.52  
% 31.90/4.52  fof(f61,plain,(
% 31.90/4.52    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 31.90/4.52    introduced(choice_axiom,[])).
% 31.90/4.52  
% 31.90/4.52  fof(f60,plain,(
% 31.90/4.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 31.90/4.52    introduced(choice_axiom,[])).
% 31.90/4.52  
% 31.90/4.52  fof(f62,plain,(
% 31.90/4.52    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 31.90/4.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f55,f61,f60])).
% 31.90/4.52  
% 31.90/4.52  fof(f98,plain,(
% 31.90/4.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 31.90/4.52    inference(cnf_transformation,[],[f62])).
% 31.90/4.52  
% 31.90/4.52  fof(f2,axiom,(
% 31.90/4.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f29,plain,(
% 31.90/4.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 31.90/4.52    inference(ennf_transformation,[],[f2])).
% 31.90/4.52  
% 31.90/4.52  fof(f66,plain,(
% 31.90/4.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f29])).
% 31.90/4.52  
% 31.90/4.52  fof(f5,axiom,(
% 31.90/4.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f70,plain,(
% 31.90/4.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 31.90/4.52    inference(cnf_transformation,[],[f5])).
% 31.90/4.52  
% 31.90/4.52  fof(f96,plain,(
% 31.90/4.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 31.90/4.52    inference(cnf_transformation,[],[f62])).
% 31.90/4.52  
% 31.90/4.52  fof(f8,axiom,(
% 31.90/4.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f34,plain,(
% 31.90/4.52    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.90/4.52    inference(ennf_transformation,[],[f8])).
% 31.90/4.52  
% 31.90/4.52  fof(f73,plain,(
% 31.90/4.52    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f34])).
% 31.90/4.52  
% 31.90/4.52  fof(f22,axiom,(
% 31.90/4.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f52,plain,(
% 31.90/4.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 31.90/4.52    inference(ennf_transformation,[],[f22])).
% 31.90/4.52  
% 31.90/4.52  fof(f53,plain,(
% 31.90/4.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 31.90/4.52    inference(flattening,[],[f52])).
% 31.90/4.52  
% 31.90/4.52  fof(f93,plain,(
% 31.90/4.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f53])).
% 31.90/4.52  
% 31.90/4.52  fof(f97,plain,(
% 31.90/4.52    v1_funct_1(sK3)),
% 31.90/4.52    inference(cnf_transformation,[],[f62])).
% 31.90/4.52  
% 31.90/4.52  fof(f19,axiom,(
% 31.90/4.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f48,plain,(
% 31.90/4.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 31.90/4.52    inference(ennf_transformation,[],[f19])).
% 31.90/4.52  
% 31.90/4.52  fof(f49,plain,(
% 31.90/4.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.90/4.52    inference(flattening,[],[f48])).
% 31.90/4.52  
% 31.90/4.52  fof(f59,plain,(
% 31.90/4.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.90/4.52    inference(nnf_transformation,[],[f49])).
% 31.90/4.52  
% 31.90/4.52  fof(f88,plain,(
% 31.90/4.52    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.90/4.52    inference(cnf_transformation,[],[f59])).
% 31.90/4.52  
% 31.90/4.52  fof(f100,plain,(
% 31.90/4.52    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 31.90/4.52    inference(cnf_transformation,[],[f62])).
% 31.90/4.52  
% 31.90/4.52  fof(f21,axiom,(
% 31.90/4.52    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f27,plain,(
% 31.90/4.52    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 31.90/4.52    inference(pure_predicate_removal,[],[f21])).
% 31.90/4.52  
% 31.90/4.52  fof(f92,plain,(
% 31.90/4.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 31.90/4.52    inference(cnf_transformation,[],[f27])).
% 31.90/4.52  
% 31.90/4.52  fof(f95,plain,(
% 31.90/4.52    v1_funct_1(sK2)),
% 31.90/4.52    inference(cnf_transformation,[],[f62])).
% 31.90/4.52  
% 31.90/4.52  fof(f20,axiom,(
% 31.90/4.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f50,plain,(
% 31.90/4.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 31.90/4.52    inference(ennf_transformation,[],[f20])).
% 31.90/4.52  
% 31.90/4.52  fof(f51,plain,(
% 31.90/4.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 31.90/4.52    inference(flattening,[],[f50])).
% 31.90/4.52  
% 31.90/4.52  fof(f91,plain,(
% 31.90/4.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f51])).
% 31.90/4.52  
% 31.90/4.52  fof(f17,axiom,(
% 31.90/4.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f28,plain,(
% 31.90/4.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 31.90/4.52    inference(pure_predicate_removal,[],[f17])).
% 31.90/4.52  
% 31.90/4.52  fof(f46,plain,(
% 31.90/4.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.90/4.52    inference(ennf_transformation,[],[f28])).
% 31.90/4.52  
% 31.90/4.52  fof(f86,plain,(
% 31.90/4.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.90/4.52    inference(cnf_transformation,[],[f46])).
% 31.90/4.52  
% 31.90/4.52  fof(f3,axiom,(
% 31.90/4.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f30,plain,(
% 31.90/4.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 31.90/4.52    inference(ennf_transformation,[],[f3])).
% 31.90/4.52  
% 31.90/4.52  fof(f58,plain,(
% 31.90/4.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 31.90/4.52    inference(nnf_transformation,[],[f30])).
% 31.90/4.52  
% 31.90/4.52  fof(f67,plain,(
% 31.90/4.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f58])).
% 31.90/4.52  
% 31.90/4.52  fof(f11,axiom,(
% 31.90/4.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f35,plain,(
% 31.90/4.52    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 31.90/4.52    inference(ennf_transformation,[],[f11])).
% 31.90/4.52  
% 31.90/4.52  fof(f36,plain,(
% 31.90/4.52    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 31.90/4.52    inference(flattening,[],[f35])).
% 31.90/4.52  
% 31.90/4.52  fof(f77,plain,(
% 31.90/4.52    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f36])).
% 31.90/4.52  
% 31.90/4.52  fof(f23,axiom,(
% 31.90/4.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f94,plain,(
% 31.90/4.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f23])).
% 31.90/4.52  
% 31.90/4.52  fof(f108,plain,(
% 31.90/4.52    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 31.90/4.52    inference(definition_unfolding,[],[f77,f94])).
% 31.90/4.52  
% 31.90/4.52  fof(f6,axiom,(
% 31.90/4.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f32,plain,(
% 31.90/4.52    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.90/4.52    inference(ennf_transformation,[],[f6])).
% 31.90/4.52  
% 31.90/4.52  fof(f71,plain,(
% 31.90/4.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f32])).
% 31.90/4.52  
% 31.90/4.52  fof(f18,axiom,(
% 31.90/4.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f47,plain,(
% 31.90/4.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.90/4.52    inference(ennf_transformation,[],[f18])).
% 31.90/4.52  
% 31.90/4.52  fof(f87,plain,(
% 31.90/4.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.90/4.52    inference(cnf_transformation,[],[f47])).
% 31.90/4.52  
% 31.90/4.52  fof(f99,plain,(
% 31.90/4.52    k2_relset_1(sK0,sK1,sK2) = sK1),
% 31.90/4.52    inference(cnf_transformation,[],[f62])).
% 31.90/4.52  
% 31.90/4.52  fof(f13,axiom,(
% 31.90/4.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f38,plain,(
% 31.90/4.52    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.90/4.52    inference(ennf_transformation,[],[f13])).
% 31.90/4.52  
% 31.90/4.52  fof(f39,plain,(
% 31.90/4.52    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.90/4.52    inference(flattening,[],[f38])).
% 31.90/4.52  
% 31.90/4.52  fof(f79,plain,(
% 31.90/4.52    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f39])).
% 31.90/4.52  
% 31.90/4.52  fof(f101,plain,(
% 31.90/4.52    v2_funct_1(sK2)),
% 31.90/4.52    inference(cnf_transformation,[],[f62])).
% 31.90/4.52  
% 31.90/4.52  fof(f15,axiom,(
% 31.90/4.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f42,plain,(
% 31.90/4.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.90/4.52    inference(ennf_transformation,[],[f15])).
% 31.90/4.52  
% 31.90/4.52  fof(f43,plain,(
% 31.90/4.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.90/4.52    inference(flattening,[],[f42])).
% 31.90/4.52  
% 31.90/4.52  fof(f82,plain,(
% 31.90/4.52    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f43])).
% 31.90/4.52  
% 31.90/4.52  fof(f4,axiom,(
% 31.90/4.52    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f31,plain,(
% 31.90/4.52    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 31.90/4.52    inference(ennf_transformation,[],[f4])).
% 31.90/4.52  
% 31.90/4.52  fof(f69,plain,(
% 31.90/4.52    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f31])).
% 31.90/4.52  
% 31.90/4.52  fof(f7,axiom,(
% 31.90/4.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f33,plain,(
% 31.90/4.52    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.90/4.52    inference(ennf_transformation,[],[f7])).
% 31.90/4.52  
% 31.90/4.52  fof(f72,plain,(
% 31.90/4.52    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f33])).
% 31.90/4.52  
% 31.90/4.52  fof(f10,axiom,(
% 31.90/4.52    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f76,plain,(
% 31.90/4.52    ( ! [X0] : (k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f10])).
% 31.90/4.52  
% 31.90/4.52  fof(f107,plain,(
% 31.90/4.52    ( ! [X0] : (k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 31.90/4.52    inference(definition_unfolding,[],[f76,f94,f94])).
% 31.90/4.52  
% 31.90/4.52  fof(f16,axiom,(
% 31.90/4.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f44,plain,(
% 31.90/4.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.90/4.52    inference(ennf_transformation,[],[f16])).
% 31.90/4.52  
% 31.90/4.52  fof(f45,plain,(
% 31.90/4.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.90/4.52    inference(flattening,[],[f44])).
% 31.90/4.52  
% 31.90/4.52  fof(f85,plain,(
% 31.90/4.52    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f45])).
% 31.90/4.52  
% 31.90/4.52  fof(f110,plain,(
% 31.90/4.52    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.90/4.52    inference(definition_unfolding,[],[f85,f94])).
% 31.90/4.52  
% 31.90/4.52  fof(f12,axiom,(
% 31.90/4.52    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f37,plain,(
% 31.90/4.52    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 31.90/4.52    inference(ennf_transformation,[],[f12])).
% 31.90/4.52  
% 31.90/4.52  fof(f78,plain,(
% 31.90/4.52    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f37])).
% 31.90/4.52  
% 31.90/4.52  fof(f109,plain,(
% 31.90/4.52    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 31.90/4.52    inference(definition_unfolding,[],[f78,f94])).
% 31.90/4.52  
% 31.90/4.52  fof(f83,plain,(
% 31.90/4.52    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f43])).
% 31.90/4.52  
% 31.90/4.52  fof(f9,axiom,(
% 31.90/4.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f75,plain,(
% 31.90/4.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 31.90/4.52    inference(cnf_transformation,[],[f9])).
% 31.90/4.52  
% 31.90/4.52  fof(f105,plain,(
% 31.90/4.52    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 31.90/4.52    inference(definition_unfolding,[],[f75,f94])).
% 31.90/4.52  
% 31.90/4.52  fof(f1,axiom,(
% 31.90/4.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.90/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.52  
% 31.90/4.52  fof(f56,plain,(
% 31.90/4.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.90/4.52    inference(nnf_transformation,[],[f1])).
% 31.90/4.52  
% 31.90/4.52  fof(f57,plain,(
% 31.90/4.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.90/4.52    inference(flattening,[],[f56])).
% 31.90/4.52  
% 31.90/4.52  fof(f65,plain,(
% 31.90/4.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.90/4.52    inference(cnf_transformation,[],[f57])).
% 31.90/4.52  
% 31.90/4.52  fof(f104,plain,(
% 31.90/4.52    k2_funct_1(sK2) != sK3),
% 31.90/4.52    inference(cnf_transformation,[],[f62])).
% 31.90/4.52  
% 31.90/4.52  cnf(c_37,negated_conjecture,
% 31.90/4.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 31.90/4.52      inference(cnf_transformation,[],[f98]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1188,plain,
% 31.90/4.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_3,plain,
% 31.90/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.90/4.52      | ~ v1_relat_1(X1)
% 31.90/4.52      | v1_relat_1(X0) ),
% 31.90/4.52      inference(cnf_transformation,[],[f66]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1203,plain,
% 31.90/4.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.90/4.52      | v1_relat_1(X1) != iProver_top
% 31.90/4.52      | v1_relat_1(X0) = iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2848,plain,
% 31.90/4.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 31.90/4.52      | v1_relat_1(sK3) = iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_1188,c_1203]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_44,plain,
% 31.90/4.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1593,plain,
% 31.90/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.90/4.52      | v1_relat_1(X0)
% 31.90/4.52      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 31.90/4.52      inference(instantiation,[status(thm)],[c_3]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2208,plain,
% 31.90/4.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 31.90/4.52      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 31.90/4.52      | v1_relat_1(sK3) ),
% 31.90/4.52      inference(instantiation,[status(thm)],[c_1593]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2209,plain,
% 31.90/4.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.90/4.52      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 31.90/4.52      | v1_relat_1(sK3) = iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_2208]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_7,plain,
% 31.90/4.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 31.90/4.52      inference(cnf_transformation,[],[f70]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2426,plain,
% 31.90/4.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 31.90/4.52      inference(instantiation,[status(thm)],[c_7]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2427,plain,
% 31.90/4.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_2426]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2957,plain,
% 31.90/4.52      ( v1_relat_1(sK3) = iProver_top ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_2848,c_44,c_2209,c_2427]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_39,negated_conjecture,
% 31.90/4.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.90/4.52      inference(cnf_transformation,[],[f96]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1186,plain,
% 31.90/4.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2849,plain,
% 31.90/4.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 31.90/4.52      | v1_relat_1(sK2) = iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_1186,c_1203]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_42,plain,
% 31.90/4.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1265,plain,
% 31.90/4.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 31.90/4.52      | ~ v1_relat_1(X0)
% 31.90/4.52      | v1_relat_1(sK2) ),
% 31.90/4.52      inference(instantiation,[status(thm)],[c_3]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1327,plain,
% 31.90/4.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.90/4.52      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 31.90/4.52      | v1_relat_1(sK2) ),
% 31.90/4.52      inference(instantiation,[status(thm)],[c_1265]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1531,plain,
% 31.90/4.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.90/4.52      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 31.90/4.52      | v1_relat_1(sK2) ),
% 31.90/4.52      inference(instantiation,[status(thm)],[c_1327]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1532,plain,
% 31.90/4.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.90/4.52      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 31.90/4.52      | v1_relat_1(sK2) = iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_1531]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1658,plain,
% 31.90/4.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.90/4.52      inference(instantiation,[status(thm)],[c_7]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1659,plain,
% 31.90/4.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_1658]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2964,plain,
% 31.90/4.52      ( v1_relat_1(sK2) = iProver_top ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_2849,c_42,c_1532,c_1659]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_10,plain,
% 31.90/4.52      ( ~ v1_relat_1(X0)
% 31.90/4.52      | ~ v1_relat_1(X1)
% 31.90/4.52      | ~ v1_relat_1(X2)
% 31.90/4.52      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 31.90/4.52      inference(cnf_transformation,[],[f73]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1198,plain,
% 31.90/4.52      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 31.90/4.52      | v1_relat_1(X0) != iProver_top
% 31.90/4.52      | v1_relat_1(X1) != iProver_top
% 31.90/4.52      | v1_relat_1(X2) != iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_4478,plain,
% 31.90/4.52      ( k5_relat_1(sK2,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK2,X0),X1)
% 31.90/4.52      | v1_relat_1(X0) != iProver_top
% 31.90/4.52      | v1_relat_1(X1) != iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_2964,c_1198]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_7524,plain,
% 31.90/4.52      ( k5_relat_1(k5_relat_1(sK2,sK3),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0))
% 31.90/4.52      | v1_relat_1(X0) != iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_2957,c_4478]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_30,plain,
% 31.90/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.90/4.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.90/4.52      | ~ v1_funct_1(X0)
% 31.90/4.52      | ~ v1_funct_1(X3)
% 31.90/4.52      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 31.90/4.52      inference(cnf_transformation,[],[f93]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1189,plain,
% 31.90/4.52      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 31.90/4.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 31.90/4.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.90/4.52      | v1_funct_1(X5) != iProver_top
% 31.90/4.52      | v1_funct_1(X4) != iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_4707,plain,
% 31.90/4.52      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 31.90/4.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.90/4.52      | v1_funct_1(X2) != iProver_top
% 31.90/4.52      | v1_funct_1(sK3) != iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_1188,c_1189]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_38,negated_conjecture,
% 31.90/4.52      ( v1_funct_1(sK3) ),
% 31.90/4.52      inference(cnf_transformation,[],[f97]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_43,plain,
% 31.90/4.52      ( v1_funct_1(sK3) = iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_4817,plain,
% 31.90/4.52      ( v1_funct_1(X2) != iProver_top
% 31.90/4.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.90/4.52      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_4707,c_43]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_4818,plain,
% 31.90/4.52      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 31.90/4.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.90/4.52      | v1_funct_1(X2) != iProver_top ),
% 31.90/4.52      inference(renaming,[status(thm)],[c_4817]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_4826,plain,
% 31.90/4.52      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 31.90/4.52      | v1_funct_1(sK2) != iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_1186,c_4818]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_26,plain,
% 31.90/4.52      ( ~ r2_relset_1(X0,X1,X2,X3)
% 31.90/4.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.90/4.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.90/4.52      | X3 = X2 ),
% 31.90/4.52      inference(cnf_transformation,[],[f88]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_35,negated_conjecture,
% 31.90/4.52      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 31.90/4.52      inference(cnf_transformation,[],[f100]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_409,plain,
% 31.90/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.90/4.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.90/4.52      | X3 = X0
% 31.90/4.52      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 31.90/4.52      | k6_partfun1(sK0) != X3
% 31.90/4.52      | sK0 != X2
% 31.90/4.52      | sK0 != X1 ),
% 31.90/4.52      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_410,plain,
% 31.90/4.52      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.90/4.52      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.90/4.52      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.90/4.52      inference(unflattening,[status(thm)],[c_409]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_29,plain,
% 31.90/4.52      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 31.90/4.52      inference(cnf_transformation,[],[f92]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_51,plain,
% 31.90/4.52      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 31.90/4.52      inference(instantiation,[status(thm)],[c_29]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_412,plain,
% 31.90/4.52      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.90/4.52      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_410,c_51]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1183,plain,
% 31.90/4.52      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 31.90/4.52      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_40,negated_conjecture,
% 31.90/4.52      ( v1_funct_1(sK2) ),
% 31.90/4.52      inference(cnf_transformation,[],[f95]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_27,plain,
% 31.90/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.90/4.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.90/4.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.90/4.52      | ~ v1_funct_1(X0)
% 31.90/4.52      | ~ v1_funct_1(X3) ),
% 31.90/4.52      inference(cnf_transformation,[],[f91]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1257,plain,
% 31.90/4.52      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.90/4.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 31.90/4.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.90/4.52      | ~ v1_funct_1(sK3)
% 31.90/4.52      | ~ v1_funct_1(sK2) ),
% 31.90/4.52      inference(instantiation,[status(thm)],[c_27]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1839,plain,
% 31.90/4.52      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_1183,c_40,c_39,c_38,c_37,c_51,c_410,c_1257]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_4827,plain,
% 31.90/4.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 31.90/4.52      | v1_funct_1(sK2) != iProver_top ),
% 31.90/4.52      inference(light_normalisation,[status(thm)],[c_4826,c_1839]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_41,plain,
% 31.90/4.52      ( v1_funct_1(sK2) = iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_5383,plain,
% 31.90/4.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_4827,c_41]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_7526,plain,
% 31.90/4.52      ( k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0)
% 31.90/4.52      | v1_relat_1(X0) != iProver_top ),
% 31.90/4.52      inference(light_normalisation,[status(thm)],[c_7524,c_5383]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_15574,plain,
% 31.90/4.52      ( k5_relat_1(sK2,k5_relat_1(sK3,sK2)) = k5_relat_1(k6_partfun1(sK0),sK2) ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_2964,c_7526]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_23,plain,
% 31.90/4.52      ( v4_relat_1(X0,X1)
% 31.90/4.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 31.90/4.52      inference(cnf_transformation,[],[f86]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_5,plain,
% 31.90/4.52      ( ~ v4_relat_1(X0,X1)
% 31.90/4.52      | r1_tarski(k1_relat_1(X0),X1)
% 31.90/4.52      | ~ v1_relat_1(X0) ),
% 31.90/4.52      inference(cnf_transformation,[],[f67]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_388,plain,
% 31.90/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.90/4.52      | r1_tarski(k1_relat_1(X0),X1)
% 31.90/4.52      | ~ v1_relat_1(X0) ),
% 31.90/4.52      inference(resolution,[status(thm)],[c_23,c_5]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1184,plain,
% 31.90/4.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.90/4.52      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 31.90/4.52      | v1_relat_1(X0) != iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1971,plain,
% 31.90/4.52      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 31.90/4.52      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_1186,c_1184]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2420,plain,
% 31.90/4.52      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_1971,c_42,c_1532,c_1659]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_14,plain,
% 31.90/4.52      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 31.90/4.52      | ~ v1_relat_1(X0)
% 31.90/4.52      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 31.90/4.52      inference(cnf_transformation,[],[f108]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1197,plain,
% 31.90/4.52      ( k5_relat_1(k6_partfun1(X0),X1) = X1
% 31.90/4.52      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 31.90/4.52      | v1_relat_1(X1) != iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_3366,plain,
% 31.90/4.52      ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2
% 31.90/4.52      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_2420,c_1197]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1974,plain,
% 31.90/4.52      ( r1_tarski(k1_relat_1(sK2),sK0) | ~ v1_relat_1(sK2) ),
% 31.90/4.52      inference(predicate_to_equality_rev,[status(thm)],[c_1971]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2708,plain,
% 31.90/4.52      ( ~ r1_tarski(k1_relat_1(sK2),X0)
% 31.90/4.52      | ~ v1_relat_1(sK2)
% 31.90/4.52      | k5_relat_1(k6_partfun1(X0),sK2) = sK2 ),
% 31.90/4.52      inference(instantiation,[status(thm)],[c_14]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2710,plain,
% 31.90/4.52      ( ~ r1_tarski(k1_relat_1(sK2),sK0)
% 31.90/4.52      | ~ v1_relat_1(sK2)
% 31.90/4.52      | k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
% 31.90/4.52      inference(instantiation,[status(thm)],[c_2708]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_4081,plain,
% 31.90/4.52      ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_3366,c_39,c_1531,c_1658,c_1974,c_2710]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_15583,plain,
% 31.90/4.52      ( k5_relat_1(sK2,k5_relat_1(sK3,sK2)) = sK2 ),
% 31.90/4.52      inference(light_normalisation,[status(thm)],[c_15574,c_4081]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_8,plain,
% 31.90/4.52      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 31.90/4.52      | ~ v1_relat_1(X0)
% 31.90/4.52      | ~ v1_relat_1(X1) ),
% 31.90/4.52      inference(cnf_transformation,[],[f71]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1200,plain,
% 31.90/4.52      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 31.90/4.52      | v1_relat_1(X0) != iProver_top
% 31.90/4.52      | v1_relat_1(X1) != iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_16070,plain,
% 31.90/4.52      ( r1_tarski(k2_relat_1(sK2),k2_relat_1(k5_relat_1(sK3,sK2))) = iProver_top
% 31.90/4.52      | v1_relat_1(k5_relat_1(sK3,sK2)) != iProver_top
% 31.90/4.52      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_15583,c_1200]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_24,plain,
% 31.90/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.90/4.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 31.90/4.52      inference(cnf_transformation,[],[f87]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1193,plain,
% 31.90/4.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 31.90/4.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2018,plain,
% 31.90/4.52      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_1186,c_1193]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_36,negated_conjecture,
% 31.90/4.52      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 31.90/4.52      inference(cnf_transformation,[],[f99]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2019,plain,
% 31.90/4.52      ( k2_relat_1(sK2) = sK1 ),
% 31.90/4.52      inference(light_normalisation,[status(thm)],[c_2018,c_36]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_16071,plain,
% 31.90/4.52      ( r1_tarski(sK1,k2_relat_1(k5_relat_1(sK3,sK2))) = iProver_top
% 31.90/4.52      | v1_relat_1(k5_relat_1(sK3,sK2)) != iProver_top
% 31.90/4.52      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.52      inference(light_normalisation,[status(thm)],[c_16070,c_2019]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1201,plain,
% 31.90/4.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_4708,plain,
% 31.90/4.52      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 31.90/4.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.90/4.52      | v1_funct_1(X2) != iProver_top
% 31.90/4.52      | v1_funct_1(sK2) != iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_1186,c_1189]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_5085,plain,
% 31.90/4.52      ( v1_funct_1(X2) != iProver_top
% 31.90/4.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.90/4.52      | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_4708,c_41]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_5086,plain,
% 31.90/4.52      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 31.90/4.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.90/4.52      | v1_funct_1(X2) != iProver_top ),
% 31.90/4.52      inference(renaming,[status(thm)],[c_5085]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_5093,plain,
% 31.90/4.52      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
% 31.90/4.52      | v1_funct_1(sK3) != iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_1188,c_5086]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_5104,plain,
% 31.90/4.52      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_5093,c_43]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1192,plain,
% 31.90/4.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.90/4.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 31.90/4.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 31.90/4.52      | v1_funct_1(X0) != iProver_top
% 31.90/4.52      | v1_funct_1(X3) != iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_5106,plain,
% 31.90/4.52      ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 31.90/4.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.90/4.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.90/4.52      | v1_funct_1(sK3) != iProver_top
% 31.90/4.52      | v1_funct_1(sK2) != iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_5104,c_1192]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_10060,plain,
% 31.90/4.52      ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_5106,c_41,c_42,c_43,c_44]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_10064,plain,
% 31.90/4.52      ( v1_relat_1(k5_relat_1(sK3,sK2)) = iProver_top
% 31.90/4.52      | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_10060,c_1203]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_10444,plain,
% 31.90/4.52      ( v1_relat_1(k5_relat_1(sK3,sK2)) = iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_1201,c_10064]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_16074,plain,
% 31.90/4.52      ( r1_tarski(sK1,k2_relat_1(k5_relat_1(sK3,sK2))) = iProver_top ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_16071,c_42,c_1532,c_1659,c_10444]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_16,plain,
% 31.90/4.52      ( ~ v1_funct_1(X0)
% 31.90/4.52      | ~ v2_funct_1(X0)
% 31.90/4.52      | ~ v1_relat_1(X0)
% 31.90/4.52      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 31.90/4.52      inference(cnf_transformation,[],[f79]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_34,negated_conjecture,
% 31.90/4.52      ( v2_funct_1(sK2) ),
% 31.90/4.52      inference(cnf_transformation,[],[f101]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_482,plain,
% 31.90/4.52      ( ~ v1_funct_1(X0)
% 31.90/4.52      | ~ v1_relat_1(X0)
% 31.90/4.52      | k2_funct_1(X0) = k4_relat_1(X0)
% 31.90/4.52      | sK2 != X0 ),
% 31.90/4.52      inference(resolution_lifted,[status(thm)],[c_16,c_34]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_483,plain,
% 31.90/4.52      ( ~ v1_funct_1(sK2)
% 31.90/4.52      | ~ v1_relat_1(sK2)
% 31.90/4.52      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 31.90/4.52      inference(unflattening,[status(thm)],[c_482]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_485,plain,
% 31.90/4.52      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_483,c_40]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1178,plain,
% 31.90/4.52      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 31.90/4.52      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2971,plain,
% 31.90/4.52      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_2964,c_1178]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_20,plain,
% 31.90/4.52      ( ~ v1_funct_1(X0)
% 31.90/4.52      | ~ v2_funct_1(X0)
% 31.90/4.52      | ~ v1_relat_1(X0)
% 31.90/4.52      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 31.90/4.52      inference(cnf_transformation,[],[f82]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_454,plain,
% 31.90/4.52      ( ~ v1_funct_1(X0)
% 31.90/4.52      | ~ v1_relat_1(X0)
% 31.90/4.52      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 31.90/4.52      | sK2 != X0 ),
% 31.90/4.52      inference(resolution_lifted,[status(thm)],[c_20,c_34]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_455,plain,
% 31.90/4.52      ( ~ v1_funct_1(sK2)
% 31.90/4.52      | ~ v1_relat_1(sK2)
% 31.90/4.52      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 31.90/4.52      inference(unflattening,[status(thm)],[c_454]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_457,plain,
% 31.90/4.52      ( ~ v1_relat_1(sK2)
% 31.90/4.52      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_455,c_40]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1180,plain,
% 31.90/4.52      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 31.90/4.52      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1695,plain,
% 31.90/4.52      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_1180,c_40,c_39,c_455,c_1531,c_1658]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2159,plain,
% 31.90/4.52      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 31.90/4.52      inference(demodulation,[status(thm)],[c_2019,c_1695]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_3028,plain,
% 31.90/4.52      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 31.90/4.52      inference(demodulation,[status(thm)],[c_2971,c_2159]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_3368,plain,
% 31.90/4.52      ( k5_relat_1(k6_partfun1(X0),k4_relat_1(sK2)) = k4_relat_1(sK2)
% 31.90/4.52      | r1_tarski(sK1,X0) != iProver_top
% 31.90/4.52      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_3028,c_1197]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_6,plain,
% 31.90/4.52      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 31.90/4.52      inference(cnf_transformation,[],[f69]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1821,plain,
% 31.90/4.52      ( v1_relat_1(k4_relat_1(sK2)) | ~ v1_relat_1(sK2) ),
% 31.90/4.52      inference(instantiation,[status(thm)],[c_6]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1824,plain,
% 31.90/4.52      ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 31.90/4.52      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_1821]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_15202,plain,
% 31.90/4.52      ( r1_tarski(sK1,X0) != iProver_top
% 31.90/4.52      | k5_relat_1(k6_partfun1(X0),k4_relat_1(sK2)) = k4_relat_1(sK2) ),
% 31.90/4.52      inference(global_propositional_subsumption,
% 31.90/4.52                [status(thm)],
% 31.90/4.52                [c_3368,c_42,c_1532,c_1659,c_1824]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_15203,plain,
% 31.90/4.52      ( k5_relat_1(k6_partfun1(X0),k4_relat_1(sK2)) = k4_relat_1(sK2)
% 31.90/4.52      | r1_tarski(sK1,X0) != iProver_top ),
% 31.90/4.52      inference(renaming,[status(thm)],[c_15202]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_1190,plain,
% 31.90/4.52      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 31.90/4.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_2847,plain,
% 31.90/4.52      ( v1_relat_1(k2_zfmisc_1(X0,X0)) != iProver_top
% 31.90/4.52      | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_1190,c_1203]) ).
% 31.90/4.52  
% 31.90/4.52  cnf(c_4722,plain,
% 31.90/4.52      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 31.90/4.52      inference(superposition,[status(thm)],[c_1201,c_2847]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_9,plain,
% 31.90/4.53      ( ~ v1_relat_1(X0)
% 31.90/4.53      | ~ v1_relat_1(X1)
% 31.90/4.53      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 31.90/4.53      inference(cnf_transformation,[],[f72]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_1199,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 31.90/4.53      | v1_relat_1(X1) != iProver_top
% 31.90/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.90/4.53      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_5812,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(k6_partfun1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_partfun1(X0)))
% 31.90/4.53      | v1_relat_1(X1) != iProver_top ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_4722,c_1199]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_13,plain,
% 31.90/4.53      ( k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 31.90/4.53      inference(cnf_transformation,[],[f107]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_5817,plain,
% 31.90/4.53      ( k5_relat_1(k6_partfun1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_partfun1(X0)))
% 31.90/4.53      | v1_relat_1(X1) != iProver_top ),
% 31.90/4.53      inference(light_normalisation,[status(thm)],[c_5812,c_13]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_6810,plain,
% 31.90/4.53      ( k5_relat_1(k6_partfun1(X0),k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_2964,c_5817]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_15208,plain,
% 31.90/4.53      ( k4_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) = k4_relat_1(sK2)
% 31.90/4.53      | r1_tarski(sK1,X0) != iProver_top ),
% 31.90/4.53      inference(demodulation,[status(thm)],[c_15203,c_6810]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_16080,plain,
% 31.90/4.53      ( k4_relat_1(k5_relat_1(sK2,k6_partfun1(k2_relat_1(k5_relat_1(sK3,sK2))))) = k4_relat_1(sK2) ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_16074,c_15208]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_1202,plain,
% 31.90/4.53      ( v1_relat_1(X0) != iProver_top
% 31.90/4.53      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 31.90/4.53      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_16252,plain,
% 31.90/4.53      ( v1_relat_1(k5_relat_1(sK2,k6_partfun1(k2_relat_1(k5_relat_1(sK3,sK2))))) != iProver_top
% 31.90/4.53      | v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_16080,c_1202]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_16499,plain,
% 31.90/4.53      ( v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
% 31.90/4.53      inference(global_propositional_subsumption,
% 31.90/4.53                [status(thm)],
% 31.90/4.53                [c_16252,c_42,c_1532,c_1659,c_1824]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_16513,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1)
% 31.90/4.53      | v1_relat_1(X0) != iProver_top
% 31.90/4.53      | v1_relat_1(X1) != iProver_top ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_16499,c_1198]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_119851,plain,
% 31.90/4.53      ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),X0) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0))
% 31.90/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_2964,c_16513]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_21,plain,
% 31.90/4.53      ( ~ v1_funct_1(X0)
% 31.90/4.53      | ~ v2_funct_1(X0)
% 31.90/4.53      | ~ v1_relat_1(X0)
% 31.90/4.53      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 31.90/4.53      inference(cnf_transformation,[],[f110]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_440,plain,
% 31.90/4.53      ( ~ v1_funct_1(X0)
% 31.90/4.53      | ~ v1_relat_1(X0)
% 31.90/4.53      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 31.90/4.53      | sK2 != X0 ),
% 31.90/4.53      inference(resolution_lifted,[status(thm)],[c_21,c_34]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_441,plain,
% 31.90/4.53      ( ~ v1_funct_1(sK2)
% 31.90/4.53      | ~ v1_relat_1(sK2)
% 31.90/4.53      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 31.90/4.53      inference(unflattening,[status(thm)],[c_440]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_443,plain,
% 31.90/4.53      ( ~ v1_relat_1(sK2)
% 31.90/4.53      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 31.90/4.53      inference(global_propositional_subsumption,
% 31.90/4.53                [status(thm)],
% 31.90/4.53                [c_441,c_40]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_1181,plain,
% 31.90/4.53      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 31.90/4.53      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.53      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_1698,plain,
% 31.90/4.53      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 31.90/4.53      inference(global_propositional_subsumption,
% 31.90/4.53                [status(thm)],
% 31.90/4.53                [c_1181,c_40,c_39,c_441,c_1531,c_1658]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_2158,plain,
% 31.90/4.53      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 31.90/4.53      inference(demodulation,[status(thm)],[c_2019,c_1698]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_3027,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
% 31.90/4.53      inference(demodulation,[status(thm)],[c_2971,c_2158]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_119874,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 31.90/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.90/4.53      inference(light_normalisation,[status(thm)],[c_119851,c_3027]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_120823,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_2957,c_119874]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_1970,plain,
% 31.90/4.53      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
% 31.90/4.53      | v1_relat_1(sK3) != iProver_top ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_1188,c_1184]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_3365,plain,
% 31.90/4.53      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
% 31.90/4.53      | v1_relat_1(sK3) != iProver_top ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_1970,c_1197]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_3766,plain,
% 31.90/4.53      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 31.90/4.53      inference(global_propositional_subsumption,
% 31.90/4.53                [status(thm)],
% 31.90/4.53                [c_3365,c_44,c_2209,c_2427]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_15,plain,
% 31.90/4.53      ( ~ v1_relat_1(X0)
% 31.90/4.53      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 31.90/4.53      inference(cnf_transformation,[],[f109]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_1196,plain,
% 31.90/4.53      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 31.90/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.90/4.53      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_2009,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(X0),k6_partfun1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
% 31.90/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_1202,c_1196]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_2968,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2)))) = k4_relat_1(sK2) ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_2964,c_2009]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_19,plain,
% 31.90/4.53      ( ~ v1_funct_1(X0)
% 31.90/4.53      | ~ v2_funct_1(X0)
% 31.90/4.53      | ~ v1_relat_1(X0)
% 31.90/4.53      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 31.90/4.53      inference(cnf_transformation,[],[f83]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_468,plain,
% 31.90/4.53      ( ~ v1_funct_1(X0)
% 31.90/4.53      | ~ v1_relat_1(X0)
% 31.90/4.53      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 31.90/4.53      | sK2 != X0 ),
% 31.90/4.53      inference(resolution_lifted,[status(thm)],[c_19,c_34]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_469,plain,
% 31.90/4.53      ( ~ v1_funct_1(sK2)
% 31.90/4.53      | ~ v1_relat_1(sK2)
% 31.90/4.53      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 31.90/4.53      inference(unflattening,[status(thm)],[c_468]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_471,plain,
% 31.90/4.53      ( ~ v1_relat_1(sK2)
% 31.90/4.53      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 31.90/4.53      inference(global_propositional_subsumption,
% 31.90/4.53                [status(thm)],
% 31.90/4.53                [c_469,c_40]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_1179,plain,
% 31.90/4.53      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 31.90/4.53      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.53      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_2970,plain,
% 31.90/4.53      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_2964,c_1179]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_2972,plain,
% 31.90/4.53      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 31.90/4.53      inference(demodulation,[status(thm)],[c_2970,c_2971]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_2974,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k4_relat_1(sK2) ),
% 31.90/4.53      inference(demodulation,[status(thm)],[c_2968,c_2972]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_3482,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK3))
% 31.90/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_2957,c_1199]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_6361,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(sK2,sK3)) ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_2964,c_3482]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_6365,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0)) ),
% 31.90/4.53      inference(light_normalisation,[status(thm)],[c_6361,c_5383]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_6366,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k6_partfun1(sK0) ),
% 31.90/4.53      inference(demodulation,[status(thm)],[c_6365,c_13]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_6756,plain,
% 31.90/4.53      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k4_relat_1(sK2))) = iProver_top
% 31.90/4.53      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 31.90/4.53      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_6366,c_1200]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_6757,plain,
% 31.90/4.53      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
% 31.90/4.53      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 31.90/4.53      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 31.90/4.53      inference(light_normalisation,[status(thm)],[c_6756,c_2972]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_11,plain,
% 31.90/4.53      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 31.90/4.53      inference(cnf_transformation,[],[f105]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_6758,plain,
% 31.90/4.53      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 31.90/4.53      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 31.90/4.53      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 31.90/4.53      inference(demodulation,[status(thm)],[c_6757,c_11]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_2561,plain,
% 31.90/4.53      ( v1_relat_1(k4_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 31.90/4.53      inference(instantiation,[status(thm)],[c_6]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_2568,plain,
% 31.90/4.53      ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 31.90/4.53      | v1_relat_1(sK3) != iProver_top ),
% 31.90/4.53      inference(predicate_to_equality,[status(thm)],[c_2561]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_7798,plain,
% 31.90/4.53      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 31.90/4.53      inference(global_propositional_subsumption,
% 31.90/4.53                [status(thm)],
% 31.90/4.53                [c_6758,c_42,c_44,c_1532,c_1659,c_1824,c_2209,c_2427,
% 31.90/4.53                 c_2568]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_0,plain,
% 31.90/4.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 31.90/4.53      inference(cnf_transformation,[],[f65]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_1205,plain,
% 31.90/4.53      ( X0 = X1
% 31.90/4.53      | r1_tarski(X0,X1) != iProver_top
% 31.90/4.53      | r1_tarski(X1,X0) != iProver_top ),
% 31.90/4.53      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_2843,plain,
% 31.90/4.53      ( k1_relat_1(sK2) = sK0
% 31.90/4.53      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_2420,c_1205]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_7804,plain,
% 31.90/4.53      ( k1_relat_1(sK2) = sK0 ),
% 31.90/4.53      inference(superposition,[status(thm)],[c_7798,c_2843]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_10228,plain,
% 31.90/4.53      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k4_relat_1(sK2) ),
% 31.90/4.53      inference(light_normalisation,[status(thm)],[c_2974,c_2974,c_7804]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_120851,plain,
% 31.90/4.53      ( k4_relat_1(sK2) = sK3 ),
% 31.90/4.53      inference(light_normalisation,
% 31.90/4.53                [status(thm)],
% 31.90/4.53                [c_120823,c_3766,c_5383,c_10228]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_31,negated_conjecture,
% 31.90/4.53      ( k2_funct_1(sK2) != sK3 ),
% 31.90/4.53      inference(cnf_transformation,[],[f104]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(c_3031,plain,
% 31.90/4.53      ( k4_relat_1(sK2) != sK3 ),
% 31.90/4.53      inference(demodulation,[status(thm)],[c_2971,c_31]) ).
% 31.90/4.53  
% 31.90/4.53  cnf(contradiction,plain,
% 31.90/4.53      ( $false ),
% 31.90/4.53      inference(minisat,[status(thm)],[c_120851,c_3031]) ).
% 31.90/4.53  
% 31.90/4.53  
% 31.90/4.53  % SZS output end CNFRefutation for theBenchmark.p
% 31.90/4.53  
% 31.90/4.53  ------                               Statistics
% 31.90/4.53  
% 31.90/4.53  ------ General
% 31.90/4.53  
% 31.90/4.53  abstr_ref_over_cycles:                  0
% 31.90/4.53  abstr_ref_under_cycles:                 0
% 31.90/4.53  gc_basic_clause_elim:                   0
% 31.90/4.53  forced_gc_time:                         0
% 31.90/4.53  parsing_time:                           0.008
% 31.90/4.53  unif_index_cands_time:                  0.
% 31.90/4.53  unif_index_add_time:                    0.
% 31.90/4.53  orderings_time:                         0.
% 31.90/4.53  out_proof_time:                         0.027
% 31.90/4.53  total_time:                             3.955
% 31.90/4.53  num_of_symbols:                         53
% 31.90/4.53  num_of_terms:                           108279
% 31.90/4.53  
% 31.90/4.53  ------ Preprocessing
% 31.90/4.53  
% 31.90/4.53  num_of_splits:                          0
% 31.90/4.53  num_of_split_atoms:                     0
% 31.90/4.53  num_of_reused_defs:                     0
% 31.90/4.53  num_eq_ax_congr_red:                    2
% 31.90/4.53  num_of_sem_filtered_clauses:            1
% 31.90/4.53  num_of_subtypes:                        0
% 31.90/4.53  monotx_restored_types:                  0
% 31.90/4.53  sat_num_of_epr_types:                   0
% 31.90/4.53  sat_num_of_non_cyclic_types:            0
% 31.90/4.53  sat_guarded_non_collapsed_types:        0
% 31.90/4.53  num_pure_diseq_elim:                    0
% 31.90/4.53  simp_replaced_by:                       0
% 31.90/4.53  res_preprocessed:                       178
% 31.90/4.53  prep_upred:                             0
% 31.90/4.53  prep_unflattend:                        13
% 31.90/4.53  smt_new_axioms:                         0
% 31.90/4.53  pred_elim_cands:                        4
% 31.90/4.53  pred_elim:                              3
% 31.90/4.53  pred_elim_cl:                           5
% 31.90/4.53  pred_elim_cycles:                       5
% 31.90/4.53  merged_defs:                            0
% 31.90/4.53  merged_defs_ncl:                        0
% 31.90/4.53  bin_hyper_res:                          0
% 31.90/4.53  prep_cycles:                            4
% 31.90/4.53  pred_elim_time:                         0.005
% 31.90/4.53  splitting_time:                         0.
% 31.90/4.53  sem_filter_time:                        0.
% 31.90/4.53  monotx_time:                            0.
% 31.90/4.53  subtype_inf_time:                       0.
% 31.90/4.53  
% 31.90/4.53  ------ Problem properties
% 31.90/4.53  
% 31.90/4.53  clauses:                                35
% 31.90/4.53  conjectures:                            8
% 31.90/4.53  epr:                                    6
% 31.90/4.53  horn:                                   35
% 31.90/4.53  ground:                                 14
% 31.90/4.53  unary:                                  14
% 31.90/4.53  binary:                                 9
% 31.90/4.53  lits:                                   75
% 31.90/4.53  lits_eq:                                20
% 31.90/4.53  fd_pure:                                0
% 31.90/4.53  fd_pseudo:                              0
% 31.90/4.53  fd_cond:                                0
% 31.90/4.53  fd_pseudo_cond:                         1
% 31.90/4.53  ac_symbols:                             0
% 31.90/4.53  
% 31.90/4.53  ------ Propositional Solver
% 31.90/4.53  
% 31.90/4.53  prop_solver_calls:                      52
% 31.90/4.53  prop_fast_solver_calls:                 4534
% 31.90/4.53  smt_solver_calls:                       0
% 31.90/4.53  smt_fast_solver_calls:                  0
% 31.90/4.53  prop_num_of_clauses:                    51853
% 31.90/4.53  prop_preprocess_simplified:             90483
% 31.90/4.53  prop_fo_subsumed:                       889
% 31.90/4.53  prop_solver_time:                       0.
% 31.90/4.53  smt_solver_time:                        0.
% 31.90/4.53  smt_fast_solver_time:                   0.
% 31.90/4.53  prop_fast_solver_time:                  0.
% 31.90/4.53  prop_unsat_core_time:                   0.007
% 31.90/4.53  
% 31.90/4.53  ------ QBF
% 31.90/4.53  
% 31.90/4.53  qbf_q_res:                              0
% 31.90/4.53  qbf_num_tautologies:                    0
% 31.90/4.53  qbf_prep_cycles:                        0
% 31.90/4.53  
% 31.90/4.53  ------ BMC1
% 31.90/4.53  
% 31.90/4.53  bmc1_current_bound:                     -1
% 31.90/4.53  bmc1_last_solved_bound:                 -1
% 31.90/4.53  bmc1_unsat_core_size:                   -1
% 31.90/4.53  bmc1_unsat_core_parents_size:           -1
% 31.90/4.53  bmc1_merge_next_fun:                    0
% 31.90/4.53  bmc1_unsat_core_clauses_time:           0.
% 31.90/4.53  
% 31.90/4.53  ------ Instantiation
% 31.90/4.53  
% 31.90/4.53  inst_num_of_clauses:                    11941
% 31.90/4.53  inst_num_in_passive:                    5007
% 31.90/4.53  inst_num_in_active:                     6378
% 31.90/4.53  inst_num_in_unprocessed:                3330
% 31.90/4.53  inst_num_of_loops:                      7109
% 31.90/4.53  inst_num_of_learning_restarts:          1
% 31.90/4.53  inst_num_moves_active_passive:          724
% 31.90/4.53  inst_lit_activity:                      0
% 31.90/4.53  inst_lit_activity_moves:                5
% 31.90/4.53  inst_num_tautologies:                   0
% 31.90/4.53  inst_num_prop_implied:                  0
% 31.90/4.53  inst_num_existing_simplified:           0
% 31.90/4.53  inst_num_eq_res_simplified:             0
% 31.90/4.53  inst_num_child_elim:                    0
% 31.90/4.53  inst_num_of_dismatching_blockings:      10846
% 31.90/4.53  inst_num_of_non_proper_insts:           18470
% 31.90/4.53  inst_num_of_duplicates:                 0
% 31.90/4.53  inst_inst_num_from_inst_to_res:         0
% 31.90/4.53  inst_dismatching_checking_time:         0.
% 31.90/4.53  
% 31.90/4.53  ------ Resolution
% 31.90/4.53  
% 31.90/4.53  res_num_of_clauses:                     51
% 31.90/4.53  res_num_in_passive:                     51
% 31.90/4.53  res_num_in_active:                      0
% 31.90/4.53  res_num_of_loops:                       182
% 31.90/4.53  res_forward_subset_subsumed:            1212
% 31.90/4.53  res_backward_subset_subsumed:           0
% 31.90/4.53  res_forward_subsumed:                   0
% 31.90/4.53  res_backward_subsumed:                  0
% 31.90/4.53  res_forward_subsumption_resolution:     0
% 31.90/4.53  res_backward_subsumption_resolution:    0
% 31.90/4.53  res_clause_to_clause_subsumption:       16001
% 31.90/4.53  res_orphan_elimination:                 0
% 31.90/4.53  res_tautology_del:                      1323
% 31.90/4.53  res_num_eq_res_simplified:              0
% 31.90/4.53  res_num_sel_changes:                    0
% 31.90/4.53  res_moves_from_active_to_pass:          0
% 31.90/4.53  
% 31.90/4.53  ------ Superposition
% 31.90/4.53  
% 31.90/4.53  sup_time_total:                         0.
% 31.90/4.53  sup_time_generating:                    0.
% 31.90/4.53  sup_time_sim_full:                      0.
% 31.90/4.53  sup_time_sim_immed:                     0.
% 31.90/4.53  
% 31.90/4.53  sup_num_of_clauses:                     5629
% 31.90/4.53  sup_num_in_active:                      922
% 31.90/4.53  sup_num_in_passive:                     4707
% 31.90/4.53  sup_num_of_loops:                       1420
% 31.90/4.53  sup_fw_superposition:                   4657
% 31.90/4.53  sup_bw_superposition:                   3109
% 31.90/4.53  sup_immediate_simplified:               3074
% 31.90/4.53  sup_given_eliminated:                   16
% 31.90/4.53  comparisons_done:                       0
% 31.90/4.53  comparisons_avoided:                    0
% 31.90/4.53  
% 31.90/4.53  ------ Simplifications
% 31.90/4.53  
% 31.90/4.53  
% 31.90/4.53  sim_fw_subset_subsumed:                 147
% 31.90/4.53  sim_bw_subset_subsumed:                 318
% 31.90/4.53  sim_fw_subsumed:                        291
% 31.90/4.53  sim_bw_subsumed:                        16
% 31.90/4.53  sim_fw_subsumption_res:                 0
% 31.90/4.53  sim_bw_subsumption_res:                 0
% 31.90/4.53  sim_tautology_del:                      21
% 31.90/4.53  sim_eq_tautology_del:                   595
% 31.90/4.53  sim_eq_res_simp:                        0
% 31.90/4.53  sim_fw_demodulated:                     837
% 31.90/4.53  sim_bw_demodulated:                     430
% 31.90/4.53  sim_light_normalised:                   2622
% 31.90/4.53  sim_joinable_taut:                      0
% 31.90/4.53  sim_joinable_simp:                      0
% 31.90/4.53  sim_ac_normalised:                      0
% 31.90/4.53  sim_smt_subsumption:                    0
% 31.90/4.53  
%------------------------------------------------------------------------------
