%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:00 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  202 (2567 expanded)
%              Number of clauses        :  117 ( 743 expanded)
%              Number of leaves         :   22 ( 645 expanded)
%              Depth                    :   21
%              Number of atoms          :  746 (21212 expanded)
%              Number of equality atoms :  329 (7512 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

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
    inference(ennf_transformation,[],[f21])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f53,plain,(
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

fof(f52,plain,
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

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f53,f52])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f67,f78])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f54])).

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

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f94,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f63,f78])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f93,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f60,f78])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f68,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1188,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1191,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1193,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4047,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1193])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4603,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4047,c_39])).

cnf(c_4604,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4603])).

cnf(c_4614,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_4604])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1936,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1621])).

cnf(c_2264,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1936])).

cnf(c_3473,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2264])).

cnf(c_4684,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4614,c_35,c_33,c_32,c_30,c_3473])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_28,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_457,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_21,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_51,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_459,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_51])).

cnf(c_1182,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_4687,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4684,c_1182])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5002,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4684,c_1196])).

cnf(c_5979,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4687,c_36,c_38,c_39,c_41,c_5002])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1200,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5996,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5979,c_1200])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1197,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2228,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1188,c_1197])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2230,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2228,c_29])).

cnf(c_2227,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1191,c_1197])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_470,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_471,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_551,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_471])).

cnf(c_1181,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_551])).

cnf(c_1650,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1181])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_37,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_40,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2009,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1650,c_36,c_37,c_38,c_39,c_40,c_41])).

cnf(c_2233,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2227,c_2009])).

cnf(c_5997,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5996,c_2230,c_2233])).

cnf(c_5998,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5997])).

cnf(c_7,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_90,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_92,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1457,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1458,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1457])).

cnf(c_1460,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1461,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_1198,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2083,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1198])).

cnf(c_2084,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1198])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1205,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3672,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2084,c_1205])).

cnf(c_5774,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2083,c_3672])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_346,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k9_relat_1(X2,k10_relat_1(X2,X3)) = X3
    | k2_relat_1(X2) != X1
    | k1_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_347,plain,
    ( ~ v4_relat_1(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,k1_relat_1(X0))) = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | X4 != X0
    | k9_relat_1(X3,k10_relat_1(X3,k1_relat_1(X4))) = k1_relat_1(X4)
    | k2_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_347])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,k1_relat_1(X0))) = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,k1_relat_1(X0))) = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_391,c_14])).

cnf(c_1184,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(X1))) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_3587,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2230,c_1184])).

cnf(c_3938,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3587,c_36,c_38,c_1461])).

cnf(c_3947,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1191,c_3938])).

cnf(c_5785,plain,
    ( k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_5774,c_3947])).

cnf(c_5982,plain,
    ( k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_5979,c_5785])).

cnf(c_6,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_15,c_4])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_15,c_14,c_4])).

cnf(c_1185,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_3436,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_1188,c_1185])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1206,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2460,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2084,c_1206])).

cnf(c_3486,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3436,c_2460])).

cnf(c_3487,plain,
    ( k9_relat_1(sK2,sK0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3486,c_2230])).

cnf(c_5991,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_5982,c_6,c_3487])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1202,plain,
    ( k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4449,plain,
    ( k1_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2230,c_1202])).

cnf(c_4930,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | k1_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4449,c_36,c_38,c_1461])).

cnf(c_4931,plain,
    ( k1_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4930])).

cnf(c_6631,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5991,c_4931])).

cnf(c_6636,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6631,c_5979])).

cnf(c_8422,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5998,c_36,c_38,c_39,c_41,c_92,c_1458,c_1461,c_5991,c_6636])).

cnf(c_1189,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1199,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3728,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1189,c_1199])).

cnf(c_1495,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1496,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1495])).

cnf(c_3800,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3728,c_39,c_41,c_1458,c_1496])).

cnf(c_3801,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3800])).

cnf(c_8425,plain,
    ( k2_funct_1(sK2) = sK3
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8422,c_3801])).

cnf(c_24,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f91])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8425,c_6636,c_1458,c_92,c_24,c_41,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.19/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.04  
% 3.19/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.19/1.04  
% 3.19/1.04  ------  iProver source info
% 3.19/1.04  
% 3.19/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.19/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.19/1.04  git: non_committed_changes: false
% 3.19/1.04  git: last_make_outside_of_git: false
% 3.19/1.04  
% 3.19/1.04  ------ 
% 3.19/1.04  
% 3.19/1.04  ------ Input Options
% 3.19/1.04  
% 3.19/1.04  --out_options                           all
% 3.19/1.04  --tptp_safe_out                         true
% 3.19/1.04  --problem_path                          ""
% 3.19/1.04  --include_path                          ""
% 3.19/1.04  --clausifier                            res/vclausify_rel
% 3.19/1.04  --clausifier_options                    --mode clausify
% 3.19/1.04  --stdin                                 false
% 3.19/1.04  --stats_out                             all
% 3.19/1.04  
% 3.19/1.04  ------ General Options
% 3.19/1.04  
% 3.19/1.04  --fof                                   false
% 3.19/1.04  --time_out_real                         305.
% 3.19/1.04  --time_out_virtual                      -1.
% 3.19/1.04  --symbol_type_check                     false
% 3.19/1.04  --clausify_out                          false
% 3.19/1.04  --sig_cnt_out                           false
% 3.19/1.04  --trig_cnt_out                          false
% 3.19/1.04  --trig_cnt_out_tolerance                1.
% 3.19/1.04  --trig_cnt_out_sk_spl                   false
% 3.19/1.04  --abstr_cl_out                          false
% 3.19/1.04  
% 3.19/1.04  ------ Global Options
% 3.19/1.04  
% 3.19/1.04  --schedule                              default
% 3.19/1.04  --add_important_lit                     false
% 3.19/1.04  --prop_solver_per_cl                    1000
% 3.19/1.04  --min_unsat_core                        false
% 3.19/1.04  --soft_assumptions                      false
% 3.19/1.04  --soft_lemma_size                       3
% 3.19/1.04  --prop_impl_unit_size                   0
% 3.19/1.04  --prop_impl_unit                        []
% 3.19/1.04  --share_sel_clauses                     true
% 3.19/1.04  --reset_solvers                         false
% 3.19/1.04  --bc_imp_inh                            [conj_cone]
% 3.19/1.04  --conj_cone_tolerance                   3.
% 3.19/1.04  --extra_neg_conj                        none
% 3.19/1.04  --large_theory_mode                     true
% 3.19/1.04  --prolific_symb_bound                   200
% 3.19/1.04  --lt_threshold                          2000
% 3.19/1.04  --clause_weak_htbl                      true
% 3.19/1.04  --gc_record_bc_elim                     false
% 3.19/1.04  
% 3.19/1.04  ------ Preprocessing Options
% 3.19/1.04  
% 3.19/1.04  --preprocessing_flag                    true
% 3.19/1.04  --time_out_prep_mult                    0.1
% 3.19/1.04  --splitting_mode                        input
% 3.19/1.04  --splitting_grd                         true
% 3.19/1.04  --splitting_cvd                         false
% 3.19/1.04  --splitting_cvd_svl                     false
% 3.19/1.04  --splitting_nvd                         32
% 3.19/1.04  --sub_typing                            true
% 3.19/1.04  --prep_gs_sim                           true
% 3.19/1.04  --prep_unflatten                        true
% 3.19/1.04  --prep_res_sim                          true
% 3.19/1.04  --prep_upred                            true
% 3.19/1.04  --prep_sem_filter                       exhaustive
% 3.19/1.04  --prep_sem_filter_out                   false
% 3.19/1.04  --pred_elim                             true
% 3.19/1.04  --res_sim_input                         true
% 3.19/1.04  --eq_ax_congr_red                       true
% 3.19/1.04  --pure_diseq_elim                       true
% 3.19/1.04  --brand_transform                       false
% 3.19/1.04  --non_eq_to_eq                          false
% 3.19/1.04  --prep_def_merge                        true
% 3.19/1.04  --prep_def_merge_prop_impl              false
% 3.19/1.04  --prep_def_merge_mbd                    true
% 3.19/1.04  --prep_def_merge_tr_red                 false
% 3.19/1.04  --prep_def_merge_tr_cl                  false
% 3.19/1.04  --smt_preprocessing                     true
% 3.19/1.04  --smt_ac_axioms                         fast
% 3.19/1.04  --preprocessed_out                      false
% 3.19/1.04  --preprocessed_stats                    false
% 3.19/1.04  
% 3.19/1.04  ------ Abstraction refinement Options
% 3.19/1.04  
% 3.19/1.04  --abstr_ref                             []
% 3.19/1.04  --abstr_ref_prep                        false
% 3.19/1.04  --abstr_ref_until_sat                   false
% 3.19/1.04  --abstr_ref_sig_restrict                funpre
% 3.19/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/1.04  --abstr_ref_under                       []
% 3.19/1.04  
% 3.19/1.04  ------ SAT Options
% 3.19/1.04  
% 3.19/1.04  --sat_mode                              false
% 3.19/1.04  --sat_fm_restart_options                ""
% 3.19/1.04  --sat_gr_def                            false
% 3.19/1.04  --sat_epr_types                         true
% 3.19/1.04  --sat_non_cyclic_types                  false
% 3.19/1.04  --sat_finite_models                     false
% 3.19/1.04  --sat_fm_lemmas                         false
% 3.19/1.04  --sat_fm_prep                           false
% 3.19/1.04  --sat_fm_uc_incr                        true
% 3.19/1.04  --sat_out_model                         small
% 3.19/1.04  --sat_out_clauses                       false
% 3.19/1.04  
% 3.19/1.04  ------ QBF Options
% 3.19/1.04  
% 3.19/1.04  --qbf_mode                              false
% 3.19/1.04  --qbf_elim_univ                         false
% 3.19/1.04  --qbf_dom_inst                          none
% 3.19/1.04  --qbf_dom_pre_inst                      false
% 3.19/1.04  --qbf_sk_in                             false
% 3.19/1.04  --qbf_pred_elim                         true
% 3.19/1.04  --qbf_split                             512
% 3.19/1.04  
% 3.19/1.04  ------ BMC1 Options
% 3.19/1.04  
% 3.19/1.04  --bmc1_incremental                      false
% 3.19/1.04  --bmc1_axioms                           reachable_all
% 3.19/1.04  --bmc1_min_bound                        0
% 3.19/1.04  --bmc1_max_bound                        -1
% 3.19/1.04  --bmc1_max_bound_default                -1
% 3.19/1.04  --bmc1_symbol_reachability              true
% 3.19/1.04  --bmc1_property_lemmas                  false
% 3.19/1.04  --bmc1_k_induction                      false
% 3.19/1.04  --bmc1_non_equiv_states                 false
% 3.19/1.04  --bmc1_deadlock                         false
% 3.19/1.04  --bmc1_ucm                              false
% 3.19/1.04  --bmc1_add_unsat_core                   none
% 3.19/1.04  --bmc1_unsat_core_children              false
% 3.19/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/1.04  --bmc1_out_stat                         full
% 3.19/1.04  --bmc1_ground_init                      false
% 3.19/1.04  --bmc1_pre_inst_next_state              false
% 3.19/1.04  --bmc1_pre_inst_state                   false
% 3.19/1.04  --bmc1_pre_inst_reach_state             false
% 3.19/1.04  --bmc1_out_unsat_core                   false
% 3.19/1.04  --bmc1_aig_witness_out                  false
% 3.19/1.04  --bmc1_verbose                          false
% 3.19/1.04  --bmc1_dump_clauses_tptp                false
% 3.19/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.19/1.04  --bmc1_dump_file                        -
% 3.19/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.19/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.19/1.04  --bmc1_ucm_extend_mode                  1
% 3.19/1.04  --bmc1_ucm_init_mode                    2
% 3.19/1.04  --bmc1_ucm_cone_mode                    none
% 3.19/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.19/1.04  --bmc1_ucm_relax_model                  4
% 3.19/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.19/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/1.04  --bmc1_ucm_layered_model                none
% 3.19/1.04  --bmc1_ucm_max_lemma_size               10
% 3.19/1.04  
% 3.19/1.04  ------ AIG Options
% 3.19/1.04  
% 3.19/1.04  --aig_mode                              false
% 3.19/1.04  
% 3.19/1.04  ------ Instantiation Options
% 3.19/1.04  
% 3.19/1.04  --instantiation_flag                    true
% 3.19/1.04  --inst_sos_flag                         false
% 3.19/1.04  --inst_sos_phase                        true
% 3.19/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/1.04  --inst_lit_sel_side                     num_symb
% 3.19/1.04  --inst_solver_per_active                1400
% 3.19/1.04  --inst_solver_calls_frac                1.
% 3.19/1.04  --inst_passive_queue_type               priority_queues
% 3.19/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/1.04  --inst_passive_queues_freq              [25;2]
% 3.19/1.04  --inst_dismatching                      true
% 3.19/1.04  --inst_eager_unprocessed_to_passive     true
% 3.19/1.04  --inst_prop_sim_given                   true
% 3.19/1.04  --inst_prop_sim_new                     false
% 3.19/1.04  --inst_subs_new                         false
% 3.19/1.04  --inst_eq_res_simp                      false
% 3.19/1.04  --inst_subs_given                       false
% 3.19/1.04  --inst_orphan_elimination               true
% 3.19/1.04  --inst_learning_loop_flag               true
% 3.19/1.04  --inst_learning_start                   3000
% 3.19/1.04  --inst_learning_factor                  2
% 3.19/1.04  --inst_start_prop_sim_after_learn       3
% 3.19/1.04  --inst_sel_renew                        solver
% 3.19/1.04  --inst_lit_activity_flag                true
% 3.19/1.04  --inst_restr_to_given                   false
% 3.19/1.04  --inst_activity_threshold               500
% 3.19/1.04  --inst_out_proof                        true
% 3.19/1.04  
% 3.19/1.04  ------ Resolution Options
% 3.19/1.04  
% 3.19/1.04  --resolution_flag                       true
% 3.19/1.04  --res_lit_sel                           adaptive
% 3.19/1.04  --res_lit_sel_side                      none
% 3.19/1.04  --res_ordering                          kbo
% 3.19/1.04  --res_to_prop_solver                    active
% 3.19/1.04  --res_prop_simpl_new                    false
% 3.19/1.04  --res_prop_simpl_given                  true
% 3.19/1.04  --res_passive_queue_type                priority_queues
% 3.19/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/1.04  --res_passive_queues_freq               [15;5]
% 3.19/1.04  --res_forward_subs                      full
% 3.19/1.04  --res_backward_subs                     full
% 3.19/1.04  --res_forward_subs_resolution           true
% 3.19/1.04  --res_backward_subs_resolution          true
% 3.19/1.04  --res_orphan_elimination                true
% 3.19/1.04  --res_time_limit                        2.
% 3.19/1.04  --res_out_proof                         true
% 3.19/1.04  
% 3.19/1.04  ------ Superposition Options
% 3.19/1.04  
% 3.19/1.04  --superposition_flag                    true
% 3.19/1.04  --sup_passive_queue_type                priority_queues
% 3.19/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.19/1.04  --demod_completeness_check              fast
% 3.19/1.04  --demod_use_ground                      true
% 3.19/1.04  --sup_to_prop_solver                    passive
% 3.19/1.04  --sup_prop_simpl_new                    true
% 3.19/1.04  --sup_prop_simpl_given                  true
% 3.19/1.04  --sup_fun_splitting                     false
% 3.19/1.04  --sup_smt_interval                      50000
% 3.19/1.04  
% 3.19/1.04  ------ Superposition Simplification Setup
% 3.19/1.04  
% 3.19/1.04  --sup_indices_passive                   []
% 3.19/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.04  --sup_full_bw                           [BwDemod]
% 3.19/1.04  --sup_immed_triv                        [TrivRules]
% 3.19/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.04  --sup_immed_bw_main                     []
% 3.19/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/1.04  
% 3.19/1.04  ------ Combination Options
% 3.19/1.04  
% 3.19/1.04  --comb_res_mult                         3
% 3.19/1.04  --comb_sup_mult                         2
% 3.19/1.04  --comb_inst_mult                        10
% 3.19/1.04  
% 3.19/1.04  ------ Debug Options
% 3.19/1.04  
% 3.19/1.04  --dbg_backtrace                         false
% 3.19/1.04  --dbg_dump_prop_clauses                 false
% 3.19/1.04  --dbg_dump_prop_clauses_file            -
% 3.19/1.04  --dbg_out_stat                          false
% 3.19/1.04  ------ Parsing...
% 3.19/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.19/1.04  
% 3.19/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.19/1.04  
% 3.19/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.19/1.04  
% 3.19/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.19/1.04  ------ Proving...
% 3.19/1.04  ------ Problem Properties 
% 3.19/1.04  
% 3.19/1.04  
% 3.19/1.04  clauses                                 32
% 3.19/1.04  conjectures                             11
% 3.19/1.04  EPR                                     7
% 3.19/1.04  Horn                                    32
% 3.19/1.04  unary                                   16
% 3.19/1.04  binary                                  5
% 3.19/1.04  lits                                    90
% 3.19/1.04  lits eq                                 23
% 3.19/1.04  fd_pure                                 0
% 3.19/1.04  fd_pseudo                               0
% 3.19/1.04  fd_cond                                 0
% 3.19/1.04  fd_pseudo_cond                          1
% 3.19/1.04  AC symbols                              0
% 3.19/1.04  
% 3.19/1.04  ------ Schedule dynamic 5 is on 
% 3.19/1.04  
% 3.19/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.19/1.04  
% 3.19/1.04  
% 3.19/1.04  ------ 
% 3.19/1.04  Current options:
% 3.19/1.04  ------ 
% 3.19/1.04  
% 3.19/1.04  ------ Input Options
% 3.19/1.04  
% 3.19/1.04  --out_options                           all
% 3.19/1.04  --tptp_safe_out                         true
% 3.19/1.04  --problem_path                          ""
% 3.19/1.04  --include_path                          ""
% 3.19/1.04  --clausifier                            res/vclausify_rel
% 3.19/1.04  --clausifier_options                    --mode clausify
% 3.19/1.04  --stdin                                 false
% 3.19/1.04  --stats_out                             all
% 3.19/1.04  
% 3.19/1.04  ------ General Options
% 3.19/1.04  
% 3.19/1.04  --fof                                   false
% 3.19/1.04  --time_out_real                         305.
% 3.19/1.04  --time_out_virtual                      -1.
% 3.19/1.04  --symbol_type_check                     false
% 3.19/1.04  --clausify_out                          false
% 3.19/1.04  --sig_cnt_out                           false
% 3.19/1.04  --trig_cnt_out                          false
% 3.19/1.04  --trig_cnt_out_tolerance                1.
% 3.19/1.04  --trig_cnt_out_sk_spl                   false
% 3.19/1.04  --abstr_cl_out                          false
% 3.19/1.04  
% 3.19/1.04  ------ Global Options
% 3.19/1.04  
% 3.19/1.04  --schedule                              default
% 3.19/1.04  --add_important_lit                     false
% 3.19/1.04  --prop_solver_per_cl                    1000
% 3.19/1.04  --min_unsat_core                        false
% 3.19/1.04  --soft_assumptions                      false
% 3.19/1.04  --soft_lemma_size                       3
% 3.19/1.04  --prop_impl_unit_size                   0
% 3.19/1.04  --prop_impl_unit                        []
% 3.19/1.04  --share_sel_clauses                     true
% 3.19/1.04  --reset_solvers                         false
% 3.19/1.04  --bc_imp_inh                            [conj_cone]
% 3.19/1.04  --conj_cone_tolerance                   3.
% 3.19/1.04  --extra_neg_conj                        none
% 3.19/1.04  --large_theory_mode                     true
% 3.19/1.04  --prolific_symb_bound                   200
% 3.19/1.04  --lt_threshold                          2000
% 3.19/1.04  --clause_weak_htbl                      true
% 3.19/1.04  --gc_record_bc_elim                     false
% 3.19/1.04  
% 3.19/1.04  ------ Preprocessing Options
% 3.19/1.04  
% 3.19/1.04  --preprocessing_flag                    true
% 3.19/1.04  --time_out_prep_mult                    0.1
% 3.19/1.04  --splitting_mode                        input
% 3.19/1.04  --splitting_grd                         true
% 3.19/1.04  --splitting_cvd                         false
% 3.19/1.04  --splitting_cvd_svl                     false
% 3.19/1.04  --splitting_nvd                         32
% 3.19/1.04  --sub_typing                            true
% 3.19/1.04  --prep_gs_sim                           true
% 3.19/1.04  --prep_unflatten                        true
% 3.19/1.04  --prep_res_sim                          true
% 3.19/1.04  --prep_upred                            true
% 3.19/1.04  --prep_sem_filter                       exhaustive
% 3.19/1.04  --prep_sem_filter_out                   false
% 3.19/1.04  --pred_elim                             true
% 3.19/1.04  --res_sim_input                         true
% 3.19/1.04  --eq_ax_congr_red                       true
% 3.19/1.04  --pure_diseq_elim                       true
% 3.19/1.04  --brand_transform                       false
% 3.19/1.04  --non_eq_to_eq                          false
% 3.19/1.04  --prep_def_merge                        true
% 3.19/1.04  --prep_def_merge_prop_impl              false
% 3.19/1.04  --prep_def_merge_mbd                    true
% 3.19/1.04  --prep_def_merge_tr_red                 false
% 3.19/1.04  --prep_def_merge_tr_cl                  false
% 3.19/1.04  --smt_preprocessing                     true
% 3.19/1.04  --smt_ac_axioms                         fast
% 3.19/1.04  --preprocessed_out                      false
% 3.19/1.04  --preprocessed_stats                    false
% 3.19/1.04  
% 3.19/1.04  ------ Abstraction refinement Options
% 3.19/1.04  
% 3.19/1.04  --abstr_ref                             []
% 3.19/1.04  --abstr_ref_prep                        false
% 3.19/1.04  --abstr_ref_until_sat                   false
% 3.19/1.04  --abstr_ref_sig_restrict                funpre
% 3.19/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/1.04  --abstr_ref_under                       []
% 3.19/1.04  
% 3.19/1.04  ------ SAT Options
% 3.19/1.04  
% 3.19/1.04  --sat_mode                              false
% 3.19/1.04  --sat_fm_restart_options                ""
% 3.19/1.04  --sat_gr_def                            false
% 3.19/1.04  --sat_epr_types                         true
% 3.19/1.04  --sat_non_cyclic_types                  false
% 3.19/1.04  --sat_finite_models                     false
% 3.19/1.04  --sat_fm_lemmas                         false
% 3.19/1.04  --sat_fm_prep                           false
% 3.19/1.04  --sat_fm_uc_incr                        true
% 3.19/1.04  --sat_out_model                         small
% 3.19/1.04  --sat_out_clauses                       false
% 3.19/1.04  
% 3.19/1.04  ------ QBF Options
% 3.19/1.04  
% 3.19/1.04  --qbf_mode                              false
% 3.19/1.04  --qbf_elim_univ                         false
% 3.19/1.04  --qbf_dom_inst                          none
% 3.19/1.04  --qbf_dom_pre_inst                      false
% 3.19/1.04  --qbf_sk_in                             false
% 3.19/1.04  --qbf_pred_elim                         true
% 3.19/1.04  --qbf_split                             512
% 3.19/1.04  
% 3.19/1.04  ------ BMC1 Options
% 3.19/1.04  
% 3.19/1.04  --bmc1_incremental                      false
% 3.19/1.04  --bmc1_axioms                           reachable_all
% 3.19/1.04  --bmc1_min_bound                        0
% 3.19/1.04  --bmc1_max_bound                        -1
% 3.19/1.04  --bmc1_max_bound_default                -1
% 3.19/1.04  --bmc1_symbol_reachability              true
% 3.19/1.04  --bmc1_property_lemmas                  false
% 3.19/1.04  --bmc1_k_induction                      false
% 3.19/1.04  --bmc1_non_equiv_states                 false
% 3.19/1.04  --bmc1_deadlock                         false
% 3.19/1.04  --bmc1_ucm                              false
% 3.19/1.04  --bmc1_add_unsat_core                   none
% 3.19/1.04  --bmc1_unsat_core_children              false
% 3.19/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/1.04  --bmc1_out_stat                         full
% 3.19/1.04  --bmc1_ground_init                      false
% 3.19/1.04  --bmc1_pre_inst_next_state              false
% 3.19/1.04  --bmc1_pre_inst_state                   false
% 3.19/1.04  --bmc1_pre_inst_reach_state             false
% 3.19/1.04  --bmc1_out_unsat_core                   false
% 3.19/1.04  --bmc1_aig_witness_out                  false
% 3.19/1.04  --bmc1_verbose                          false
% 3.19/1.04  --bmc1_dump_clauses_tptp                false
% 3.19/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.19/1.04  --bmc1_dump_file                        -
% 3.19/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.19/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.19/1.04  --bmc1_ucm_extend_mode                  1
% 3.19/1.04  --bmc1_ucm_init_mode                    2
% 3.19/1.04  --bmc1_ucm_cone_mode                    none
% 3.19/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.19/1.04  --bmc1_ucm_relax_model                  4
% 3.19/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.19/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/1.04  --bmc1_ucm_layered_model                none
% 3.19/1.04  --bmc1_ucm_max_lemma_size               10
% 3.19/1.04  
% 3.19/1.04  ------ AIG Options
% 3.19/1.04  
% 3.19/1.04  --aig_mode                              false
% 3.19/1.04  
% 3.19/1.04  ------ Instantiation Options
% 3.19/1.04  
% 3.19/1.04  --instantiation_flag                    true
% 3.19/1.04  --inst_sos_flag                         false
% 3.19/1.04  --inst_sos_phase                        true
% 3.19/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/1.04  --inst_lit_sel_side                     none
% 3.19/1.04  --inst_solver_per_active                1400
% 3.19/1.04  --inst_solver_calls_frac                1.
% 3.19/1.04  --inst_passive_queue_type               priority_queues
% 3.19/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/1.04  --inst_passive_queues_freq              [25;2]
% 3.19/1.04  --inst_dismatching                      true
% 3.19/1.04  --inst_eager_unprocessed_to_passive     true
% 3.19/1.04  --inst_prop_sim_given                   true
% 3.19/1.04  --inst_prop_sim_new                     false
% 3.19/1.04  --inst_subs_new                         false
% 3.19/1.04  --inst_eq_res_simp                      false
% 3.19/1.04  --inst_subs_given                       false
% 3.19/1.04  --inst_orphan_elimination               true
% 3.19/1.04  --inst_learning_loop_flag               true
% 3.19/1.04  --inst_learning_start                   3000
% 3.19/1.04  --inst_learning_factor                  2
% 3.19/1.04  --inst_start_prop_sim_after_learn       3
% 3.19/1.04  --inst_sel_renew                        solver
% 3.19/1.04  --inst_lit_activity_flag                true
% 3.19/1.04  --inst_restr_to_given                   false
% 3.19/1.04  --inst_activity_threshold               500
% 3.19/1.04  --inst_out_proof                        true
% 3.19/1.04  
% 3.19/1.04  ------ Resolution Options
% 3.19/1.04  
% 3.19/1.04  --resolution_flag                       false
% 3.19/1.04  --res_lit_sel                           adaptive
% 3.19/1.04  --res_lit_sel_side                      none
% 3.19/1.04  --res_ordering                          kbo
% 3.19/1.04  --res_to_prop_solver                    active
% 3.19/1.04  --res_prop_simpl_new                    false
% 3.19/1.04  --res_prop_simpl_given                  true
% 3.19/1.04  --res_passive_queue_type                priority_queues
% 3.19/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/1.04  --res_passive_queues_freq               [15;5]
% 3.19/1.04  --res_forward_subs                      full
% 3.19/1.04  --res_backward_subs                     full
% 3.19/1.04  --res_forward_subs_resolution           true
% 3.19/1.04  --res_backward_subs_resolution          true
% 3.19/1.04  --res_orphan_elimination                true
% 3.19/1.04  --res_time_limit                        2.
% 3.19/1.04  --res_out_proof                         true
% 3.19/1.04  
% 3.19/1.04  ------ Superposition Options
% 3.19/1.04  
% 3.19/1.04  --superposition_flag                    true
% 3.19/1.04  --sup_passive_queue_type                priority_queues
% 3.19/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.19/1.04  --demod_completeness_check              fast
% 3.19/1.04  --demod_use_ground                      true
% 3.19/1.04  --sup_to_prop_solver                    passive
% 3.19/1.04  --sup_prop_simpl_new                    true
% 3.19/1.04  --sup_prop_simpl_given                  true
% 3.19/1.04  --sup_fun_splitting                     false
% 3.19/1.04  --sup_smt_interval                      50000
% 3.19/1.04  
% 3.19/1.04  ------ Superposition Simplification Setup
% 3.19/1.04  
% 3.19/1.04  --sup_indices_passive                   []
% 3.19/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.04  --sup_full_bw                           [BwDemod]
% 3.19/1.04  --sup_immed_triv                        [TrivRules]
% 3.19/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.04  --sup_immed_bw_main                     []
% 3.19/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/1.04  
% 3.19/1.04  ------ Combination Options
% 3.19/1.04  
% 3.19/1.04  --comb_res_mult                         3
% 3.19/1.04  --comb_sup_mult                         2
% 3.19/1.04  --comb_inst_mult                        10
% 3.19/1.04  
% 3.19/1.04  ------ Debug Options
% 3.19/1.04  
% 3.19/1.04  --dbg_backtrace                         false
% 3.19/1.04  --dbg_dump_prop_clauses                 false
% 3.19/1.04  --dbg_dump_prop_clauses_file            -
% 3.19/1.04  --dbg_out_stat                          false
% 3.19/1.04  
% 3.19/1.04  
% 3.19/1.04  
% 3.19/1.04  
% 3.19/1.04  ------ Proving...
% 3.19/1.04  
% 3.19/1.04  
% 3.19/1.04  % SZS status Theorem for theBenchmark.p
% 3.19/1.04  
% 3.19/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.19/1.04  
% 3.19/1.04  fof(f20,conjecture,(
% 3.19/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.19/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.04  
% 3.19/1.04  fof(f21,negated_conjecture,(
% 3.19/1.04    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.19/1.04    inference(negated_conjecture,[],[f20])).
% 3.19/1.04  
% 3.19/1.04  fof(f48,plain,(
% 3.19/1.04    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.19/1.04    inference(ennf_transformation,[],[f21])).
% 3.19/1.04  
% 3.19/1.04  fof(f49,plain,(
% 3.19/1.04    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.19/1.04    inference(flattening,[],[f48])).
% 3.19/1.04  
% 3.19/1.04  fof(f53,plain,(
% 3.19/1.04    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.19/1.04    introduced(choice_axiom,[])).
% 3.19/1.04  
% 3.19/1.04  fof(f52,plain,(
% 3.19/1.04    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.19/1.04    introduced(choice_axiom,[])).
% 3.19/1.04  
% 3.19/1.04  fof(f54,plain,(
% 3.19/1.04    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.19/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f53,f52])).
% 3.19/1.04  
% 3.19/1.04  fof(f82,plain,(
% 3.19/1.04    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.19/1.04    inference(cnf_transformation,[],[f54])).
% 3.19/1.04  
% 3.19/1.04  fof(f85,plain,(
% 3.19/1.04    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.19/1.04    inference(cnf_transformation,[],[f54])).
% 3.19/1.04  
% 3.19/1.04  fof(f17,axiom,(
% 3.19/1.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.19/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.04  
% 3.19/1.04  fof(f44,plain,(
% 3.19/1.04    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.19/1.04    inference(ennf_transformation,[],[f17])).
% 3.19/1.04  
% 3.19/1.04  fof(f45,plain,(
% 3.19/1.04    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.19/1.04    inference(flattening,[],[f44])).
% 3.19/1.04  
% 3.19/1.04  fof(f77,plain,(
% 3.19/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.19/1.04    inference(cnf_transformation,[],[f45])).
% 3.19/1.04  
% 3.19/1.04  fof(f83,plain,(
% 3.19/1.04    v1_funct_1(sK3)),
% 3.19/1.04    inference(cnf_transformation,[],[f54])).
% 3.19/1.04  
% 3.19/1.04  fof(f80,plain,(
% 3.19/1.04    v1_funct_1(sK2)),
% 3.19/1.04    inference(cnf_transformation,[],[f54])).
% 3.19/1.04  
% 3.19/1.04  fof(f14,axiom,(
% 3.19/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.19/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.04  
% 3.19/1.04  fof(f40,plain,(
% 3.19/1.04    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.19/1.04    inference(ennf_transformation,[],[f14])).
% 3.19/1.04  
% 3.19/1.04  fof(f41,plain,(
% 3.19/1.04    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/1.04    inference(flattening,[],[f40])).
% 3.19/1.04  
% 3.19/1.04  fof(f51,plain,(
% 3.19/1.04    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/1.04    inference(nnf_transformation,[],[f41])).
% 3.19/1.04  
% 3.19/1.04  fof(f72,plain,(
% 3.19/1.04    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/1.04    inference(cnf_transformation,[],[f51])).
% 3.19/1.04  
% 3.19/1.04  fof(f87,plain,(
% 3.19/1.04    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.19/1.04    inference(cnf_transformation,[],[f54])).
% 3.19/1.04  
% 3.19/1.04  fof(f16,axiom,(
% 3.19/1.04    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.19/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.04  
% 3.19/1.04  fof(f22,plain,(
% 3.19/1.04    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.19/1.04    inference(pure_predicate_removal,[],[f16])).
% 3.19/1.04  
% 3.19/1.04  fof(f76,plain,(
% 3.19/1.04    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.19/1.04    inference(cnf_transformation,[],[f22])).
% 3.19/1.04  
% 3.19/1.04  fof(f15,axiom,(
% 3.19/1.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.19/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.04  
% 3.19/1.04  fof(f42,plain,(
% 3.19/1.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.19/1.04    inference(ennf_transformation,[],[f15])).
% 3.19/1.04  
% 3.19/1.04  fof(f43,plain,(
% 3.19/1.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.19/1.04    inference(flattening,[],[f42])).
% 3.19/1.04  
% 3.19/1.04  fof(f75,plain,(
% 3.19/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.19/1.04    inference(cnf_transformation,[],[f43])).
% 3.19/1.04  
% 3.19/1.04  fof(f9,axiom,(
% 3.19/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.19/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.04  
% 3.19/1.04  fof(f33,plain,(
% 3.19/1.04    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.19/1.04    inference(ennf_transformation,[],[f9])).
% 3.19/1.04  
% 3.19/1.04  fof(f34,plain,(
% 3.19/1.04    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.19/1.04    inference(flattening,[],[f33])).
% 3.19/1.04  
% 3.19/1.04  fof(f67,plain,(
% 3.19/1.04    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/1.04    inference(cnf_transformation,[],[f34])).
% 3.19/1.04  
% 3.19/1.04  fof(f18,axiom,(
% 3.19/1.04    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.19/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.04  
% 3.19/1.04  fof(f78,plain,(
% 3.19/1.04    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.19/1.04    inference(cnf_transformation,[],[f18])).
% 3.19/1.04  
% 3.19/1.04  fof(f96,plain,(
% 3.19/1.04    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/1.04    inference(definition_unfolding,[],[f67,f78])).
% 3.19/1.04  
% 3.19/1.04  fof(f13,axiom,(
% 3.19/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.19/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.04  
% 3.19/1.04  fof(f39,plain,(
% 3.19/1.04    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/1.04    inference(ennf_transformation,[],[f13])).
% 3.19/1.04  
% 3.19/1.04  fof(f71,plain,(
% 3.19/1.04    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/1.04    inference(cnf_transformation,[],[f39])).
% 3.19/1.04  
% 3.19/1.04  fof(f86,plain,(
% 3.19/1.04    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.19/1.04    inference(cnf_transformation,[],[f54])).
% 3.19/1.04  
% 3.19/1.04  fof(f19,axiom,(
% 3.19/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.19/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.04  
% 3.19/1.04  fof(f46,plain,(
% 3.19/1.04    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.19/1.05    inference(ennf_transformation,[],[f19])).
% 3.19/1.05  
% 3.19/1.05  fof(f47,plain,(
% 3.19/1.05    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.19/1.05    inference(flattening,[],[f46])).
% 3.19/1.05  
% 3.19/1.05  fof(f79,plain,(
% 3.19/1.05    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.19/1.05    inference(cnf_transformation,[],[f47])).
% 3.19/1.05  
% 3.19/1.05  fof(f81,plain,(
% 3.19/1.05    v1_funct_2(sK2,sK0,sK1)),
% 3.19/1.05    inference(cnf_transformation,[],[f54])).
% 3.19/1.05  
% 3.19/1.05  fof(f84,plain,(
% 3.19/1.05    v1_funct_2(sK3,sK1,sK0)),
% 3.19/1.05    inference(cnf_transformation,[],[f54])).
% 3.19/1.05  
% 3.19/1.05  fof(f6,axiom,(
% 3.19/1.05    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.19/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.05  
% 3.19/1.05  fof(f63,plain,(
% 3.19/1.05    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.19/1.05    inference(cnf_transformation,[],[f6])).
% 3.19/1.05  
% 3.19/1.05  fof(f94,plain,(
% 3.19/1.05    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.19/1.05    inference(definition_unfolding,[],[f63,f78])).
% 3.19/1.05  
% 3.19/1.05  fof(f11,axiom,(
% 3.19/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.19/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.05  
% 3.19/1.05  fof(f37,plain,(
% 3.19/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/1.05    inference(ennf_transformation,[],[f11])).
% 3.19/1.05  
% 3.19/1.05  fof(f69,plain,(
% 3.19/1.05    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/1.05    inference(cnf_transformation,[],[f37])).
% 3.19/1.05  
% 3.19/1.05  fof(f3,axiom,(
% 3.19/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.19/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.05  
% 3.19/1.05  fof(f26,plain,(
% 3.19/1.05    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.19/1.05    inference(ennf_transformation,[],[f3])).
% 3.19/1.05  
% 3.19/1.05  fof(f58,plain,(
% 3.19/1.05    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.19/1.05    inference(cnf_transformation,[],[f26])).
% 3.19/1.05  
% 3.19/1.05  fof(f12,axiom,(
% 3.19/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.19/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.05  
% 3.19/1.05  fof(f23,plain,(
% 3.19/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.19/1.05    inference(pure_predicate_removal,[],[f12])).
% 3.19/1.05  
% 3.19/1.05  fof(f38,plain,(
% 3.19/1.05    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/1.05    inference(ennf_transformation,[],[f23])).
% 3.19/1.05  
% 3.19/1.05  fof(f70,plain,(
% 3.19/1.05    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/1.05    inference(cnf_transformation,[],[f38])).
% 3.19/1.05  
% 3.19/1.05  fof(f1,axiom,(
% 3.19/1.05    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.19/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.05  
% 3.19/1.05  fof(f24,plain,(
% 3.19/1.05    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.19/1.05    inference(ennf_transformation,[],[f1])).
% 3.19/1.05  
% 3.19/1.05  fof(f50,plain,(
% 3.19/1.05    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.19/1.05    inference(nnf_transformation,[],[f24])).
% 3.19/1.05  
% 3.19/1.05  fof(f55,plain,(
% 3.19/1.05    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.19/1.05    inference(cnf_transformation,[],[f50])).
% 3.19/1.05  
% 3.19/1.05  fof(f7,axiom,(
% 3.19/1.05    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.19/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.05  
% 3.19/1.05  fof(f29,plain,(
% 3.19/1.05    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.19/1.05    inference(ennf_transformation,[],[f7])).
% 3.19/1.05  
% 3.19/1.05  fof(f30,plain,(
% 3.19/1.05    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.19/1.05    inference(flattening,[],[f29])).
% 3.19/1.05  
% 3.19/1.05  fof(f64,plain,(
% 3.19/1.05    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.19/1.05    inference(cnf_transformation,[],[f30])).
% 3.19/1.05  
% 3.19/1.05  fof(f5,axiom,(
% 3.19/1.05    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.19/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.05  
% 3.19/1.05  fof(f60,plain,(
% 3.19/1.05    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.19/1.05    inference(cnf_transformation,[],[f5])).
% 3.19/1.05  
% 3.19/1.05  fof(f93,plain,(
% 3.19/1.05    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.19/1.05    inference(definition_unfolding,[],[f60,f78])).
% 3.19/1.05  
% 3.19/1.05  fof(f4,axiom,(
% 3.19/1.05    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.19/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.05  
% 3.19/1.05  fof(f27,plain,(
% 3.19/1.05    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.19/1.05    inference(ennf_transformation,[],[f4])).
% 3.19/1.05  
% 3.19/1.05  fof(f28,plain,(
% 3.19/1.05    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.19/1.05    inference(flattening,[],[f27])).
% 3.19/1.05  
% 3.19/1.05  fof(f59,plain,(
% 3.19/1.05    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.19/1.05    inference(cnf_transformation,[],[f28])).
% 3.19/1.05  
% 3.19/1.05  fof(f2,axiom,(
% 3.19/1.05    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.19/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.05  
% 3.19/1.05  fof(f25,plain,(
% 3.19/1.05    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.19/1.05    inference(ennf_transformation,[],[f2])).
% 3.19/1.05  
% 3.19/1.05  fof(f57,plain,(
% 3.19/1.05    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.19/1.05    inference(cnf_transformation,[],[f25])).
% 3.19/1.05  
% 3.19/1.05  fof(f8,axiom,(
% 3.19/1.05    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 3.19/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.05  
% 3.19/1.05  fof(f31,plain,(
% 3.19/1.05    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.19/1.05    inference(ennf_transformation,[],[f8])).
% 3.19/1.05  
% 3.19/1.05  fof(f32,plain,(
% 3.19/1.05    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.19/1.05    inference(flattening,[],[f31])).
% 3.19/1.05  
% 3.19/1.05  fof(f66,plain,(
% 3.19/1.05    ( ! [X0,X1] : (v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/1.05    inference(cnf_transformation,[],[f32])).
% 3.19/1.05  
% 3.19/1.05  fof(f10,axiom,(
% 3.19/1.05    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.19/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.05  
% 3.19/1.05  fof(f35,plain,(
% 3.19/1.05    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.19/1.05    inference(ennf_transformation,[],[f10])).
% 3.19/1.05  
% 3.19/1.05  fof(f36,plain,(
% 3.19/1.05    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.19/1.05    inference(flattening,[],[f35])).
% 3.19/1.05  
% 3.19/1.05  fof(f68,plain,(
% 3.19/1.05    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/1.05    inference(cnf_transformation,[],[f36])).
% 3.19/1.05  
% 3.19/1.05  fof(f91,plain,(
% 3.19/1.05    k2_funct_1(sK2) != sK3),
% 3.19/1.05    inference(cnf_transformation,[],[f54])).
% 3.19/1.05  
% 3.19/1.05  cnf(c_33,negated_conjecture,
% 3.19/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.19/1.05      inference(cnf_transformation,[],[f82]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1188,plain,
% 3.19/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_30,negated_conjecture,
% 3.19/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.19/1.05      inference(cnf_transformation,[],[f85]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1191,plain,
% 3.19/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_22,plain,
% 3.19/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.19/1.05      | ~ v1_funct_1(X0)
% 3.19/1.05      | ~ v1_funct_1(X3)
% 3.19/1.05      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.19/1.05      inference(cnf_transformation,[],[f77]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1193,plain,
% 3.19/1.05      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.19/1.05      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.19/1.05      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/1.05      | v1_funct_1(X4) != iProver_top
% 3.19/1.05      | v1_funct_1(X5) != iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_4047,plain,
% 3.19/1.05      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.19/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/1.05      | v1_funct_1(X2) != iProver_top
% 3.19/1.05      | v1_funct_1(sK3) != iProver_top ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_1191,c_1193]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_32,negated_conjecture,
% 3.19/1.05      ( v1_funct_1(sK3) ),
% 3.19/1.05      inference(cnf_transformation,[],[f83]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_39,plain,
% 3.19/1.05      ( v1_funct_1(sK3) = iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_4603,plain,
% 3.19/1.05      ( v1_funct_1(X2) != iProver_top
% 3.19/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/1.05      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.19/1.05      inference(global_propositional_subsumption,
% 3.19/1.05                [status(thm)],
% 3.19/1.05                [c_4047,c_39]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_4604,plain,
% 3.19/1.05      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.19/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/1.05      | v1_funct_1(X2) != iProver_top ),
% 3.19/1.05      inference(renaming,[status(thm)],[c_4603]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_4614,plain,
% 3.19/1.05      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.19/1.05      | v1_funct_1(sK2) != iProver_top ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_1188,c_4604]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_35,negated_conjecture,
% 3.19/1.05      ( v1_funct_1(sK2) ),
% 3.19/1.05      inference(cnf_transformation,[],[f80]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1621,plain,
% 3.19/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.19/1.05      | ~ v1_funct_1(X0)
% 3.19/1.05      | ~ v1_funct_1(sK3)
% 3.19/1.05      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 3.19/1.05      inference(instantiation,[status(thm)],[c_22]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1936,plain,
% 3.19/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/1.05      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.19/1.05      | ~ v1_funct_1(sK3)
% 3.19/1.05      | ~ v1_funct_1(sK2)
% 3.19/1.05      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.19/1.05      inference(instantiation,[status(thm)],[c_1621]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_2264,plain,
% 3.19/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.19/1.05      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/1.05      | ~ v1_funct_1(sK3)
% 3.19/1.05      | ~ v1_funct_1(sK2)
% 3.19/1.05      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.19/1.05      inference(instantiation,[status(thm)],[c_1936]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_3473,plain,
% 3.19/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.19/1.05      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.19/1.05      | ~ v1_funct_1(sK3)
% 3.19/1.05      | ~ v1_funct_1(sK2)
% 3.19/1.05      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.19/1.05      inference(instantiation,[status(thm)],[c_2264]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_4684,plain,
% 3.19/1.05      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.19/1.05      inference(global_propositional_subsumption,
% 3.19/1.05                [status(thm)],
% 3.19/1.05                [c_4614,c_35,c_33,c_32,c_30,c_3473]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_18,plain,
% 3.19/1.05      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.19/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/1.05      | X3 = X2 ),
% 3.19/1.05      inference(cnf_transformation,[],[f72]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_28,negated_conjecture,
% 3.19/1.05      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.19/1.05      inference(cnf_transformation,[],[f87]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_456,plain,
% 3.19/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.05      | X3 = X0
% 3.19/1.05      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.19/1.05      | k6_partfun1(sK0) != X3
% 3.19/1.05      | sK0 != X2
% 3.19/1.05      | sK0 != X1 ),
% 3.19/1.05      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_457,plain,
% 3.19/1.05      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.19/1.05      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.19/1.05      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.19/1.05      inference(unflattening,[status(thm)],[c_456]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_21,plain,
% 3.19/1.05      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.19/1.05      inference(cnf_transformation,[],[f76]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_51,plain,
% 3.19/1.05      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.19/1.05      inference(instantiation,[status(thm)],[c_21]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_459,plain,
% 3.19/1.05      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.19/1.05      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.19/1.05      inference(global_propositional_subsumption,
% 3.19/1.05                [status(thm)],
% 3.19/1.05                [c_457,c_51]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1182,plain,
% 3.19/1.05      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.19/1.05      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_4687,plain,
% 3.19/1.05      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.19/1.05      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.19/1.05      inference(demodulation,[status(thm)],[c_4684,c_1182]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_36,plain,
% 3.19/1.05      ( v1_funct_1(sK2) = iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_38,plain,
% 3.19/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_41,plain,
% 3.19/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_19,plain,
% 3.19/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.19/1.05      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.19/1.05      | ~ v1_funct_1(X0)
% 3.19/1.05      | ~ v1_funct_1(X3) ),
% 3.19/1.05      inference(cnf_transformation,[],[f75]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1196,plain,
% 3.19/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.19/1.05      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.19/1.05      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.19/1.05      | v1_funct_1(X3) != iProver_top
% 3.19/1.05      | v1_funct_1(X0) != iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_5002,plain,
% 3.19/1.05      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.19/1.05      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.19/1.05      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.19/1.05      | v1_funct_1(sK3) != iProver_top
% 3.19/1.05      | v1_funct_1(sK2) != iProver_top ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_4684,c_1196]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_5979,plain,
% 3.19/1.05      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.19/1.05      inference(global_propositional_subsumption,
% 3.19/1.05                [status(thm)],
% 3.19/1.05                [c_4687,c_36,c_38,c_39,c_41,c_5002]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_12,plain,
% 3.19/1.05      ( ~ v1_funct_1(X0)
% 3.19/1.05      | ~ v1_funct_1(X1)
% 3.19/1.05      | ~ v2_funct_1(X1)
% 3.19/1.05      | ~ v1_relat_1(X0)
% 3.19/1.05      | ~ v1_relat_1(X1)
% 3.19/1.05      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.19/1.05      | k2_funct_1(X1) = X0
% 3.19/1.05      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 3.19/1.05      inference(cnf_transformation,[],[f96]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1200,plain,
% 3.19/1.05      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.19/1.05      | k2_funct_1(X1) = X0
% 3.19/1.05      | k2_relat_1(X0) != k1_relat_1(X1)
% 3.19/1.05      | v1_funct_1(X0) != iProver_top
% 3.19/1.05      | v1_funct_1(X1) != iProver_top
% 3.19/1.05      | v2_funct_1(X1) != iProver_top
% 3.19/1.05      | v1_relat_1(X0) != iProver_top
% 3.19/1.05      | v1_relat_1(X1) != iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_5996,plain,
% 3.19/1.05      ( k2_funct_1(sK3) = sK2
% 3.19/1.05      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 3.19/1.05      | k2_relat_1(sK2) != k1_relat_1(sK3)
% 3.19/1.05      | v1_funct_1(sK3) != iProver_top
% 3.19/1.05      | v1_funct_1(sK2) != iProver_top
% 3.19/1.05      | v2_funct_1(sK3) != iProver_top
% 3.19/1.05      | v1_relat_1(sK3) != iProver_top
% 3.19/1.05      | v1_relat_1(sK2) != iProver_top ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_5979,c_1200]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_16,plain,
% 3.19/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.05      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.19/1.05      inference(cnf_transformation,[],[f71]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1197,plain,
% 3.19/1.05      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.19/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_2228,plain,
% 3.19/1.05      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_1188,c_1197]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_29,negated_conjecture,
% 3.19/1.05      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.19/1.05      inference(cnf_transformation,[],[f86]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_2230,plain,
% 3.19/1.05      ( k2_relat_1(sK2) = sK1 ),
% 3.19/1.05      inference(light_normalisation,[status(thm)],[c_2228,c_29]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_2227,plain,
% 3.19/1.05      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_1191,c_1197]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_23,plain,
% 3.19/1.05      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.19/1.05      | ~ v1_funct_2(X2,X0,X1)
% 3.19/1.05      | ~ v1_funct_2(X3,X1,X0)
% 3.19/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.19/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/1.05      | ~ v1_funct_1(X2)
% 3.19/1.05      | ~ v1_funct_1(X3)
% 3.19/1.05      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.19/1.05      inference(cnf_transformation,[],[f79]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_470,plain,
% 3.19/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 3.19/1.05      | ~ v1_funct_2(X3,X2,X1)
% 3.19/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.19/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.05      | ~ v1_funct_1(X3)
% 3.19/1.05      | ~ v1_funct_1(X0)
% 3.19/1.05      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.19/1.05      | k2_relset_1(X2,X1,X3) = X1
% 3.19/1.05      | k6_partfun1(X1) != k6_partfun1(sK0)
% 3.19/1.05      | sK0 != X1 ),
% 3.19/1.05      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_471,plain,
% 3.19/1.05      ( ~ v1_funct_2(X0,X1,sK0)
% 3.19/1.05      | ~ v1_funct_2(X2,sK0,X1)
% 3.19/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.19/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.19/1.05      | ~ v1_funct_1(X2)
% 3.19/1.05      | ~ v1_funct_1(X0)
% 3.19/1.05      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.19/1.05      | k2_relset_1(X1,sK0,X0) = sK0
% 3.19/1.05      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.19/1.05      inference(unflattening,[status(thm)],[c_470]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_551,plain,
% 3.19/1.05      ( ~ v1_funct_2(X0,X1,sK0)
% 3.19/1.05      | ~ v1_funct_2(X2,sK0,X1)
% 3.19/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.19/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.19/1.05      | ~ v1_funct_1(X0)
% 3.19/1.05      | ~ v1_funct_1(X2)
% 3.19/1.05      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.19/1.05      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.19/1.05      inference(equality_resolution_simp,[status(thm)],[c_471]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1181,plain,
% 3.19/1.05      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.19/1.05      | k2_relset_1(X0,sK0,X2) = sK0
% 3.19/1.05      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.19/1.05      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.19/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.19/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.19/1.05      | v1_funct_1(X1) != iProver_top
% 3.19/1.05      | v1_funct_1(X2) != iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_551]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1650,plain,
% 3.19/1.05      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.19/1.05      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.19/1.05      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.19/1.05      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.19/1.05      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.19/1.05      | v1_funct_1(sK3) != iProver_top
% 3.19/1.05      | v1_funct_1(sK2) != iProver_top ),
% 3.19/1.05      inference(equality_resolution,[status(thm)],[c_1181]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_34,negated_conjecture,
% 3.19/1.05      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.19/1.05      inference(cnf_transformation,[],[f81]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_37,plain,
% 3.19/1.05      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_31,negated_conjecture,
% 3.19/1.05      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.19/1.05      inference(cnf_transformation,[],[f84]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_40,plain,
% 3.19/1.05      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_2009,plain,
% 3.19/1.05      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.19/1.05      inference(global_propositional_subsumption,
% 3.19/1.05                [status(thm)],
% 3.19/1.05                [c_1650,c_36,c_37,c_38,c_39,c_40,c_41]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_2233,plain,
% 3.19/1.05      ( k2_relat_1(sK3) = sK0 ),
% 3.19/1.05      inference(light_normalisation,[status(thm)],[c_2227,c_2009]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_5997,plain,
% 3.19/1.05      ( k2_funct_1(sK3) = sK2
% 3.19/1.05      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 3.19/1.05      | k1_relat_1(sK3) != sK1
% 3.19/1.05      | v1_funct_1(sK3) != iProver_top
% 3.19/1.05      | v1_funct_1(sK2) != iProver_top
% 3.19/1.05      | v2_funct_1(sK3) != iProver_top
% 3.19/1.05      | v1_relat_1(sK3) != iProver_top
% 3.19/1.05      | v1_relat_1(sK2) != iProver_top ),
% 3.19/1.05      inference(light_normalisation,[status(thm)],[c_5996,c_2230,c_2233]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_5998,plain,
% 3.19/1.05      ( k2_funct_1(sK3) = sK2
% 3.19/1.05      | k1_relat_1(sK3) != sK1
% 3.19/1.05      | v1_funct_1(sK3) != iProver_top
% 3.19/1.05      | v1_funct_1(sK2) != iProver_top
% 3.19/1.05      | v2_funct_1(sK3) != iProver_top
% 3.19/1.05      | v1_relat_1(sK3) != iProver_top
% 3.19/1.05      | v1_relat_1(sK2) != iProver_top ),
% 3.19/1.05      inference(equality_resolution_simp,[status(thm)],[c_5997]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_7,plain,
% 3.19/1.05      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.19/1.05      inference(cnf_transformation,[],[f94]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_90,plain,
% 3.19/1.05      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_92,plain,
% 3.19/1.05      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 3.19/1.05      inference(instantiation,[status(thm)],[c_90]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_14,plain,
% 3.19/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.05      | v1_relat_1(X0) ),
% 3.19/1.05      inference(cnf_transformation,[],[f69]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1457,plain,
% 3.19/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.19/1.05      | v1_relat_1(sK3) ),
% 3.19/1.05      inference(instantiation,[status(thm)],[c_14]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1458,plain,
% 3.19/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.19/1.05      | v1_relat_1(sK3) = iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_1457]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1460,plain,
% 3.19/1.05      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.19/1.05      | v1_relat_1(sK2) ),
% 3.19/1.05      inference(instantiation,[status(thm)],[c_14]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1461,plain,
% 3.19/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.19/1.05      | v1_relat_1(sK2) = iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_1460]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1198,plain,
% 3.19/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.19/1.05      | v1_relat_1(X0) = iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_2083,plain,
% 3.19/1.05      ( v1_relat_1(sK3) = iProver_top ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_1191,c_1198]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_2084,plain,
% 3.19/1.05      ( v1_relat_1(sK2) = iProver_top ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_1188,c_1198]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_3,plain,
% 3.19/1.05      ( ~ v1_relat_1(X0)
% 3.19/1.05      | ~ v1_relat_1(X1)
% 3.19/1.05      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 3.19/1.05      inference(cnf_transformation,[],[f58]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1205,plain,
% 3.19/1.05      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 3.19/1.05      | v1_relat_1(X1) != iProver_top
% 3.19/1.05      | v1_relat_1(X0) != iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_3672,plain,
% 3.19/1.05      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 3.19/1.05      | v1_relat_1(X0) != iProver_top ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_2084,c_1205]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_5774,plain,
% 3.19/1.05      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_2083,c_3672]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_15,plain,
% 3.19/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.05      | v4_relat_1(X0,X1) ),
% 3.19/1.05      inference(cnf_transformation,[],[f70]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1,plain,
% 3.19/1.05      ( r1_tarski(k1_relat_1(X0),X1)
% 3.19/1.05      | ~ v4_relat_1(X0,X1)
% 3.19/1.05      | ~ v1_relat_1(X0) ),
% 3.19/1.05      inference(cnf_transformation,[],[f55]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_9,plain,
% 3.19/1.05      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.19/1.05      | ~ v1_funct_1(X1)
% 3.19/1.05      | ~ v1_relat_1(X1)
% 3.19/1.05      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.19/1.05      inference(cnf_transformation,[],[f64]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_346,plain,
% 3.19/1.05      ( ~ v4_relat_1(X0,X1)
% 3.19/1.05      | ~ v1_funct_1(X2)
% 3.19/1.05      | ~ v1_relat_1(X0)
% 3.19/1.05      | ~ v1_relat_1(X2)
% 3.19/1.05      | k9_relat_1(X2,k10_relat_1(X2,X3)) = X3
% 3.19/1.05      | k2_relat_1(X2) != X1
% 3.19/1.05      | k1_relat_1(X0) != X3 ),
% 3.19/1.05      inference(resolution_lifted,[status(thm)],[c_1,c_9]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_347,plain,
% 3.19/1.05      ( ~ v4_relat_1(X0,k2_relat_1(X1))
% 3.19/1.05      | ~ v1_funct_1(X1)
% 3.19/1.05      | ~ v1_relat_1(X0)
% 3.19/1.05      | ~ v1_relat_1(X1)
% 3.19/1.05      | k9_relat_1(X1,k10_relat_1(X1,k1_relat_1(X0))) = k1_relat_1(X0) ),
% 3.19/1.05      inference(unflattening,[status(thm)],[c_346]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_390,plain,
% 3.19/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.05      | ~ v1_funct_1(X3)
% 3.19/1.05      | ~ v1_relat_1(X4)
% 3.19/1.05      | ~ v1_relat_1(X3)
% 3.19/1.05      | X4 != X0
% 3.19/1.05      | k9_relat_1(X3,k10_relat_1(X3,k1_relat_1(X4))) = k1_relat_1(X4)
% 3.19/1.05      | k2_relat_1(X3) != X1 ),
% 3.19/1.05      inference(resolution_lifted,[status(thm)],[c_15,c_347]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_391,plain,
% 3.19/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2)))
% 3.19/1.05      | ~ v1_funct_1(X1)
% 3.19/1.05      | ~ v1_relat_1(X0)
% 3.19/1.05      | ~ v1_relat_1(X1)
% 3.19/1.05      | k9_relat_1(X1,k10_relat_1(X1,k1_relat_1(X0))) = k1_relat_1(X0) ),
% 3.19/1.05      inference(unflattening,[status(thm)],[c_390]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_405,plain,
% 3.19/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2)))
% 3.19/1.05      | ~ v1_funct_1(X1)
% 3.19/1.05      | ~ v1_relat_1(X1)
% 3.19/1.05      | k9_relat_1(X1,k10_relat_1(X1,k1_relat_1(X0))) = k1_relat_1(X0) ),
% 3.19/1.05      inference(forward_subsumption_resolution,
% 3.19/1.05                [status(thm)],
% 3.19/1.05                [c_391,c_14]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1184,plain,
% 3.19/1.05      ( k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(X1))) = k1_relat_1(X1)
% 3.19/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),X2))) != iProver_top
% 3.19/1.05      | v1_funct_1(X0) != iProver_top
% 3.19/1.05      | v1_relat_1(X0) != iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_3587,plain,
% 3.19/1.05      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
% 3.19/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) != iProver_top
% 3.19/1.05      | v1_funct_1(sK2) != iProver_top
% 3.19/1.05      | v1_relat_1(sK2) != iProver_top ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_2230,c_1184]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_3938,plain,
% 3.19/1.05      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
% 3.19/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) != iProver_top ),
% 3.19/1.05      inference(global_propositional_subsumption,
% 3.19/1.05                [status(thm)],
% 3.19/1.05                [c_3587,c_36,c_38,c_1461]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_3947,plain,
% 3.19/1.05      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_1191,c_3938]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_5785,plain,
% 3.19/1.05      ( k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(sK3) ),
% 3.19/1.05      inference(demodulation,[status(thm)],[c_5774,c_3947]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_5982,plain,
% 3.19/1.05      ( k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) = k1_relat_1(sK3) ),
% 3.19/1.05      inference(demodulation,[status(thm)],[c_5979,c_5785]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_6,plain,
% 3.19/1.05      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.19/1.05      inference(cnf_transformation,[],[f93]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_4,plain,
% 3.19/1.05      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.19/1.05      inference(cnf_transformation,[],[f59]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_373,plain,
% 3.19/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.05      | ~ v1_relat_1(X0)
% 3.19/1.05      | k7_relat_1(X0,X1) = X0 ),
% 3.19/1.05      inference(resolution,[status(thm)],[c_15,c_4]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_377,plain,
% 3.19/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.05      | k7_relat_1(X0,X1) = X0 ),
% 3.19/1.05      inference(global_propositional_subsumption,
% 3.19/1.05                [status(thm)],
% 3.19/1.05                [c_373,c_15,c_14,c_4]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1185,plain,
% 3.19/1.05      ( k7_relat_1(X0,X1) = X0
% 3.19/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_3436,plain,
% 3.19/1.05      ( k7_relat_1(sK2,sK0) = sK2 ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_1188,c_1185]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_2,plain,
% 3.19/1.05      ( ~ v1_relat_1(X0)
% 3.19/1.05      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.19/1.05      inference(cnf_transformation,[],[f57]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1206,plain,
% 3.19/1.05      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.19/1.05      | v1_relat_1(X0) != iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_2460,plain,
% 3.19/1.05      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_2084,c_1206]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_3486,plain,
% 3.19/1.05      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_3436,c_2460]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_3487,plain,
% 3.19/1.05      ( k9_relat_1(sK2,sK0) = sK1 ),
% 3.19/1.05      inference(light_normalisation,[status(thm)],[c_3486,c_2230]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_5991,plain,
% 3.19/1.05      ( k1_relat_1(sK3) = sK1 ),
% 3.19/1.05      inference(demodulation,[status(thm)],[c_5982,c_6,c_3487]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_10,plain,
% 3.19/1.05      ( ~ v1_funct_1(X0)
% 3.19/1.05      | ~ v1_funct_1(X1)
% 3.19/1.05      | v2_funct_1(X1)
% 3.19/1.05      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 3.19/1.05      | ~ v1_relat_1(X0)
% 3.19/1.05      | ~ v1_relat_1(X1)
% 3.19/1.05      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 3.19/1.05      inference(cnf_transformation,[],[f66]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1202,plain,
% 3.19/1.05      ( k2_relat_1(X0) != k1_relat_1(X1)
% 3.19/1.05      | v1_funct_1(X0) != iProver_top
% 3.19/1.05      | v1_funct_1(X1) != iProver_top
% 3.19/1.05      | v2_funct_1(X1) = iProver_top
% 3.19/1.05      | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
% 3.19/1.05      | v1_relat_1(X0) != iProver_top
% 3.19/1.05      | v1_relat_1(X1) != iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_4449,plain,
% 3.19/1.05      ( k1_relat_1(X0) != sK1
% 3.19/1.05      | v1_funct_1(X0) != iProver_top
% 3.19/1.05      | v1_funct_1(sK2) != iProver_top
% 3.19/1.05      | v2_funct_1(X0) = iProver_top
% 3.19/1.05      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
% 3.19/1.05      | v1_relat_1(X0) != iProver_top
% 3.19/1.05      | v1_relat_1(sK2) != iProver_top ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_2230,c_1202]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_4930,plain,
% 3.19/1.05      ( v1_relat_1(X0) != iProver_top
% 3.19/1.05      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
% 3.19/1.05      | v2_funct_1(X0) = iProver_top
% 3.19/1.05      | k1_relat_1(X0) != sK1
% 3.19/1.05      | v1_funct_1(X0) != iProver_top ),
% 3.19/1.05      inference(global_propositional_subsumption,
% 3.19/1.05                [status(thm)],
% 3.19/1.05                [c_4449,c_36,c_38,c_1461]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_4931,plain,
% 3.19/1.05      ( k1_relat_1(X0) != sK1
% 3.19/1.05      | v1_funct_1(X0) != iProver_top
% 3.19/1.05      | v2_funct_1(X0) = iProver_top
% 3.19/1.05      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
% 3.19/1.05      | v1_relat_1(X0) != iProver_top ),
% 3.19/1.05      inference(renaming,[status(thm)],[c_4930]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_6631,plain,
% 3.19/1.05      ( v1_funct_1(sK3) != iProver_top
% 3.19/1.05      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 3.19/1.05      | v2_funct_1(sK3) = iProver_top
% 3.19/1.05      | v1_relat_1(sK3) != iProver_top ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_5991,c_4931]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_6636,plain,
% 3.19/1.05      ( v1_funct_1(sK3) != iProver_top
% 3.19/1.05      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.19/1.05      | v2_funct_1(sK3) = iProver_top
% 3.19/1.05      | v1_relat_1(sK3) != iProver_top ),
% 3.19/1.05      inference(light_normalisation,[status(thm)],[c_6631,c_5979]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_8422,plain,
% 3.19/1.05      ( k2_funct_1(sK3) = sK2 ),
% 3.19/1.05      inference(global_propositional_subsumption,
% 3.19/1.05                [status(thm)],
% 3.19/1.05                [c_5998,c_36,c_38,c_39,c_41,c_92,c_1458,c_1461,c_5991,
% 3.19/1.05                 c_6636]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1189,plain,
% 3.19/1.05      ( v1_funct_1(sK3) = iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_13,plain,
% 3.19/1.05      ( ~ v1_funct_1(X0)
% 3.19/1.05      | ~ v2_funct_1(X0)
% 3.19/1.05      | ~ v1_relat_1(X0)
% 3.19/1.05      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.19/1.05      inference(cnf_transformation,[],[f68]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1199,plain,
% 3.19/1.05      ( k2_funct_1(k2_funct_1(X0)) = X0
% 3.19/1.05      | v1_funct_1(X0) != iProver_top
% 3.19/1.05      | v2_funct_1(X0) != iProver_top
% 3.19/1.05      | v1_relat_1(X0) != iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_3728,plain,
% 3.19/1.05      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.19/1.05      | v2_funct_1(sK3) != iProver_top
% 3.19/1.05      | v1_relat_1(sK3) != iProver_top ),
% 3.19/1.05      inference(superposition,[status(thm)],[c_1189,c_1199]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1495,plain,
% 3.19/1.05      ( ~ v1_funct_1(sK3)
% 3.19/1.05      | ~ v2_funct_1(sK3)
% 3.19/1.05      | ~ v1_relat_1(sK3)
% 3.19/1.05      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 3.19/1.05      inference(instantiation,[status(thm)],[c_13]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_1496,plain,
% 3.19/1.05      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.19/1.05      | v1_funct_1(sK3) != iProver_top
% 3.19/1.05      | v2_funct_1(sK3) != iProver_top
% 3.19/1.05      | v1_relat_1(sK3) != iProver_top ),
% 3.19/1.05      inference(predicate_to_equality,[status(thm)],[c_1495]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_3800,plain,
% 3.19/1.05      ( v2_funct_1(sK3) != iProver_top
% 3.19/1.05      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 3.19/1.05      inference(global_propositional_subsumption,
% 3.19/1.05                [status(thm)],
% 3.19/1.05                [c_3728,c_39,c_41,c_1458,c_1496]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_3801,plain,
% 3.19/1.05      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.19/1.05      | v2_funct_1(sK3) != iProver_top ),
% 3.19/1.05      inference(renaming,[status(thm)],[c_3800]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_8425,plain,
% 3.19/1.05      ( k2_funct_1(sK2) = sK3 | v2_funct_1(sK3) != iProver_top ),
% 3.19/1.05      inference(demodulation,[status(thm)],[c_8422,c_3801]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(c_24,negated_conjecture,
% 3.19/1.05      ( k2_funct_1(sK2) != sK3 ),
% 3.19/1.05      inference(cnf_transformation,[],[f91]) ).
% 3.19/1.05  
% 3.19/1.05  cnf(contradiction,plain,
% 3.19/1.05      ( $false ),
% 3.19/1.05      inference(minisat,
% 3.19/1.05                [status(thm)],
% 3.19/1.05                [c_8425,c_6636,c_1458,c_92,c_24,c_41,c_39]) ).
% 3.19/1.05  
% 3.19/1.05  
% 3.19/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 3.19/1.05  
% 3.19/1.05  ------                               Statistics
% 3.19/1.05  
% 3.19/1.05  ------ General
% 3.19/1.05  
% 3.19/1.05  abstr_ref_over_cycles:                  0
% 3.19/1.05  abstr_ref_under_cycles:                 0
% 3.19/1.05  gc_basic_clause_elim:                   0
% 3.19/1.05  forced_gc_time:                         0
% 3.19/1.05  parsing_time:                           0.011
% 3.19/1.05  unif_index_cands_time:                  0.
% 3.19/1.05  unif_index_add_time:                    0.
% 3.19/1.05  orderings_time:                         0.
% 3.19/1.05  out_proof_time:                         0.014
% 3.19/1.05  total_time:                             0.293
% 3.19/1.05  num_of_symbols:                         56
% 3.19/1.05  num_of_terms:                           10673
% 3.19/1.05  
% 3.19/1.05  ------ Preprocessing
% 3.19/1.05  
% 3.19/1.05  num_of_splits:                          0
% 3.19/1.05  num_of_split_atoms:                     0
% 3.19/1.05  num_of_reused_defs:                     0
% 3.19/1.05  num_eq_ax_congr_red:                    20
% 3.19/1.05  num_of_sem_filtered_clauses:            1
% 3.19/1.05  num_of_subtypes:                        0
% 3.19/1.05  monotx_restored_types:                  0
% 3.19/1.05  sat_num_of_epr_types:                   0
% 3.19/1.05  sat_num_of_non_cyclic_types:            0
% 3.19/1.05  sat_guarded_non_collapsed_types:        0
% 3.19/1.05  num_pure_diseq_elim:                    0
% 3.19/1.05  simp_replaced_by:                       0
% 3.19/1.05  res_preprocessed:                       167
% 3.19/1.05  prep_upred:                             0
% 3.19/1.05  prep_unflattend:                        16
% 3.19/1.05  smt_new_axioms:                         0
% 3.19/1.05  pred_elim_cands:                        5
% 3.19/1.05  pred_elim:                              3
% 3.19/1.05  pred_elim_cl:                           4
% 3.19/1.05  pred_elim_cycles:                       5
% 3.19/1.05  merged_defs:                            0
% 3.19/1.05  merged_defs_ncl:                        0
% 3.19/1.05  bin_hyper_res:                          0
% 3.19/1.05  prep_cycles:                            4
% 3.19/1.05  pred_elim_time:                         0.007
% 3.19/1.05  splitting_time:                         0.
% 3.19/1.05  sem_filter_time:                        0.
% 3.19/1.05  monotx_time:                            0.001
% 3.19/1.05  subtype_inf_time:                       0.
% 3.19/1.05  
% 3.19/1.05  ------ Problem properties
% 3.19/1.05  
% 3.19/1.05  clauses:                                32
% 3.19/1.05  conjectures:                            11
% 3.19/1.05  epr:                                    7
% 3.19/1.05  horn:                                   32
% 3.19/1.05  ground:                                 12
% 3.19/1.05  unary:                                  16
% 3.19/1.05  binary:                                 5
% 3.19/1.05  lits:                                   90
% 3.19/1.05  lits_eq:                                23
% 3.19/1.05  fd_pure:                                0
% 3.19/1.05  fd_pseudo:                              0
% 3.19/1.05  fd_cond:                                0
% 3.19/1.05  fd_pseudo_cond:                         1
% 3.19/1.05  ac_symbols:                             0
% 3.19/1.05  
% 3.19/1.05  ------ Propositional Solver
% 3.19/1.05  
% 3.19/1.05  prop_solver_calls:                      29
% 3.19/1.05  prop_fast_solver_calls:                 1286
% 3.19/1.05  smt_solver_calls:                       0
% 3.19/1.05  smt_fast_solver_calls:                  0
% 3.19/1.05  prop_num_of_clauses:                    3773
% 3.19/1.05  prop_preprocess_simplified:             9155
% 3.19/1.05  prop_fo_subsumed:                       55
% 3.19/1.05  prop_solver_time:                       0.
% 3.19/1.05  smt_solver_time:                        0.
% 3.19/1.05  smt_fast_solver_time:                   0.
% 3.19/1.05  prop_fast_solver_time:                  0.
% 3.19/1.05  prop_unsat_core_time:                   0.
% 3.19/1.05  
% 3.19/1.05  ------ QBF
% 3.19/1.05  
% 3.19/1.05  qbf_q_res:                              0
% 3.19/1.05  qbf_num_tautologies:                    0
% 3.19/1.05  qbf_prep_cycles:                        0
% 3.19/1.05  
% 3.19/1.05  ------ BMC1
% 3.19/1.05  
% 3.19/1.05  bmc1_current_bound:                     -1
% 3.19/1.05  bmc1_last_solved_bound:                 -1
% 3.19/1.05  bmc1_unsat_core_size:                   -1
% 3.19/1.05  bmc1_unsat_core_parents_size:           -1
% 3.19/1.05  bmc1_merge_next_fun:                    0
% 3.19/1.05  bmc1_unsat_core_clauses_time:           0.
% 3.19/1.05  
% 3.19/1.05  ------ Instantiation
% 3.19/1.05  
% 3.19/1.05  inst_num_of_clauses:                    1118
% 3.19/1.05  inst_num_in_passive:                    320
% 3.19/1.05  inst_num_in_active:                     522
% 3.19/1.05  inst_num_in_unprocessed:                276
% 3.19/1.05  inst_num_of_loops:                      530
% 3.19/1.05  inst_num_of_learning_restarts:          0
% 3.19/1.05  inst_num_moves_active_passive:          6
% 3.19/1.05  inst_lit_activity:                      0
% 3.19/1.05  inst_lit_activity_moves:                1
% 3.19/1.05  inst_num_tautologies:                   0
% 3.19/1.05  inst_num_prop_implied:                  0
% 3.19/1.05  inst_num_existing_simplified:           0
% 3.19/1.05  inst_num_eq_res_simplified:             0
% 3.19/1.05  inst_num_child_elim:                    0
% 3.19/1.05  inst_num_of_dismatching_blockings:      26
% 3.19/1.05  inst_num_of_non_proper_insts:           601
% 3.19/1.05  inst_num_of_duplicates:                 0
% 3.19/1.05  inst_inst_num_from_inst_to_res:         0
% 3.19/1.05  inst_dismatching_checking_time:         0.
% 3.19/1.05  
% 3.19/1.05  ------ Resolution
% 3.19/1.05  
% 3.19/1.05  res_num_of_clauses:                     0
% 3.19/1.05  res_num_in_passive:                     0
% 3.19/1.05  res_num_in_active:                      0
% 3.19/1.05  res_num_of_loops:                       171
% 3.19/1.05  res_forward_subset_subsumed:            37
% 3.19/1.05  res_backward_subset_subsumed:           0
% 3.19/1.05  res_forward_subsumed:                   0
% 3.19/1.05  res_backward_subsumed:                  0
% 3.19/1.05  res_forward_subsumption_resolution:     2
% 3.19/1.05  res_backward_subsumption_resolution:    0
% 3.19/1.05  res_clause_to_clause_subsumption:       280
% 3.19/1.05  res_orphan_elimination:                 0
% 3.19/1.05  res_tautology_del:                      28
% 3.19/1.05  res_num_eq_res_simplified:              1
% 3.19/1.05  res_num_sel_changes:                    0
% 3.19/1.05  res_moves_from_active_to_pass:          0
% 3.19/1.05  
% 3.19/1.05  ------ Superposition
% 3.19/1.05  
% 3.19/1.05  sup_time_total:                         0.
% 3.19/1.05  sup_time_generating:                    0.
% 3.19/1.05  sup_time_sim_full:                      0.
% 3.19/1.05  sup_time_sim_immed:                     0.
% 3.19/1.05  
% 3.19/1.05  sup_num_of_clauses:                     178
% 3.19/1.05  sup_num_in_active:                      93
% 3.19/1.05  sup_num_in_passive:                     85
% 3.19/1.05  sup_num_of_loops:                       105
% 3.19/1.05  sup_fw_superposition:                   79
% 3.19/1.05  sup_bw_superposition:                   86
% 3.19/1.05  sup_immediate_simplified:               38
% 3.19/1.05  sup_given_eliminated:                   0
% 3.19/1.05  comparisons_done:                       0
% 3.19/1.05  comparisons_avoided:                    0
% 3.19/1.05  
% 3.19/1.05  ------ Simplifications
% 3.19/1.05  
% 3.19/1.05  
% 3.19/1.05  sim_fw_subset_subsumed:                 8
% 3.19/1.05  sim_bw_subset_subsumed:                 1
% 3.19/1.05  sim_fw_subsumed:                        7
% 3.19/1.05  sim_bw_subsumed:                        0
% 3.19/1.05  sim_fw_subsumption_res:                 2
% 3.19/1.05  sim_bw_subsumption_res:                 0
% 3.19/1.05  sim_tautology_del:                      0
% 3.19/1.05  sim_eq_tautology_del:                   2
% 3.19/1.05  sim_eq_res_simp:                        1
% 3.19/1.05  sim_fw_demodulated:                     7
% 3.19/1.05  sim_bw_demodulated:                     12
% 3.19/1.05  sim_light_normalised:                   17
% 3.19/1.05  sim_joinable_taut:                      0
% 3.19/1.05  sim_joinable_simp:                      0
% 3.19/1.05  sim_ac_normalised:                      0
% 3.19/1.05  sim_smt_subsumption:                    0
% 3.19/1.05  
%------------------------------------------------------------------------------
