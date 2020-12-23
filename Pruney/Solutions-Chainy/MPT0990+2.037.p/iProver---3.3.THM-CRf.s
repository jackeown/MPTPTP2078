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
% DateTime   : Thu Dec  3 12:03:04 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  184 (1559 expanded)
%              Number of clauses        :  109 ( 431 expanded)
%              Number of leaves         :   21 ( 411 expanded)
%              Depth                    :   22
%              Number of atoms          :  730 (14146 expanded)
%              Number of equality atoms :  361 (5103 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f46,f45])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f88,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1319,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1322,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1328,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5211,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1322,c_1328])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5546,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5211,c_42])).

cnf(c_5547,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5546])).

cnf(c_5558,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_5547])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1889,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2293,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1889])).

cnf(c_2525,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2293])).

cnf(c_2600,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2525])).

cnf(c_5832,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5558,c_38,c_36,c_35,c_33,c_2600])).

cnf(c_9,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_31,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_31])).

cnf(c_431,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_439,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_431,c_20])).

cnf(c_1315,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_5835,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5832,c_1315])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1331,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5861,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5832,c_1331])).

cnf(c_6880,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5835,c_39,c_41,c_42,c_44,c_5861])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1344,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6892,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6880,c_1344])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1341,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2467,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1319,c_1341])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2469,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2467,c_32])).

cnf(c_2466,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1322,c_1341])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_443,plain,
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
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_444,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_532,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_444])).

cnf(c_1314,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_1924,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1314])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_40,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_43,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2180,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1924,c_39,c_40,c_41,c_42,c_43,c_44])).

cnf(c_2472,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2466,c_2180])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1332,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4727,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1322,c_1332])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1339,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3119,plain,
    ( k8_relset_1(sK1,sK0,sK3,sK0) = k1_relset_1(sK1,sK0,sK3) ),
    inference(superposition,[status(thm)],[c_1322,c_1339])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1340,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2505,plain,
    ( k8_relset_1(sK1,sK0,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1322,c_1340])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1342,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2371,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1322,c_1342])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1347,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2439,plain,
    ( k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2371,c_1347])).

cnf(c_2680,plain,
    ( k10_relat_1(sK3,sK0) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_2439,c_2472])).

cnf(c_3125,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3119,c_2505,c_2680])).

cnf(c_4739,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4727,c_3125])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_729,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_758,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_730,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1764,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_1765,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1764])).

cnf(c_4946,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4739,c_43,c_29,c_758,c_1765])).

cnf(c_6893,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6892,c_2469,c_2472,c_4946])).

cnf(c_6894,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6893])).

cnf(c_1705,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1706,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1705])).

cnf(c_1708,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1709,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1708])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_1326,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5065,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_32,c_1326])).

cnf(c_5455,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5065,c_39,c_40,c_41])).

cnf(c_5456,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5455])).

cnf(c_5864,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5832,c_5456])).

cnf(c_6394,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5864,c_42,c_43,c_44,c_29,c_758,c_1765])).

cnf(c_6883,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6880,c_6394])).

cnf(c_1,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1346,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7198,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6883,c_1346])).

cnf(c_8411,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6894,c_39,c_41,c_42,c_44,c_1706,c_1709,c_7198])).

cnf(c_1320,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1343,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3176,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1320,c_1343])).

cnf(c_1738,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1739,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1738])).

cnf(c_3193,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3176,c_42,c_44,c_1706,c_1739])).

cnf(c_3194,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3193])).

cnf(c_7200,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_7198,c_3194])).

cnf(c_8414,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_8411,c_7200])).

cnf(c_27,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8414,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.39/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/1.00  
% 3.39/1.00  ------  iProver source info
% 3.39/1.00  
% 3.39/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.39/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/1.00  git: non_committed_changes: false
% 3.39/1.00  git: last_make_outside_of_git: false
% 3.39/1.00  
% 3.39/1.00  ------ 
% 3.39/1.00  
% 3.39/1.00  ------ Input Options
% 3.39/1.00  
% 3.39/1.00  --out_options                           all
% 3.39/1.00  --tptp_safe_out                         true
% 3.39/1.00  --problem_path                          ""
% 3.39/1.00  --include_path                          ""
% 3.39/1.00  --clausifier                            res/vclausify_rel
% 3.39/1.00  --clausifier_options                    --mode clausify
% 3.39/1.00  --stdin                                 false
% 3.39/1.00  --stats_out                             all
% 3.39/1.00  
% 3.39/1.00  ------ General Options
% 3.39/1.00  
% 3.39/1.00  --fof                                   false
% 3.39/1.00  --time_out_real                         305.
% 3.39/1.00  --time_out_virtual                      -1.
% 3.39/1.00  --symbol_type_check                     false
% 3.39/1.00  --clausify_out                          false
% 3.39/1.00  --sig_cnt_out                           false
% 3.39/1.00  --trig_cnt_out                          false
% 3.39/1.00  --trig_cnt_out_tolerance                1.
% 3.39/1.00  --trig_cnt_out_sk_spl                   false
% 3.39/1.00  --abstr_cl_out                          false
% 3.39/1.00  
% 3.39/1.00  ------ Global Options
% 3.39/1.00  
% 3.39/1.00  --schedule                              default
% 3.39/1.00  --add_important_lit                     false
% 3.39/1.00  --prop_solver_per_cl                    1000
% 3.39/1.00  --min_unsat_core                        false
% 3.39/1.00  --soft_assumptions                      false
% 3.39/1.00  --soft_lemma_size                       3
% 3.39/1.00  --prop_impl_unit_size                   0
% 3.39/1.00  --prop_impl_unit                        []
% 3.39/1.00  --share_sel_clauses                     true
% 3.39/1.00  --reset_solvers                         false
% 3.39/1.00  --bc_imp_inh                            [conj_cone]
% 3.39/1.00  --conj_cone_tolerance                   3.
% 3.39/1.00  --extra_neg_conj                        none
% 3.39/1.00  --large_theory_mode                     true
% 3.39/1.00  --prolific_symb_bound                   200
% 3.39/1.00  --lt_threshold                          2000
% 3.39/1.00  --clause_weak_htbl                      true
% 3.39/1.00  --gc_record_bc_elim                     false
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing Options
% 3.39/1.00  
% 3.39/1.00  --preprocessing_flag                    true
% 3.39/1.00  --time_out_prep_mult                    0.1
% 3.39/1.00  --splitting_mode                        input
% 3.39/1.00  --splitting_grd                         true
% 3.39/1.00  --splitting_cvd                         false
% 3.39/1.00  --splitting_cvd_svl                     false
% 3.39/1.00  --splitting_nvd                         32
% 3.39/1.00  --sub_typing                            true
% 3.39/1.00  --prep_gs_sim                           true
% 3.39/1.00  --prep_unflatten                        true
% 3.39/1.00  --prep_res_sim                          true
% 3.39/1.00  --prep_upred                            true
% 3.39/1.00  --prep_sem_filter                       exhaustive
% 3.39/1.00  --prep_sem_filter_out                   false
% 3.39/1.00  --pred_elim                             true
% 3.39/1.00  --res_sim_input                         true
% 3.39/1.00  --eq_ax_congr_red                       true
% 3.39/1.00  --pure_diseq_elim                       true
% 3.39/1.00  --brand_transform                       false
% 3.39/1.00  --non_eq_to_eq                          false
% 3.39/1.00  --prep_def_merge                        true
% 3.39/1.00  --prep_def_merge_prop_impl              false
% 3.39/1.00  --prep_def_merge_mbd                    true
% 3.39/1.00  --prep_def_merge_tr_red                 false
% 3.39/1.00  --prep_def_merge_tr_cl                  false
% 3.39/1.00  --smt_preprocessing                     true
% 3.39/1.00  --smt_ac_axioms                         fast
% 3.39/1.00  --preprocessed_out                      false
% 3.39/1.00  --preprocessed_stats                    false
% 3.39/1.00  
% 3.39/1.00  ------ Abstraction refinement Options
% 3.39/1.00  
% 3.39/1.00  --abstr_ref                             []
% 3.39/1.00  --abstr_ref_prep                        false
% 3.39/1.00  --abstr_ref_until_sat                   false
% 3.39/1.00  --abstr_ref_sig_restrict                funpre
% 3.39/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/1.00  --abstr_ref_under                       []
% 3.39/1.00  
% 3.39/1.00  ------ SAT Options
% 3.39/1.00  
% 3.39/1.00  --sat_mode                              false
% 3.39/1.00  --sat_fm_restart_options                ""
% 3.39/1.00  --sat_gr_def                            false
% 3.39/1.00  --sat_epr_types                         true
% 3.39/1.00  --sat_non_cyclic_types                  false
% 3.39/1.00  --sat_finite_models                     false
% 3.39/1.00  --sat_fm_lemmas                         false
% 3.39/1.00  --sat_fm_prep                           false
% 3.39/1.00  --sat_fm_uc_incr                        true
% 3.39/1.00  --sat_out_model                         small
% 3.39/1.00  --sat_out_clauses                       false
% 3.39/1.00  
% 3.39/1.00  ------ QBF Options
% 3.39/1.00  
% 3.39/1.00  --qbf_mode                              false
% 3.39/1.00  --qbf_elim_univ                         false
% 3.39/1.00  --qbf_dom_inst                          none
% 3.39/1.00  --qbf_dom_pre_inst                      false
% 3.39/1.00  --qbf_sk_in                             false
% 3.39/1.00  --qbf_pred_elim                         true
% 3.39/1.00  --qbf_split                             512
% 3.39/1.00  
% 3.39/1.00  ------ BMC1 Options
% 3.39/1.00  
% 3.39/1.00  --bmc1_incremental                      false
% 3.39/1.00  --bmc1_axioms                           reachable_all
% 3.39/1.00  --bmc1_min_bound                        0
% 3.39/1.00  --bmc1_max_bound                        -1
% 3.39/1.00  --bmc1_max_bound_default                -1
% 3.39/1.00  --bmc1_symbol_reachability              true
% 3.39/1.00  --bmc1_property_lemmas                  false
% 3.39/1.00  --bmc1_k_induction                      false
% 3.39/1.00  --bmc1_non_equiv_states                 false
% 3.39/1.00  --bmc1_deadlock                         false
% 3.39/1.00  --bmc1_ucm                              false
% 3.39/1.00  --bmc1_add_unsat_core                   none
% 3.39/1.00  --bmc1_unsat_core_children              false
% 3.39/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/1.00  --bmc1_out_stat                         full
% 3.39/1.00  --bmc1_ground_init                      false
% 3.39/1.00  --bmc1_pre_inst_next_state              false
% 3.39/1.00  --bmc1_pre_inst_state                   false
% 3.39/1.00  --bmc1_pre_inst_reach_state             false
% 3.39/1.00  --bmc1_out_unsat_core                   false
% 3.39/1.00  --bmc1_aig_witness_out                  false
% 3.39/1.00  --bmc1_verbose                          false
% 3.39/1.00  --bmc1_dump_clauses_tptp                false
% 3.39/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.39/1.00  --bmc1_dump_file                        -
% 3.39/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.39/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.39/1.00  --bmc1_ucm_extend_mode                  1
% 3.39/1.00  --bmc1_ucm_init_mode                    2
% 3.39/1.00  --bmc1_ucm_cone_mode                    none
% 3.39/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.39/1.00  --bmc1_ucm_relax_model                  4
% 3.39/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.39/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/1.00  --bmc1_ucm_layered_model                none
% 3.39/1.00  --bmc1_ucm_max_lemma_size               10
% 3.39/1.00  
% 3.39/1.00  ------ AIG Options
% 3.39/1.00  
% 3.39/1.00  --aig_mode                              false
% 3.39/1.00  
% 3.39/1.00  ------ Instantiation Options
% 3.39/1.00  
% 3.39/1.00  --instantiation_flag                    true
% 3.39/1.00  --inst_sos_flag                         false
% 3.39/1.00  --inst_sos_phase                        true
% 3.39/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel_side                     num_symb
% 3.39/1.00  --inst_solver_per_active                1400
% 3.39/1.00  --inst_solver_calls_frac                1.
% 3.39/1.00  --inst_passive_queue_type               priority_queues
% 3.39/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/1.00  --inst_passive_queues_freq              [25;2]
% 3.39/1.00  --inst_dismatching                      true
% 3.39/1.00  --inst_eager_unprocessed_to_passive     true
% 3.39/1.00  --inst_prop_sim_given                   true
% 3.39/1.00  --inst_prop_sim_new                     false
% 3.39/1.00  --inst_subs_new                         false
% 3.39/1.00  --inst_eq_res_simp                      false
% 3.39/1.00  --inst_subs_given                       false
% 3.39/1.00  --inst_orphan_elimination               true
% 3.39/1.00  --inst_learning_loop_flag               true
% 3.39/1.00  --inst_learning_start                   3000
% 3.39/1.00  --inst_learning_factor                  2
% 3.39/1.00  --inst_start_prop_sim_after_learn       3
% 3.39/1.00  --inst_sel_renew                        solver
% 3.39/1.00  --inst_lit_activity_flag                true
% 3.39/1.00  --inst_restr_to_given                   false
% 3.39/1.00  --inst_activity_threshold               500
% 3.39/1.00  --inst_out_proof                        true
% 3.39/1.00  
% 3.39/1.00  ------ Resolution Options
% 3.39/1.00  
% 3.39/1.00  --resolution_flag                       true
% 3.39/1.00  --res_lit_sel                           adaptive
% 3.39/1.00  --res_lit_sel_side                      none
% 3.39/1.00  --res_ordering                          kbo
% 3.39/1.00  --res_to_prop_solver                    active
% 3.39/1.00  --res_prop_simpl_new                    false
% 3.39/1.00  --res_prop_simpl_given                  true
% 3.39/1.00  --res_passive_queue_type                priority_queues
% 3.39/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/1.00  --res_passive_queues_freq               [15;5]
% 3.39/1.00  --res_forward_subs                      full
% 3.39/1.00  --res_backward_subs                     full
% 3.39/1.00  --res_forward_subs_resolution           true
% 3.39/1.00  --res_backward_subs_resolution          true
% 3.39/1.00  --res_orphan_elimination                true
% 3.39/1.00  --res_time_limit                        2.
% 3.39/1.00  --res_out_proof                         true
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Options
% 3.39/1.00  
% 3.39/1.00  --superposition_flag                    true
% 3.39/1.00  --sup_passive_queue_type                priority_queues
% 3.39/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.39/1.00  --demod_completeness_check              fast
% 3.39/1.00  --demod_use_ground                      true
% 3.39/1.00  --sup_to_prop_solver                    passive
% 3.39/1.00  --sup_prop_simpl_new                    true
% 3.39/1.00  --sup_prop_simpl_given                  true
% 3.39/1.00  --sup_fun_splitting                     false
% 3.39/1.00  --sup_smt_interval                      50000
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Simplification Setup
% 3.39/1.00  
% 3.39/1.00  --sup_indices_passive                   []
% 3.39/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_full_bw                           [BwDemod]
% 3.39/1.00  --sup_immed_triv                        [TrivRules]
% 3.39/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_immed_bw_main                     []
% 3.39/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/1.00  
% 3.39/1.00  ------ Combination Options
% 3.39/1.00  
% 3.39/1.00  --comb_res_mult                         3
% 3.39/1.00  --comb_sup_mult                         2
% 3.39/1.00  --comb_inst_mult                        10
% 3.39/1.00  
% 3.39/1.00  ------ Debug Options
% 3.39/1.00  
% 3.39/1.00  --dbg_backtrace                         false
% 3.39/1.00  --dbg_dump_prop_clauses                 false
% 3.39/1.00  --dbg_dump_prop_clauses_file            -
% 3.39/1.00  --dbg_out_stat                          false
% 3.39/1.00  ------ Parsing...
% 3.39/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.00  ------ Proving...
% 3.39/1.00  ------ Problem Properties 
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  clauses                                 38
% 3.39/1.00  conjectures                             11
% 3.39/1.00  EPR                                     7
% 3.39/1.00  Horn                                    32
% 3.39/1.00  unary                                   14
% 3.39/1.00  binary                                  7
% 3.39/1.00  lits                                    130
% 3.39/1.00  lits eq                                 34
% 3.39/1.00  fd_pure                                 0
% 3.39/1.00  fd_pseudo                               0
% 3.39/1.00  fd_cond                                 5
% 3.39/1.00  fd_pseudo_cond                          1
% 3.39/1.00  AC symbols                              0
% 3.39/1.00  
% 3.39/1.00  ------ Schedule dynamic 5 is on 
% 3.39/1.00  
% 3.39/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  ------ 
% 3.39/1.00  Current options:
% 3.39/1.00  ------ 
% 3.39/1.00  
% 3.39/1.00  ------ Input Options
% 3.39/1.00  
% 3.39/1.00  --out_options                           all
% 3.39/1.00  --tptp_safe_out                         true
% 3.39/1.00  --problem_path                          ""
% 3.39/1.00  --include_path                          ""
% 3.39/1.00  --clausifier                            res/vclausify_rel
% 3.39/1.00  --clausifier_options                    --mode clausify
% 3.39/1.00  --stdin                                 false
% 3.39/1.00  --stats_out                             all
% 3.39/1.00  
% 3.39/1.00  ------ General Options
% 3.39/1.00  
% 3.39/1.00  --fof                                   false
% 3.39/1.00  --time_out_real                         305.
% 3.39/1.00  --time_out_virtual                      -1.
% 3.39/1.00  --symbol_type_check                     false
% 3.39/1.00  --clausify_out                          false
% 3.39/1.00  --sig_cnt_out                           false
% 3.39/1.00  --trig_cnt_out                          false
% 3.39/1.00  --trig_cnt_out_tolerance                1.
% 3.39/1.00  --trig_cnt_out_sk_spl                   false
% 3.39/1.00  --abstr_cl_out                          false
% 3.39/1.00  
% 3.39/1.00  ------ Global Options
% 3.39/1.00  
% 3.39/1.00  --schedule                              default
% 3.39/1.00  --add_important_lit                     false
% 3.39/1.00  --prop_solver_per_cl                    1000
% 3.39/1.00  --min_unsat_core                        false
% 3.39/1.00  --soft_assumptions                      false
% 3.39/1.00  --soft_lemma_size                       3
% 3.39/1.00  --prop_impl_unit_size                   0
% 3.39/1.00  --prop_impl_unit                        []
% 3.39/1.00  --share_sel_clauses                     true
% 3.39/1.00  --reset_solvers                         false
% 3.39/1.00  --bc_imp_inh                            [conj_cone]
% 3.39/1.00  --conj_cone_tolerance                   3.
% 3.39/1.00  --extra_neg_conj                        none
% 3.39/1.00  --large_theory_mode                     true
% 3.39/1.00  --prolific_symb_bound                   200
% 3.39/1.00  --lt_threshold                          2000
% 3.39/1.00  --clause_weak_htbl                      true
% 3.39/1.00  --gc_record_bc_elim                     false
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing Options
% 3.39/1.00  
% 3.39/1.00  --preprocessing_flag                    true
% 3.39/1.00  --time_out_prep_mult                    0.1
% 3.39/1.00  --splitting_mode                        input
% 3.39/1.00  --splitting_grd                         true
% 3.39/1.00  --splitting_cvd                         false
% 3.39/1.00  --splitting_cvd_svl                     false
% 3.39/1.00  --splitting_nvd                         32
% 3.39/1.00  --sub_typing                            true
% 3.39/1.00  --prep_gs_sim                           true
% 3.39/1.00  --prep_unflatten                        true
% 3.39/1.00  --prep_res_sim                          true
% 3.39/1.00  --prep_upred                            true
% 3.39/1.00  --prep_sem_filter                       exhaustive
% 3.39/1.00  --prep_sem_filter_out                   false
% 3.39/1.00  --pred_elim                             true
% 3.39/1.00  --res_sim_input                         true
% 3.39/1.00  --eq_ax_congr_red                       true
% 3.39/1.00  --pure_diseq_elim                       true
% 3.39/1.00  --brand_transform                       false
% 3.39/1.00  --non_eq_to_eq                          false
% 3.39/1.00  --prep_def_merge                        true
% 3.39/1.00  --prep_def_merge_prop_impl              false
% 3.39/1.00  --prep_def_merge_mbd                    true
% 3.39/1.00  --prep_def_merge_tr_red                 false
% 3.39/1.00  --prep_def_merge_tr_cl                  false
% 3.39/1.00  --smt_preprocessing                     true
% 3.39/1.00  --smt_ac_axioms                         fast
% 3.39/1.00  --preprocessed_out                      false
% 3.39/1.00  --preprocessed_stats                    false
% 3.39/1.00  
% 3.39/1.00  ------ Abstraction refinement Options
% 3.39/1.00  
% 3.39/1.00  --abstr_ref                             []
% 3.39/1.00  --abstr_ref_prep                        false
% 3.39/1.00  --abstr_ref_until_sat                   false
% 3.39/1.00  --abstr_ref_sig_restrict                funpre
% 3.39/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/1.00  --abstr_ref_under                       []
% 3.39/1.00  
% 3.39/1.00  ------ SAT Options
% 3.39/1.00  
% 3.39/1.00  --sat_mode                              false
% 3.39/1.00  --sat_fm_restart_options                ""
% 3.39/1.00  --sat_gr_def                            false
% 3.39/1.00  --sat_epr_types                         true
% 3.39/1.00  --sat_non_cyclic_types                  false
% 3.39/1.00  --sat_finite_models                     false
% 3.39/1.00  --sat_fm_lemmas                         false
% 3.39/1.00  --sat_fm_prep                           false
% 3.39/1.00  --sat_fm_uc_incr                        true
% 3.39/1.00  --sat_out_model                         small
% 3.39/1.00  --sat_out_clauses                       false
% 3.39/1.00  
% 3.39/1.00  ------ QBF Options
% 3.39/1.00  
% 3.39/1.00  --qbf_mode                              false
% 3.39/1.00  --qbf_elim_univ                         false
% 3.39/1.00  --qbf_dom_inst                          none
% 3.39/1.00  --qbf_dom_pre_inst                      false
% 3.39/1.00  --qbf_sk_in                             false
% 3.39/1.00  --qbf_pred_elim                         true
% 3.39/1.00  --qbf_split                             512
% 3.39/1.00  
% 3.39/1.00  ------ BMC1 Options
% 3.39/1.00  
% 3.39/1.00  --bmc1_incremental                      false
% 3.39/1.00  --bmc1_axioms                           reachable_all
% 3.39/1.00  --bmc1_min_bound                        0
% 3.39/1.00  --bmc1_max_bound                        -1
% 3.39/1.00  --bmc1_max_bound_default                -1
% 3.39/1.00  --bmc1_symbol_reachability              true
% 3.39/1.00  --bmc1_property_lemmas                  false
% 3.39/1.00  --bmc1_k_induction                      false
% 3.39/1.00  --bmc1_non_equiv_states                 false
% 3.39/1.00  --bmc1_deadlock                         false
% 3.39/1.00  --bmc1_ucm                              false
% 3.39/1.00  --bmc1_add_unsat_core                   none
% 3.39/1.00  --bmc1_unsat_core_children              false
% 3.39/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/1.00  --bmc1_out_stat                         full
% 3.39/1.00  --bmc1_ground_init                      false
% 3.39/1.00  --bmc1_pre_inst_next_state              false
% 3.39/1.00  --bmc1_pre_inst_state                   false
% 3.39/1.00  --bmc1_pre_inst_reach_state             false
% 3.39/1.00  --bmc1_out_unsat_core                   false
% 3.39/1.00  --bmc1_aig_witness_out                  false
% 3.39/1.00  --bmc1_verbose                          false
% 3.39/1.00  --bmc1_dump_clauses_tptp                false
% 3.39/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.39/1.00  --bmc1_dump_file                        -
% 3.39/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.39/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.39/1.00  --bmc1_ucm_extend_mode                  1
% 3.39/1.00  --bmc1_ucm_init_mode                    2
% 3.39/1.00  --bmc1_ucm_cone_mode                    none
% 3.39/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.39/1.00  --bmc1_ucm_relax_model                  4
% 3.39/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.39/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/1.00  --bmc1_ucm_layered_model                none
% 3.39/1.00  --bmc1_ucm_max_lemma_size               10
% 3.39/1.00  
% 3.39/1.00  ------ AIG Options
% 3.39/1.00  
% 3.39/1.00  --aig_mode                              false
% 3.39/1.00  
% 3.39/1.00  ------ Instantiation Options
% 3.39/1.00  
% 3.39/1.00  --instantiation_flag                    true
% 3.39/1.00  --inst_sos_flag                         false
% 3.39/1.00  --inst_sos_phase                        true
% 3.39/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel_side                     none
% 3.39/1.00  --inst_solver_per_active                1400
% 3.39/1.00  --inst_solver_calls_frac                1.
% 3.39/1.00  --inst_passive_queue_type               priority_queues
% 3.39/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/1.00  --inst_passive_queues_freq              [25;2]
% 3.39/1.00  --inst_dismatching                      true
% 3.39/1.00  --inst_eager_unprocessed_to_passive     true
% 3.39/1.00  --inst_prop_sim_given                   true
% 3.39/1.00  --inst_prop_sim_new                     false
% 3.39/1.00  --inst_subs_new                         false
% 3.39/1.00  --inst_eq_res_simp                      false
% 3.39/1.00  --inst_subs_given                       false
% 3.39/1.00  --inst_orphan_elimination               true
% 3.39/1.00  --inst_learning_loop_flag               true
% 3.39/1.00  --inst_learning_start                   3000
% 3.39/1.00  --inst_learning_factor                  2
% 3.39/1.00  --inst_start_prop_sim_after_learn       3
% 3.39/1.00  --inst_sel_renew                        solver
% 3.39/1.00  --inst_lit_activity_flag                true
% 3.39/1.00  --inst_restr_to_given                   false
% 3.39/1.00  --inst_activity_threshold               500
% 3.39/1.00  --inst_out_proof                        true
% 3.39/1.00  
% 3.39/1.00  ------ Resolution Options
% 3.39/1.00  
% 3.39/1.00  --resolution_flag                       false
% 3.39/1.00  --res_lit_sel                           adaptive
% 3.39/1.00  --res_lit_sel_side                      none
% 3.39/1.00  --res_ordering                          kbo
% 3.39/1.00  --res_to_prop_solver                    active
% 3.39/1.00  --res_prop_simpl_new                    false
% 3.39/1.00  --res_prop_simpl_given                  true
% 3.39/1.00  --res_passive_queue_type                priority_queues
% 3.39/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/1.00  --res_passive_queues_freq               [15;5]
% 3.39/1.00  --res_forward_subs                      full
% 3.39/1.00  --res_backward_subs                     full
% 3.39/1.00  --res_forward_subs_resolution           true
% 3.39/1.00  --res_backward_subs_resolution          true
% 3.39/1.00  --res_orphan_elimination                true
% 3.39/1.00  --res_time_limit                        2.
% 3.39/1.00  --res_out_proof                         true
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Options
% 3.39/1.00  
% 3.39/1.00  --superposition_flag                    true
% 3.39/1.00  --sup_passive_queue_type                priority_queues
% 3.39/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.39/1.00  --demod_completeness_check              fast
% 3.39/1.00  --demod_use_ground                      true
% 3.39/1.00  --sup_to_prop_solver                    passive
% 3.39/1.00  --sup_prop_simpl_new                    true
% 3.39/1.00  --sup_prop_simpl_given                  true
% 3.39/1.00  --sup_fun_splitting                     false
% 3.39/1.00  --sup_smt_interval                      50000
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Simplification Setup
% 3.39/1.00  
% 3.39/1.00  --sup_indices_passive                   []
% 3.39/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_full_bw                           [BwDemod]
% 3.39/1.00  --sup_immed_triv                        [TrivRules]
% 3.39/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_immed_bw_main                     []
% 3.39/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/1.00  
% 3.39/1.00  ------ Combination Options
% 3.39/1.00  
% 3.39/1.00  --comb_res_mult                         3
% 3.39/1.00  --comb_sup_mult                         2
% 3.39/1.00  --comb_inst_mult                        10
% 3.39/1.00  
% 3.39/1.00  ------ Debug Options
% 3.39/1.00  
% 3.39/1.00  --dbg_backtrace                         false
% 3.39/1.00  --dbg_dump_prop_clauses                 false
% 3.39/1.00  --dbg_dump_prop_clauses_file            -
% 3.39/1.00  --dbg_out_stat                          false
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  ------ Proving...
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  % SZS status Theorem for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  fof(f17,conjecture,(
% 3.39/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f18,negated_conjecture,(
% 3.39/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.39/1.00    inference(negated_conjecture,[],[f17])).
% 3.39/1.00  
% 3.39/1.00  fof(f41,plain,(
% 3.39/1.00    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.39/1.00    inference(ennf_transformation,[],[f18])).
% 3.39/1.00  
% 3.39/1.00  fof(f42,plain,(
% 3.39/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.39/1.00    inference(flattening,[],[f41])).
% 3.39/1.00  
% 3.39/1.00  fof(f46,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f45,plain,(
% 3.39/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f47,plain,(
% 3.39/1.00    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f46,f45])).
% 3.39/1.00  
% 3.39/1.00  fof(f78,plain,(
% 3.39/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f81,plain,(
% 3.39/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f13,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f35,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.39/1.00    inference(ennf_transformation,[],[f13])).
% 3.39/1.00  
% 3.39/1.00  fof(f36,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.39/1.00    inference(flattening,[],[f35])).
% 3.39/1.00  
% 3.39/1.00  fof(f69,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f36])).
% 3.39/1.00  
% 3.39/1.00  fof(f79,plain,(
% 3.39/1.00    v1_funct_1(sK3)),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f76,plain,(
% 3.39/1.00    v1_funct_1(sK2)),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f8,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f28,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.39/1.00    inference(ennf_transformation,[],[f8])).
% 3.39/1.00  
% 3.39/1.00  fof(f29,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(flattening,[],[f28])).
% 3.39/1.00  
% 3.39/1.00  fof(f43,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(nnf_transformation,[],[f29])).
% 3.39/1.00  
% 3.39/1.00  fof(f56,plain,(
% 3.39/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f43])).
% 3.39/1.00  
% 3.39/1.00  fof(f83,plain,(
% 3.39/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f12,axiom,(
% 3.39/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f19,plain,(
% 3.39/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.39/1.00    inference(pure_predicate_removal,[],[f12])).
% 3.39/1.00  
% 3.39/1.00  fof(f68,plain,(
% 3.39/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f19])).
% 3.39/1.00  
% 3.39/1.00  fof(f11,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f33,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.39/1.00    inference(ennf_transformation,[],[f11])).
% 3.39/1.00  
% 3.39/1.00  fof(f34,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.39/1.00    inference(flattening,[],[f33])).
% 3.39/1.00  
% 3.39/1.00  fof(f67,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f34])).
% 3.39/1.00  
% 3.39/1.00  fof(f3,axiom,(
% 3.39/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f21,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f3])).
% 3.39/1.00  
% 3.39/1.00  fof(f22,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.39/1.00    inference(flattening,[],[f21])).
% 3.39/1.00  
% 3.39/1.00  fof(f51,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f22])).
% 3.39/1.00  
% 3.39/1.00  fof(f14,axiom,(
% 3.39/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f70,plain,(
% 3.39/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f14])).
% 3.39/1.00  
% 3.39/1.00  fof(f90,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/1.00    inference(definition_unfolding,[],[f51,f70])).
% 3.39/1.00  
% 3.39/1.00  fof(f6,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f26,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f6])).
% 3.39/1.00  
% 3.39/1.00  fof(f54,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f26])).
% 3.39/1.00  
% 3.39/1.00  fof(f82,plain,(
% 3.39/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f15,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f37,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.39/1.00    inference(ennf_transformation,[],[f15])).
% 3.39/1.00  
% 3.39/1.00  fof(f38,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.39/1.00    inference(flattening,[],[f37])).
% 3.39/1.00  
% 3.39/1.00  fof(f71,plain,(
% 3.39/1.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f38])).
% 3.39/1.00  
% 3.39/1.00  fof(f77,plain,(
% 3.39/1.00    v1_funct_2(sK2,sK0,sK1)),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f80,plain,(
% 3.39/1.00    v1_funct_2(sK3,sK1,sK0)),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f10,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f31,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f10])).
% 3.39/1.00  
% 3.39/1.00  fof(f32,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(flattening,[],[f31])).
% 3.39/1.00  
% 3.39/1.00  fof(f44,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(nnf_transformation,[],[f32])).
% 3.39/1.00  
% 3.39/1.00  fof(f60,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f44])).
% 3.39/1.00  
% 3.39/1.00  fof(f9,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f30,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f9])).
% 3.39/1.00  
% 3.39/1.00  fof(f59,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f30])).
% 3.39/1.00  
% 3.39/1.00  fof(f7,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f27,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f7])).
% 3.39/1.00  
% 3.39/1.00  fof(f55,plain,(
% 3.39/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f27])).
% 3.39/1.00  
% 3.39/1.00  fof(f5,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f25,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f5])).
% 3.39/1.00  
% 3.39/1.00  fof(f53,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f25])).
% 3.39/1.00  
% 3.39/1.00  fof(f1,axiom,(
% 3.39/1.00    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f20,plain,(
% 3.39/1.00    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.39/1.00    inference(ennf_transformation,[],[f1])).
% 3.39/1.00  
% 3.39/1.00  fof(f48,plain,(
% 3.39/1.00    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f20])).
% 3.39/1.00  
% 3.39/1.00  fof(f85,plain,(
% 3.39/1.00    k1_xboole_0 != sK0),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f16,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f39,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.39/1.00    inference(ennf_transformation,[],[f16])).
% 3.39/1.00  
% 3.39/1.00  fof(f40,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.39/1.00    inference(flattening,[],[f39])).
% 3.39/1.00  
% 3.39/1.00  fof(f74,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f40])).
% 3.39/1.00  
% 3.39/1.00  fof(f2,axiom,(
% 3.39/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f50,plain,(
% 3.39/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f2])).
% 3.39/1.00  
% 3.39/1.00  fof(f88,plain,(
% 3.39/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.39/1.00    inference(definition_unfolding,[],[f50,f70])).
% 3.39/1.00  
% 3.39/1.00  fof(f4,axiom,(
% 3.39/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f23,plain,(
% 3.39/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f4])).
% 3.39/1.00  
% 3.39/1.00  fof(f24,plain,(
% 3.39/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.39/1.00    inference(flattening,[],[f23])).
% 3.39/1.00  
% 3.39/1.00  fof(f52,plain,(
% 3.39/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f24])).
% 3.39/1.00  
% 3.39/1.00  fof(f87,plain,(
% 3.39/1.00    k2_funct_1(sK2) != sK3),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  cnf(c_36,negated_conjecture,
% 3.39/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1319,plain,
% 3.39/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_33,negated_conjecture,
% 3.39/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1322,plain,
% 3.39/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_21,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | ~ v1_funct_1(X3)
% 3.39/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1328,plain,
% 3.39/1.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.39/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.39/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.39/1.00      | v1_funct_1(X5) != iProver_top
% 3.39/1.00      | v1_funct_1(X4) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5211,plain,
% 3.39/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.39/1.00      | v1_funct_1(X2) != iProver_top
% 3.39/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1322,c_1328]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_35,negated_conjecture,
% 3.39/1.00      ( v1_funct_1(sK3) ),
% 3.39/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_42,plain,
% 3.39/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5546,plain,
% 3.39/1.00      ( v1_funct_1(X2) != iProver_top
% 3.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.39/1.00      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_5211,c_42]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5547,plain,
% 3.39/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.39/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_5546]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5558,plain,
% 3.39/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.39/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1319,c_5547]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_38,negated_conjecture,
% 3.39/1.00      ( v1_funct_1(sK2) ),
% 3.39/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1889,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | ~ v1_funct_1(sK3)
% 3.39/1.00      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2293,plain,
% 3.39/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.39/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.39/1.00      | ~ v1_funct_1(sK3)
% 3.39/1.00      | ~ v1_funct_1(sK2)
% 3.39/1.00      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_1889]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2525,plain,
% 3.39/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.39/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.39/1.00      | ~ v1_funct_1(sK3)
% 3.39/1.00      | ~ v1_funct_1(sK2)
% 3.39/1.00      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_2293]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2600,plain,
% 3.39/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.39/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.39/1.00      | ~ v1_funct_1(sK3)
% 3.39/1.00      | ~ v1_funct_1(sK2)
% 3.39/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_2525]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5832,plain,
% 3.39/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_5558,c_38,c_36,c_35,c_33,c_2600]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9,plain,
% 3.39/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.39/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.39/1.00      | X3 = X2 ),
% 3.39/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_31,negated_conjecture,
% 3.39/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.39/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_430,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | X3 = X0
% 3.39/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.39/1.00      | k6_partfun1(sK0) != X3
% 3.39/1.00      | sK0 != X2
% 3.39/1.00      | sK0 != X1 ),
% 3.39/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_31]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_431,plain,
% 3.39/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.39/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.39/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.39/1.00      inference(unflattening,[status(thm)],[c_430]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_20,plain,
% 3.39/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_439,plain,
% 3.39/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.39/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.39/1.00      inference(forward_subsumption_resolution,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_431,c_20]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1315,plain,
% 3.39/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.39/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5835,plain,
% 3.39/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.39/1.00      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_5832,c_1315]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_39,plain,
% 3.39/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_41,plain,
% 3.39/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_44,plain,
% 3.39/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_18,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.39/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | ~ v1_funct_1(X3) ),
% 3.39/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1331,plain,
% 3.39/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.39/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.39/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.39/1.00      | v1_funct_1(X0) != iProver_top
% 3.39/1.00      | v1_funct_1(X3) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5861,plain,
% 3.39/1.00      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.39/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.39/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.39/1.00      | v1_funct_1(sK3) != iProver_top
% 3.39/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_5832,c_1331]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6880,plain,
% 3.39/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_5835,c_39,c_41,c_42,c_44,c_5861]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3,plain,
% 3.39/1.00      ( ~ v1_funct_1(X0)
% 3.39/1.00      | ~ v1_funct_1(X1)
% 3.39/1.00      | ~ v2_funct_1(X1)
% 3.39/1.00      | ~ v1_relat_1(X1)
% 3.39/1.00      | ~ v1_relat_1(X0)
% 3.39/1.00      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.39/1.00      | k2_funct_1(X1) = X0
% 3.39/1.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1344,plain,
% 3.39/1.00      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.39/1.00      | k2_funct_1(X1) = X0
% 3.39/1.00      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.39/1.00      | v1_funct_1(X0) != iProver_top
% 3.39/1.00      | v1_funct_1(X1) != iProver_top
% 3.39/1.00      | v2_funct_1(X1) != iProver_top
% 3.39/1.00      | v1_relat_1(X0) != iProver_top
% 3.39/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6892,plain,
% 3.39/1.00      ( k2_funct_1(sK3) = sK2
% 3.39/1.00      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 3.39/1.00      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 3.39/1.00      | v1_funct_1(sK3) != iProver_top
% 3.39/1.00      | v1_funct_1(sK2) != iProver_top
% 3.39/1.00      | v2_funct_1(sK3) != iProver_top
% 3.39/1.00      | v1_relat_1(sK3) != iProver_top
% 3.39/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_6880,c_1344]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1341,plain,
% 3.39/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2467,plain,
% 3.39/1.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1319,c_1341]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_32,negated_conjecture,
% 3.39/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.39/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2469,plain,
% 3.39/1.00      ( k2_relat_1(sK2) = sK1 ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_2467,c_32]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2466,plain,
% 3.39/1.00      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1322,c_1341]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_22,plain,
% 3.39/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.39/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.39/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.39/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.39/1.00      | ~ v1_funct_1(X2)
% 3.39/1.00      | ~ v1_funct_1(X3)
% 3.39/1.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.39/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_443,plain,
% 3.39/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.39/1.00      | ~ v1_funct_2(X3,X2,X1)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.39/1.00      | ~ v1_funct_1(X3)
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.39/1.00      | k2_relset_1(X2,X1,X3) = X1
% 3.39/1.00      | k6_partfun1(X1) != k6_partfun1(sK0)
% 3.39/1.00      | sK0 != X1 ),
% 3.39/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_444,plain,
% 3.39/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 3.39/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.39/1.00      | ~ v1_funct_1(X2)
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.39/1.00      | k2_relset_1(X1,sK0,X0) = sK0
% 3.39/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.39/1.00      inference(unflattening,[status(thm)],[c_443]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_532,plain,
% 3.39/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 3.39/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | ~ v1_funct_1(X2)
% 3.39/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.39/1.00      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.39/1.00      inference(equality_resolution_simp,[status(thm)],[c_444]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1314,plain,
% 3.39/1.00      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.39/1.00      | k2_relset_1(X0,sK0,X2) = sK0
% 3.39/1.00      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.39/1.00      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.39/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.39/1.00      | v1_funct_1(X2) != iProver_top
% 3.39/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1924,plain,
% 3.39/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.39/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.39/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.39/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.39/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.39/1.00      | v1_funct_1(sK3) != iProver_top
% 3.39/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.39/1.00      inference(equality_resolution,[status(thm)],[c_1314]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_37,negated_conjecture,
% 3.39/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_40,plain,
% 3.39/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_34,negated_conjecture,
% 3.39/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_43,plain,
% 3.39/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2180,plain,
% 3.39/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_1924,c_39,c_40,c_41,c_42,c_43,c_44]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2472,plain,
% 3.39/1.00      ( k2_relat_1(sK3) = sK0 ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_2466,c_2180]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_17,plain,
% 3.39/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.39/1.00      | k1_xboole_0 = X2 ),
% 3.39/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1332,plain,
% 3.39/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.39/1.00      | k1_xboole_0 = X1
% 3.39/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4727,plain,
% 3.39/1.00      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 3.39/1.00      | sK0 = k1_xboole_0
% 3.39/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1322,c_1332]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1339,plain,
% 3.39/1.00      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 3.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3119,plain,
% 3.39/1.00      ( k8_relset_1(sK1,sK0,sK3,sK0) = k1_relset_1(sK1,sK0,sK3) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1322,c_1339]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.39/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1340,plain,
% 3.39/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2505,plain,
% 3.39/1.00      ( k8_relset_1(sK1,sK0,sK3,X0) = k10_relat_1(sK3,X0) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1322,c_1340]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | v1_relat_1(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1342,plain,
% 3.39/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.39/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2371,plain,
% 3.39/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1322,c_1342]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_0,plain,
% 3.39/1.00      ( ~ v1_relat_1(X0)
% 3.39/1.00      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1347,plain,
% 3.39/1.00      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.39/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2439,plain,
% 3.39/1.00      ( k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_2371,c_1347]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2680,plain,
% 3.39/1.00      ( k10_relat_1(sK3,sK0) = k1_relat_1(sK3) ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_2439,c_2472]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3125,plain,
% 3.39/1.00      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_3119,c_2505,c_2680]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4739,plain,
% 3.39/1.00      ( k1_relat_1(sK3) = sK1
% 3.39/1.00      | sK0 = k1_xboole_0
% 3.39/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_4727,c_3125]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_29,negated_conjecture,
% 3.39/1.00      ( k1_xboole_0 != sK0 ),
% 3.39/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_729,plain,( X0 = X0 ),theory(equality) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_758,plain,
% 3.39/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_729]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_730,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1764,plain,
% 3.39/1.00      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_730]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1765,plain,
% 3.39/1.00      ( sK0 != k1_xboole_0
% 3.39/1.00      | k1_xboole_0 = sK0
% 3.39/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_1764]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4946,plain,
% 3.39/1.00      ( k1_relat_1(sK3) = sK1 ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_4739,c_43,c_29,c_758,c_1765]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6893,plain,
% 3.39/1.00      ( k2_funct_1(sK3) = sK2
% 3.39/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 3.39/1.00      | sK1 != sK1
% 3.39/1.00      | v1_funct_1(sK3) != iProver_top
% 3.39/1.00      | v1_funct_1(sK2) != iProver_top
% 3.39/1.00      | v2_funct_1(sK3) != iProver_top
% 3.39/1.00      | v1_relat_1(sK3) != iProver_top
% 3.39/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.39/1.00      inference(light_normalisation,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_6892,c_2469,c_2472,c_4946]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6894,plain,
% 3.39/1.00      ( k2_funct_1(sK3) = sK2
% 3.39/1.00      | v1_funct_1(sK3) != iProver_top
% 3.39/1.00      | v1_funct_1(sK2) != iProver_top
% 3.39/1.00      | v2_funct_1(sK3) != iProver_top
% 3.39/1.00      | v1_relat_1(sK3) != iProver_top
% 3.39/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.39/1.00      inference(equality_resolution_simp,[status(thm)],[c_6893]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1705,plain,
% 3.39/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.39/1.00      | v1_relat_1(sK3) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1706,plain,
% 3.39/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.39/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_1705]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1708,plain,
% 3.39/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.39/1.00      | v1_relat_1(sK2) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1709,plain,
% 3.39/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.39/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_1708]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_24,plain,
% 3.39/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.39/1.00      | ~ v1_funct_2(X3,X4,X1)
% 3.39/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | ~ v1_funct_1(X3)
% 3.39/1.00      | v2_funct_1(X0)
% 3.39/1.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.39/1.00      | k2_relset_1(X4,X1,X3) != X1
% 3.39/1.00      | k1_xboole_0 = X2 ),
% 3.39/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1326,plain,
% 3.39/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 3.39/1.00      | k1_xboole_0 = X3
% 3.39/1.00      | v1_funct_2(X4,X1,X3) != iProver_top
% 3.39/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.39/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 3.39/1.00      | v1_funct_1(X4) != iProver_top
% 3.39/1.00      | v1_funct_1(X2) != iProver_top
% 3.39/1.00      | v2_funct_1(X4) = iProver_top
% 3.39/1.00      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5065,plain,
% 3.39/1.00      ( k1_xboole_0 = X0
% 3.39/1.00      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.39/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.39/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.39/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.39/1.00      | v1_funct_1(X1) != iProver_top
% 3.39/1.00      | v1_funct_1(sK2) != iProver_top
% 3.39/1.00      | v2_funct_1(X1) = iProver_top
% 3.39/1.00      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_32,c_1326]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5455,plain,
% 3.39/1.00      ( v1_funct_1(X1) != iProver_top
% 3.39/1.00      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.39/1.00      | k1_xboole_0 = X0
% 3.39/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.39/1.00      | v2_funct_1(X1) = iProver_top
% 3.39/1.00      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_5065,c_39,c_40,c_41]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5456,plain,
% 3.39/1.00      ( k1_xboole_0 = X0
% 3.39/1.00      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.39/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.39/1.00      | v1_funct_1(X1) != iProver_top
% 3.39/1.00      | v2_funct_1(X1) = iProver_top
% 3.39/1.00      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_5455]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5864,plain,
% 3.39/1.00      ( sK0 = k1_xboole_0
% 3.39/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.39/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.39/1.00      | v1_funct_1(sK3) != iProver_top
% 3.39/1.00      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 3.39/1.00      | v2_funct_1(sK3) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_5832,c_5456]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6394,plain,
% 3.39/1.00      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 3.39/1.00      | v2_funct_1(sK3) = iProver_top ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_5864,c_42,c_43,c_44,c_29,c_758,c_1765]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6883,plain,
% 3.39/1.00      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.39/1.00      | v2_funct_1(sK3) = iProver_top ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_6880,c_6394]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1,plain,
% 3.39/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.39/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1346,plain,
% 3.39/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7198,plain,
% 3.39/1.00      ( v2_funct_1(sK3) = iProver_top ),
% 3.39/1.00      inference(forward_subsumption_resolution,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_6883,c_1346]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_8411,plain,
% 3.39/1.00      ( k2_funct_1(sK3) = sK2 ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_6894,c_39,c_41,c_42,c_44,c_1706,c_1709,c_7198]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1320,plain,
% 3.39/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4,plain,
% 3.39/1.00      ( ~ v1_funct_1(X0)
% 3.39/1.00      | ~ v2_funct_1(X0)
% 3.39/1.00      | ~ v1_relat_1(X0)
% 3.39/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.39/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1343,plain,
% 3.39/1.00      ( k2_funct_1(k2_funct_1(X0)) = X0
% 3.39/1.00      | v1_funct_1(X0) != iProver_top
% 3.39/1.00      | v2_funct_1(X0) != iProver_top
% 3.39/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3176,plain,
% 3.39/1.00      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.39/1.00      | v2_funct_1(sK3) != iProver_top
% 3.39/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1320,c_1343]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1738,plain,
% 3.39/1.00      ( ~ v1_funct_1(sK3)
% 3.39/1.00      | ~ v2_funct_1(sK3)
% 3.39/1.00      | ~ v1_relat_1(sK3)
% 3.39/1.00      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1739,plain,
% 3.39/1.00      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.39/1.00      | v1_funct_1(sK3) != iProver_top
% 3.39/1.00      | v2_funct_1(sK3) != iProver_top
% 3.39/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_1738]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3193,plain,
% 3.39/1.00      ( v2_funct_1(sK3) != iProver_top
% 3.39/1.00      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_3176,c_42,c_44,c_1706,c_1739]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3194,plain,
% 3.39/1.00      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.39/1.00      | v2_funct_1(sK3) != iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_3193]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7200,plain,
% 3.39/1.00      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_7198,c_3194]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_8414,plain,
% 3.39/1.00      ( k2_funct_1(sK2) = sK3 ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_8411,c_7200]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_27,negated_conjecture,
% 3.39/1.00      ( k2_funct_1(sK2) != sK3 ),
% 3.39/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(contradiction,plain,
% 3.39/1.00      ( $false ),
% 3.39/1.00      inference(minisat,[status(thm)],[c_8414,c_27]) ).
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  ------                               Statistics
% 3.39/1.00  
% 3.39/1.00  ------ General
% 3.39/1.00  
% 3.39/1.00  abstr_ref_over_cycles:                  0
% 3.39/1.00  abstr_ref_under_cycles:                 0
% 3.39/1.00  gc_basic_clause_elim:                   0
% 3.39/1.00  forced_gc_time:                         0
% 3.39/1.00  parsing_time:                           0.018
% 3.39/1.00  unif_index_cands_time:                  0.
% 3.39/1.00  unif_index_add_time:                    0.
% 3.39/1.00  orderings_time:                         0.
% 3.39/1.00  out_proof_time:                         0.014
% 3.39/1.00  total_time:                             0.332
% 3.39/1.00  num_of_symbols:                         55
% 3.39/1.00  num_of_terms:                           10666
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing
% 3.39/1.00  
% 3.39/1.00  num_of_splits:                          0
% 3.39/1.00  num_of_split_atoms:                     0
% 3.39/1.00  num_of_reused_defs:                     0
% 3.39/1.00  num_eq_ax_congr_red:                    45
% 3.39/1.00  num_of_sem_filtered_clauses:            1
% 3.39/1.00  num_of_subtypes:                        0
% 3.39/1.00  monotx_restored_types:                  0
% 3.39/1.00  sat_num_of_epr_types:                   0
% 3.39/1.00  sat_num_of_non_cyclic_types:            0
% 3.39/1.00  sat_guarded_non_collapsed_types:        0
% 3.39/1.00  num_pure_diseq_elim:                    0
% 3.39/1.00  simp_replaced_by:                       0
% 3.39/1.00  res_preprocessed:                       184
% 3.39/1.00  prep_upred:                             0
% 3.39/1.00  prep_unflattend:                        12
% 3.39/1.00  smt_new_axioms:                         0
% 3.39/1.00  pred_elim_cands:                        5
% 3.39/1.00  pred_elim:                              1
% 3.39/1.00  pred_elim_cl:                           1
% 3.39/1.00  pred_elim_cycles:                       3
% 3.39/1.00  merged_defs:                            0
% 3.39/1.00  merged_defs_ncl:                        0
% 3.39/1.00  bin_hyper_res:                          0
% 3.39/1.00  prep_cycles:                            4
% 3.39/1.00  pred_elim_time:                         0.005
% 3.39/1.00  splitting_time:                         0.
% 3.39/1.00  sem_filter_time:                        0.
% 3.39/1.00  monotx_time:                            0.
% 3.39/1.00  subtype_inf_time:                       0.
% 3.39/1.00  
% 3.39/1.00  ------ Problem properties
% 3.39/1.00  
% 3.39/1.00  clauses:                                38
% 3.39/1.00  conjectures:                            11
% 3.39/1.00  epr:                                    7
% 3.39/1.00  horn:                                   32
% 3.39/1.00  ground:                                 12
% 3.39/1.00  unary:                                  14
% 3.39/1.00  binary:                                 7
% 3.39/1.00  lits:                                   130
% 3.39/1.00  lits_eq:                                34
% 3.39/1.00  fd_pure:                                0
% 3.39/1.00  fd_pseudo:                              0
% 3.39/1.00  fd_cond:                                5
% 3.39/1.00  fd_pseudo_cond:                         1
% 3.39/1.00  ac_symbols:                             0
% 3.39/1.00  
% 3.39/1.00  ------ Propositional Solver
% 3.39/1.00  
% 3.39/1.00  prop_solver_calls:                      27
% 3.39/1.00  prop_fast_solver_calls:                 1543
% 3.39/1.00  smt_solver_calls:                       0
% 3.39/1.00  smt_fast_solver_calls:                  0
% 3.39/1.00  prop_num_of_clauses:                    3686
% 3.39/1.00  prop_preprocess_simplified:             10596
% 3.39/1.00  prop_fo_subsumed:                       48
% 3.39/1.00  prop_solver_time:                       0.
% 3.39/1.00  smt_solver_time:                        0.
% 3.39/1.00  smt_fast_solver_time:                   0.
% 3.39/1.00  prop_fast_solver_time:                  0.
% 3.39/1.00  prop_unsat_core_time:                   0.
% 3.39/1.00  
% 3.39/1.00  ------ QBF
% 3.39/1.00  
% 3.39/1.00  qbf_q_res:                              0
% 3.39/1.00  qbf_num_tautologies:                    0
% 3.39/1.00  qbf_prep_cycles:                        0
% 3.39/1.00  
% 3.39/1.00  ------ BMC1
% 3.39/1.00  
% 3.39/1.00  bmc1_current_bound:                     -1
% 3.39/1.00  bmc1_last_solved_bound:                 -1
% 3.39/1.00  bmc1_unsat_core_size:                   -1
% 3.39/1.00  bmc1_unsat_core_parents_size:           -1
% 3.39/1.00  bmc1_merge_next_fun:                    0
% 3.39/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.39/1.00  
% 3.39/1.00  ------ Instantiation
% 3.39/1.00  
% 3.39/1.00  inst_num_of_clauses:                    1023
% 3.39/1.00  inst_num_in_passive:                    466
% 3.39/1.00  inst_num_in_active:                     474
% 3.39/1.00  inst_num_in_unprocessed:                83
% 3.39/1.00  inst_num_of_loops:                      480
% 3.39/1.00  inst_num_of_learning_restarts:          0
% 3.39/1.00  inst_num_moves_active_passive:          4
% 3.39/1.00  inst_lit_activity:                      0
% 3.39/1.00  inst_lit_activity_moves:                0
% 3.39/1.00  inst_num_tautologies:                   0
% 3.39/1.00  inst_num_prop_implied:                  0
% 3.39/1.00  inst_num_existing_simplified:           0
% 3.39/1.00  inst_num_eq_res_simplified:             0
% 3.39/1.00  inst_num_child_elim:                    0
% 3.39/1.00  inst_num_of_dismatching_blockings:      44
% 3.39/1.00  inst_num_of_non_proper_insts:           793
% 3.39/1.00  inst_num_of_duplicates:                 0
% 3.39/1.01  inst_inst_num_from_inst_to_res:         0
% 3.39/1.01  inst_dismatching_checking_time:         0.
% 3.39/1.01  
% 3.39/1.01  ------ Resolution
% 3.39/1.01  
% 3.39/1.01  res_num_of_clauses:                     0
% 3.39/1.01  res_num_in_passive:                     0
% 3.39/1.01  res_num_in_active:                      0
% 3.39/1.01  res_num_of_loops:                       188
% 3.39/1.01  res_forward_subset_subsumed:            94
% 3.39/1.01  res_backward_subset_subsumed:           0
% 3.39/1.01  res_forward_subsumed:                   0
% 3.39/1.01  res_backward_subsumed:                  0
% 3.39/1.01  res_forward_subsumption_resolution:     2
% 3.39/1.01  res_backward_subsumption_resolution:    0
% 3.39/1.01  res_clause_to_clause_subsumption:       179
% 3.39/1.01  res_orphan_elimination:                 0
% 3.39/1.01  res_tautology_del:                      20
% 3.39/1.01  res_num_eq_res_simplified:              1
% 3.39/1.01  res_num_sel_changes:                    0
% 3.39/1.01  res_moves_from_active_to_pass:          0
% 3.39/1.01  
% 3.39/1.01  ------ Superposition
% 3.39/1.01  
% 3.39/1.01  sup_time_total:                         0.
% 3.39/1.01  sup_time_generating:                    0.
% 3.39/1.01  sup_time_sim_full:                      0.
% 3.39/1.01  sup_time_sim_immed:                     0.
% 3.39/1.01  
% 3.39/1.01  sup_num_of_clauses:                     134
% 3.39/1.01  sup_num_in_active:                      84
% 3.39/1.01  sup_num_in_passive:                     50
% 3.39/1.01  sup_num_of_loops:                       94
% 3.39/1.01  sup_fw_superposition:                   46
% 3.39/1.01  sup_bw_superposition:                   64
% 3.39/1.01  sup_immediate_simplified:               31
% 3.39/1.01  sup_given_eliminated:                   0
% 3.39/1.01  comparisons_done:                       0
% 3.39/1.01  comparisons_avoided:                    0
% 3.39/1.01  
% 3.39/1.01  ------ Simplifications
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  sim_fw_subset_subsumed:                 9
% 3.39/1.01  sim_bw_subset_subsumed:                 2
% 3.39/1.01  sim_fw_subsumed:                        2
% 3.39/1.01  sim_bw_subsumed:                        0
% 3.39/1.01  sim_fw_subsumption_res:                 1
% 3.39/1.01  sim_bw_subsumption_res:                 0
% 3.39/1.01  sim_tautology_del:                      0
% 3.39/1.01  sim_eq_tautology_del:                   1
% 3.39/1.01  sim_eq_res_simp:                        1
% 3.39/1.01  sim_fw_demodulated:                     11
% 3.39/1.01  sim_bw_demodulated:                     9
% 3.39/1.01  sim_light_normalised:                   10
% 3.39/1.01  sim_joinable_taut:                      0
% 3.39/1.01  sim_joinable_simp:                      0
% 3.39/1.01  sim_ac_normalised:                      0
% 3.39/1.01  sim_smt_subsumption:                    0
% 3.39/1.01  
%------------------------------------------------------------------------------
