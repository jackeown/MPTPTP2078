%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:57 EST 2020

% Result     : Theorem 11.65s
% Output     : CNFRefutation 11.65s
% Verified   : 
% Statistics : Number of formulae       :  235 (1357 expanded)
%              Number of clauses        :  140 ( 384 expanded)
%              Number of leaves         :   23 ( 314 expanded)
%              Depth                    :   24
%              Number of atoms          :  695 (9069 expanded)
%              Number of equality atoms :  332 (3548 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f23,plain,(
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
    inference(pure_predicate_removal,[],[f22])).

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
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

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
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f55,f54])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f93,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f106,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f83,f87])).

fof(f88,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v4_relat_1(k5_relat_1(X1,X2),X0)
        & v1_relat_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k5_relat_1(X1,X2),X0)
        & v1_relat_1(k5_relat_1(X1,X2)) )
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k5_relat_1(X1,X2),X0)
        & v1_relat_1(k5_relat_1(X1,X2)) )
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f76,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f105,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f76,f87])).

fof(f94,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f99,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f64,f87])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f103,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f72,f87])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f87])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f56])).

fof(f77,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f77,f87])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f67,f87])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f97,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1358,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1360,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1361,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5682,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_1361])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5831,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5682,c_42])).

cnf(c_5832,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5831])).

cnf(c_5840,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1358,c_5832])).

cnf(c_25,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_392,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_56,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_56])).

cnf(c_1356,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1448,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1940,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1356,c_39,c_38,c_37,c_36,c_56,c_392,c_1448])).

cnf(c_5841,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5840,c_1940])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6402,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5841,c_40])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k5_relat_1(X0,X2),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1370,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(k5_relat_1(X0,X2),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6404,plain,
    ( v4_relat_1(k6_partfun1(sK0),X0) = iProver_top
    | v4_relat_1(sK2,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6402,c_1370])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1461,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1527,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_1528,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1527])).

cnf(c_1661,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1662,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1661])).

cnf(c_18160,plain,
    ( v4_relat_1(k6_partfun1(sK0),X0) = iProver_top
    | v4_relat_1(sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6404,c_41,c_43,c_1528,c_1662])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1377,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_480,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_33])).

cnf(c_481,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_483,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_481,c_39])).

cnf(c_1351,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_1863,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1351,c_39,c_38,c_481,c_1527])).

cnf(c_5497,plain,
    ( v4_relat_1(k6_partfun1(k1_relat_1(sK2)),X0) = iProver_top
    | v4_relat_1(sK2,X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1863,c_1370])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2094,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2095,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2094])).

cnf(c_11345,plain,
    ( v4_relat_1(k6_partfun1(k1_relat_1(sK2)),X0) = iProver_top
    | v4_relat_1(sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5497,c_40,c_41,c_1528,c_2095])).

cnf(c_8,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1380,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4744,plain,
    ( k1_relat_1(X0) = X1
    | v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_1380])).

cnf(c_16612,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X1
    | v4_relat_1(k6_partfun1(X0),X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_4744])).

cnf(c_16617,plain,
    ( X0 = X1
    | v4_relat_1(k6_partfun1(X1),X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_partfun1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16612,c_8])).

cnf(c_17187,plain,
    ( k1_relat_1(sK2) = X0
    | v4_relat_1(sK2,X0) != iProver_top
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(k6_partfun1(k1_relat_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11345,c_16617])).

cnf(c_16,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2514,plain,
    ( v1_relat_1(k6_partfun1(k1_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2515,plain,
    ( v1_relat_1(k6_partfun1(k1_relat_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2514])).

cnf(c_38625,plain,
    ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v4_relat_1(sK2,X0) != iProver_top
    | k1_relat_1(sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17187,c_2515])).

cnf(c_38626,plain,
    ( k1_relat_1(sK2) = X0
    | v4_relat_1(sK2,X0) != iProver_top
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_38625])).

cnf(c_38632,plain,
    ( k1_relat_1(X0) = k1_relat_1(sK2)
    | v4_relat_1(X0,k1_relat_1(sK2)) != iProver_top
    | v4_relat_1(sK2,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_38626])).

cnf(c_44713,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
    | v4_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) != iProver_top
    | v4_relat_1(sK2,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18160,c_38632])).

cnf(c_44729,plain,
    ( k1_relat_1(sK2) = sK0
    | v4_relat_1(sK2,k1_relat_1(sK2)) != iProver_top
    | v4_relat_1(sK2,sK0) != iProver_top
    | v1_relat_1(k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_44713,c_8])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1366,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v4_relat_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2307,plain,
    ( v4_relat_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1358,c_1366])).

cnf(c_4741,plain,
    ( v4_relat_1(k6_partfun1(X0),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1377])).

cnf(c_85,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4788,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v4_relat_1(k6_partfun1(X0),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4741,c_85])).

cnf(c_4789,plain,
    ( v4_relat_1(k6_partfun1(X0),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_4788])).

cnf(c_11352,plain,
    ( v4_relat_1(sK2,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11345,c_4789])).

cnf(c_11357,plain,
    ( v4_relat_1(sK2,sK0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11352])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1379,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1378,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4772,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1379,c_1378])).

cnf(c_18167,plain,
    ( sK0 = X0
    | v4_relat_1(sK2,X0) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18160,c_16617])).

cnf(c_87,plain,
    ( v1_relat_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(c_18837,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | v4_relat_1(sK2,X0) != iProver_top
    | sK0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18167,c_87])).

cnf(c_18838,plain,
    ( sK0 = X0
    | v4_relat_1(sK2,X0) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_18837])).

cnf(c_18842,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4772,c_18838])).

cnf(c_44958,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_44729,c_41,c_1528,c_2307,c_11357,c_18842])).

cnf(c_1357,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_1371,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1374,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4366,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1371,c_1374])).

cnf(c_9520,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_4366])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_522,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_523,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_525,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_39])).

cnf(c_1348,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_1645,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1348,c_39,c_38,c_523,c_1527])).

cnf(c_9525,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9520,c_1645])).

cnf(c_9600,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9525,c_41,c_1528])).

cnf(c_44968,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_44958,c_9600])).

cnf(c_1367,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2263,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_1367])).

cnf(c_2264,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1358,c_1367])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1375,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5659,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1371,c_1375])).

cnf(c_19714,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_5659])).

cnf(c_20705,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19714,c_41,c_1528])).

cnf(c_20706,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_20705])).

cnf(c_20713,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2264,c_20706])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1365,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3325,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1358,c_1365])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3326,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3325,c_35])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_494,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_33])).

cnf(c_495,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_497,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_39])).

cnf(c_1350,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_1860,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1350,c_39,c_38,c_495,c_1527])).

cnf(c_3480,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_3326,c_1860])).

cnf(c_20732,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20713,c_3480])).

cnf(c_20841,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2263,c_20732])).

cnf(c_20865,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(light_normalisation,[status(thm)],[c_20841,c_6402])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1373,plain,
    ( k5_relat_1(k6_partfun1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2441,plain,
    ( k5_relat_1(k6_partfun1(X0),sK3) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2263,c_1373])).

cnf(c_2306,plain,
    ( v4_relat_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_1366])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1376,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4550,plain,
    ( k7_relat_1(sK3,sK1) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2306,c_1376])).

cnf(c_4587,plain,
    ( k7_relat_1(sK3,sK1) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4550,c_43,c_1662])).

cnf(c_20866,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_20865,c_2441,c_4587])).

cnf(c_44972,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_44968,c_20866])).

cnf(c_30,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f97])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44972,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.65/2.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.65/2.01  
% 11.65/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.65/2.01  
% 11.65/2.01  ------  iProver source info
% 11.65/2.01  
% 11.65/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.65/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.65/2.01  git: non_committed_changes: false
% 11.65/2.01  git: last_make_outside_of_git: false
% 11.65/2.01  
% 11.65/2.01  ------ 
% 11.65/2.01  
% 11.65/2.01  ------ Input Options
% 11.65/2.01  
% 11.65/2.01  --out_options                           all
% 11.65/2.01  --tptp_safe_out                         true
% 11.65/2.01  --problem_path                          ""
% 11.65/2.01  --include_path                          ""
% 11.65/2.01  --clausifier                            res/vclausify_rel
% 11.65/2.01  --clausifier_options                    ""
% 11.65/2.01  --stdin                                 false
% 11.65/2.01  --stats_out                             all
% 11.65/2.01  
% 11.65/2.01  ------ General Options
% 11.65/2.01  
% 11.65/2.01  --fof                                   false
% 11.65/2.01  --time_out_real                         305.
% 11.65/2.01  --time_out_virtual                      -1.
% 11.65/2.01  --symbol_type_check                     false
% 11.65/2.01  --clausify_out                          false
% 11.65/2.01  --sig_cnt_out                           false
% 11.65/2.01  --trig_cnt_out                          false
% 11.65/2.01  --trig_cnt_out_tolerance                1.
% 11.65/2.01  --trig_cnt_out_sk_spl                   false
% 11.65/2.01  --abstr_cl_out                          false
% 11.65/2.01  
% 11.65/2.01  ------ Global Options
% 11.65/2.01  
% 11.65/2.01  --schedule                              default
% 11.65/2.01  --add_important_lit                     false
% 11.65/2.01  --prop_solver_per_cl                    1000
% 11.65/2.01  --min_unsat_core                        false
% 11.65/2.01  --soft_assumptions                      false
% 11.65/2.01  --soft_lemma_size                       3
% 11.65/2.01  --prop_impl_unit_size                   0
% 11.65/2.01  --prop_impl_unit                        []
% 11.65/2.01  --share_sel_clauses                     true
% 11.65/2.01  --reset_solvers                         false
% 11.65/2.01  --bc_imp_inh                            [conj_cone]
% 11.65/2.01  --conj_cone_tolerance                   3.
% 11.65/2.01  --extra_neg_conj                        none
% 11.65/2.01  --large_theory_mode                     true
% 11.65/2.01  --prolific_symb_bound                   200
% 11.65/2.01  --lt_threshold                          2000
% 11.65/2.01  --clause_weak_htbl                      true
% 11.65/2.01  --gc_record_bc_elim                     false
% 11.65/2.01  
% 11.65/2.01  ------ Preprocessing Options
% 11.65/2.01  
% 11.65/2.01  --preprocessing_flag                    true
% 11.65/2.01  --time_out_prep_mult                    0.1
% 11.65/2.01  --splitting_mode                        input
% 11.65/2.01  --splitting_grd                         true
% 11.65/2.01  --splitting_cvd                         false
% 11.65/2.01  --splitting_cvd_svl                     false
% 11.65/2.01  --splitting_nvd                         32
% 11.65/2.01  --sub_typing                            true
% 11.65/2.01  --prep_gs_sim                           true
% 11.65/2.01  --prep_unflatten                        true
% 11.65/2.01  --prep_res_sim                          true
% 11.65/2.01  --prep_upred                            true
% 11.65/2.01  --prep_sem_filter                       exhaustive
% 11.65/2.01  --prep_sem_filter_out                   false
% 11.65/2.01  --pred_elim                             true
% 11.65/2.01  --res_sim_input                         true
% 11.65/2.01  --eq_ax_congr_red                       true
% 11.65/2.01  --pure_diseq_elim                       true
% 11.65/2.01  --brand_transform                       false
% 11.65/2.01  --non_eq_to_eq                          false
% 11.65/2.01  --prep_def_merge                        true
% 11.65/2.01  --prep_def_merge_prop_impl              false
% 11.65/2.01  --prep_def_merge_mbd                    true
% 11.65/2.01  --prep_def_merge_tr_red                 false
% 11.65/2.01  --prep_def_merge_tr_cl                  false
% 11.65/2.01  --smt_preprocessing                     true
% 11.65/2.01  --smt_ac_axioms                         fast
% 11.65/2.01  --preprocessed_out                      false
% 11.65/2.01  --preprocessed_stats                    false
% 11.65/2.01  
% 11.65/2.01  ------ Abstraction refinement Options
% 11.65/2.01  
% 11.65/2.01  --abstr_ref                             []
% 11.65/2.01  --abstr_ref_prep                        false
% 11.65/2.01  --abstr_ref_until_sat                   false
% 11.65/2.01  --abstr_ref_sig_restrict                funpre
% 11.65/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/2.01  --abstr_ref_under                       []
% 11.65/2.01  
% 11.65/2.01  ------ SAT Options
% 11.65/2.01  
% 11.65/2.01  --sat_mode                              false
% 11.65/2.01  --sat_fm_restart_options                ""
% 11.65/2.01  --sat_gr_def                            false
% 11.65/2.01  --sat_epr_types                         true
% 11.65/2.01  --sat_non_cyclic_types                  false
% 11.65/2.01  --sat_finite_models                     false
% 11.65/2.01  --sat_fm_lemmas                         false
% 11.65/2.01  --sat_fm_prep                           false
% 11.65/2.01  --sat_fm_uc_incr                        true
% 11.65/2.01  --sat_out_model                         small
% 11.65/2.01  --sat_out_clauses                       false
% 11.65/2.01  
% 11.65/2.01  ------ QBF Options
% 11.65/2.01  
% 11.65/2.01  --qbf_mode                              false
% 11.65/2.01  --qbf_elim_univ                         false
% 11.65/2.01  --qbf_dom_inst                          none
% 11.65/2.01  --qbf_dom_pre_inst                      false
% 11.65/2.01  --qbf_sk_in                             false
% 11.65/2.01  --qbf_pred_elim                         true
% 11.65/2.01  --qbf_split                             512
% 11.65/2.01  
% 11.65/2.01  ------ BMC1 Options
% 11.65/2.01  
% 11.65/2.01  --bmc1_incremental                      false
% 11.65/2.01  --bmc1_axioms                           reachable_all
% 11.65/2.01  --bmc1_min_bound                        0
% 11.65/2.01  --bmc1_max_bound                        -1
% 11.65/2.01  --bmc1_max_bound_default                -1
% 11.65/2.01  --bmc1_symbol_reachability              true
% 11.65/2.01  --bmc1_property_lemmas                  false
% 11.65/2.01  --bmc1_k_induction                      false
% 11.65/2.01  --bmc1_non_equiv_states                 false
% 11.65/2.01  --bmc1_deadlock                         false
% 11.65/2.01  --bmc1_ucm                              false
% 11.65/2.01  --bmc1_add_unsat_core                   none
% 11.65/2.01  --bmc1_unsat_core_children              false
% 11.65/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/2.01  --bmc1_out_stat                         full
% 11.65/2.01  --bmc1_ground_init                      false
% 11.65/2.01  --bmc1_pre_inst_next_state              false
% 11.65/2.01  --bmc1_pre_inst_state                   false
% 11.65/2.01  --bmc1_pre_inst_reach_state             false
% 11.65/2.01  --bmc1_out_unsat_core                   false
% 11.65/2.01  --bmc1_aig_witness_out                  false
% 11.65/2.01  --bmc1_verbose                          false
% 11.65/2.01  --bmc1_dump_clauses_tptp                false
% 11.65/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.65/2.01  --bmc1_dump_file                        -
% 11.65/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.65/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.65/2.01  --bmc1_ucm_extend_mode                  1
% 11.65/2.01  --bmc1_ucm_init_mode                    2
% 11.65/2.01  --bmc1_ucm_cone_mode                    none
% 11.65/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.65/2.01  --bmc1_ucm_relax_model                  4
% 11.65/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.65/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/2.01  --bmc1_ucm_layered_model                none
% 11.65/2.01  --bmc1_ucm_max_lemma_size               10
% 11.65/2.01  
% 11.65/2.01  ------ AIG Options
% 11.65/2.01  
% 11.65/2.01  --aig_mode                              false
% 11.65/2.01  
% 11.65/2.01  ------ Instantiation Options
% 11.65/2.01  
% 11.65/2.01  --instantiation_flag                    true
% 11.65/2.01  --inst_sos_flag                         true
% 11.65/2.01  --inst_sos_phase                        true
% 11.65/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/2.01  --inst_lit_sel_side                     num_symb
% 11.65/2.01  --inst_solver_per_active                1400
% 11.65/2.01  --inst_solver_calls_frac                1.
% 11.65/2.01  --inst_passive_queue_type               priority_queues
% 11.65/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/2.01  --inst_passive_queues_freq              [25;2]
% 11.65/2.01  --inst_dismatching                      true
% 11.65/2.01  --inst_eager_unprocessed_to_passive     true
% 11.65/2.01  --inst_prop_sim_given                   true
% 11.65/2.01  --inst_prop_sim_new                     false
% 11.65/2.01  --inst_subs_new                         false
% 11.65/2.01  --inst_eq_res_simp                      false
% 11.65/2.01  --inst_subs_given                       false
% 11.65/2.01  --inst_orphan_elimination               true
% 11.65/2.01  --inst_learning_loop_flag               true
% 11.65/2.01  --inst_learning_start                   3000
% 11.65/2.01  --inst_learning_factor                  2
% 11.65/2.01  --inst_start_prop_sim_after_learn       3
% 11.65/2.01  --inst_sel_renew                        solver
% 11.65/2.01  --inst_lit_activity_flag                true
% 11.65/2.01  --inst_restr_to_given                   false
% 11.65/2.01  --inst_activity_threshold               500
% 11.65/2.01  --inst_out_proof                        true
% 11.65/2.01  
% 11.65/2.01  ------ Resolution Options
% 11.65/2.01  
% 11.65/2.01  --resolution_flag                       true
% 11.65/2.01  --res_lit_sel                           adaptive
% 11.65/2.01  --res_lit_sel_side                      none
% 11.65/2.01  --res_ordering                          kbo
% 11.65/2.01  --res_to_prop_solver                    active
% 11.65/2.01  --res_prop_simpl_new                    false
% 11.65/2.01  --res_prop_simpl_given                  true
% 11.65/2.01  --res_passive_queue_type                priority_queues
% 11.65/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/2.01  --res_passive_queues_freq               [15;5]
% 11.65/2.01  --res_forward_subs                      full
% 11.65/2.01  --res_backward_subs                     full
% 11.65/2.01  --res_forward_subs_resolution           true
% 11.65/2.01  --res_backward_subs_resolution          true
% 11.65/2.01  --res_orphan_elimination                true
% 11.65/2.01  --res_time_limit                        2.
% 11.65/2.01  --res_out_proof                         true
% 11.65/2.01  
% 11.65/2.01  ------ Superposition Options
% 11.65/2.01  
% 11.65/2.01  --superposition_flag                    true
% 11.65/2.01  --sup_passive_queue_type                priority_queues
% 11.65/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.65/2.01  --demod_completeness_check              fast
% 11.65/2.01  --demod_use_ground                      true
% 11.65/2.01  --sup_to_prop_solver                    passive
% 11.65/2.01  --sup_prop_simpl_new                    true
% 11.65/2.01  --sup_prop_simpl_given                  true
% 11.65/2.01  --sup_fun_splitting                     true
% 11.65/2.01  --sup_smt_interval                      50000
% 11.65/2.01  
% 11.65/2.01  ------ Superposition Simplification Setup
% 11.65/2.01  
% 11.65/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.65/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.65/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.65/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.65/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.65/2.01  --sup_immed_triv                        [TrivRules]
% 11.65/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.01  --sup_immed_bw_main                     []
% 11.65/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.65/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.01  --sup_input_bw                          []
% 11.65/2.01  
% 11.65/2.01  ------ Combination Options
% 11.65/2.01  
% 11.65/2.01  --comb_res_mult                         3
% 11.65/2.01  --comb_sup_mult                         2
% 11.65/2.01  --comb_inst_mult                        10
% 11.65/2.01  
% 11.65/2.01  ------ Debug Options
% 11.65/2.01  
% 11.65/2.01  --dbg_backtrace                         false
% 11.65/2.01  --dbg_dump_prop_clauses                 false
% 11.65/2.01  --dbg_dump_prop_clauses_file            -
% 11.65/2.01  --dbg_out_stat                          false
% 11.65/2.01  ------ Parsing...
% 11.65/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.65/2.01  
% 11.65/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.65/2.01  
% 11.65/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.65/2.01  
% 11.65/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.65/2.01  ------ Proving...
% 11.65/2.01  ------ Problem Properties 
% 11.65/2.01  
% 11.65/2.01  
% 11.65/2.01  clauses                                 39
% 11.65/2.01  conjectures                             8
% 11.65/2.01  EPR                                     6
% 11.65/2.01  Horn                                    39
% 11.65/2.01  unary                                   13
% 11.65/2.01  binary                                  14
% 11.65/2.01  lits                                    86
% 11.65/2.01  lits eq                                 22
% 11.65/2.01  fd_pure                                 0
% 11.65/2.01  fd_pseudo                               0
% 11.65/2.01  fd_cond                                 0
% 11.65/2.01  fd_pseudo_cond                          1
% 11.65/2.01  AC symbols                              0
% 11.65/2.01  
% 11.65/2.01  ------ Schedule dynamic 5 is on 
% 11.65/2.01  
% 11.65/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.65/2.01  
% 11.65/2.01  
% 11.65/2.01  ------ 
% 11.65/2.01  Current options:
% 11.65/2.01  ------ 
% 11.65/2.01  
% 11.65/2.01  ------ Input Options
% 11.65/2.01  
% 11.65/2.01  --out_options                           all
% 11.65/2.01  --tptp_safe_out                         true
% 11.65/2.01  --problem_path                          ""
% 11.65/2.01  --include_path                          ""
% 11.65/2.01  --clausifier                            res/vclausify_rel
% 11.65/2.01  --clausifier_options                    ""
% 11.65/2.01  --stdin                                 false
% 11.65/2.01  --stats_out                             all
% 11.65/2.01  
% 11.65/2.01  ------ General Options
% 11.65/2.01  
% 11.65/2.01  --fof                                   false
% 11.65/2.01  --time_out_real                         305.
% 11.65/2.01  --time_out_virtual                      -1.
% 11.65/2.01  --symbol_type_check                     false
% 11.65/2.01  --clausify_out                          false
% 11.65/2.01  --sig_cnt_out                           false
% 11.65/2.01  --trig_cnt_out                          false
% 11.65/2.01  --trig_cnt_out_tolerance                1.
% 11.65/2.01  --trig_cnt_out_sk_spl                   false
% 11.65/2.01  --abstr_cl_out                          false
% 11.65/2.01  
% 11.65/2.01  ------ Global Options
% 11.65/2.01  
% 11.65/2.01  --schedule                              default
% 11.65/2.01  --add_important_lit                     false
% 11.65/2.01  --prop_solver_per_cl                    1000
% 11.65/2.01  --min_unsat_core                        false
% 11.65/2.01  --soft_assumptions                      false
% 11.65/2.01  --soft_lemma_size                       3
% 11.65/2.01  --prop_impl_unit_size                   0
% 11.65/2.01  --prop_impl_unit                        []
% 11.65/2.01  --share_sel_clauses                     true
% 11.65/2.01  --reset_solvers                         false
% 11.65/2.01  --bc_imp_inh                            [conj_cone]
% 11.65/2.01  --conj_cone_tolerance                   3.
% 11.65/2.01  --extra_neg_conj                        none
% 11.65/2.01  --large_theory_mode                     true
% 11.65/2.01  --prolific_symb_bound                   200
% 11.65/2.01  --lt_threshold                          2000
% 11.65/2.01  --clause_weak_htbl                      true
% 11.65/2.01  --gc_record_bc_elim                     false
% 11.65/2.01  
% 11.65/2.01  ------ Preprocessing Options
% 11.65/2.01  
% 11.65/2.01  --preprocessing_flag                    true
% 11.65/2.01  --time_out_prep_mult                    0.1
% 11.65/2.01  --splitting_mode                        input
% 11.65/2.01  --splitting_grd                         true
% 11.65/2.01  --splitting_cvd                         false
% 11.65/2.01  --splitting_cvd_svl                     false
% 11.65/2.01  --splitting_nvd                         32
% 11.65/2.01  --sub_typing                            true
% 11.65/2.01  --prep_gs_sim                           true
% 11.65/2.01  --prep_unflatten                        true
% 11.65/2.01  --prep_res_sim                          true
% 11.65/2.01  --prep_upred                            true
% 11.65/2.01  --prep_sem_filter                       exhaustive
% 11.65/2.01  --prep_sem_filter_out                   false
% 11.65/2.01  --pred_elim                             true
% 11.65/2.01  --res_sim_input                         true
% 11.65/2.01  --eq_ax_congr_red                       true
% 11.65/2.01  --pure_diseq_elim                       true
% 11.65/2.01  --brand_transform                       false
% 11.65/2.01  --non_eq_to_eq                          false
% 11.65/2.01  --prep_def_merge                        true
% 11.65/2.01  --prep_def_merge_prop_impl              false
% 11.65/2.01  --prep_def_merge_mbd                    true
% 11.65/2.01  --prep_def_merge_tr_red                 false
% 11.65/2.01  --prep_def_merge_tr_cl                  false
% 11.65/2.01  --smt_preprocessing                     true
% 11.65/2.01  --smt_ac_axioms                         fast
% 11.65/2.01  --preprocessed_out                      false
% 11.65/2.01  --preprocessed_stats                    false
% 11.65/2.01  
% 11.65/2.01  ------ Abstraction refinement Options
% 11.65/2.01  
% 11.65/2.01  --abstr_ref                             []
% 11.65/2.01  --abstr_ref_prep                        false
% 11.65/2.01  --abstr_ref_until_sat                   false
% 11.65/2.01  --abstr_ref_sig_restrict                funpre
% 11.65/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/2.01  --abstr_ref_under                       []
% 11.65/2.01  
% 11.65/2.01  ------ SAT Options
% 11.65/2.01  
% 11.65/2.01  --sat_mode                              false
% 11.65/2.01  --sat_fm_restart_options                ""
% 11.65/2.01  --sat_gr_def                            false
% 11.65/2.01  --sat_epr_types                         true
% 11.65/2.01  --sat_non_cyclic_types                  false
% 11.65/2.01  --sat_finite_models                     false
% 11.65/2.01  --sat_fm_lemmas                         false
% 11.65/2.01  --sat_fm_prep                           false
% 11.65/2.01  --sat_fm_uc_incr                        true
% 11.65/2.01  --sat_out_model                         small
% 11.65/2.01  --sat_out_clauses                       false
% 11.65/2.01  
% 11.65/2.01  ------ QBF Options
% 11.65/2.01  
% 11.65/2.01  --qbf_mode                              false
% 11.65/2.01  --qbf_elim_univ                         false
% 11.65/2.01  --qbf_dom_inst                          none
% 11.65/2.01  --qbf_dom_pre_inst                      false
% 11.65/2.01  --qbf_sk_in                             false
% 11.65/2.01  --qbf_pred_elim                         true
% 11.65/2.01  --qbf_split                             512
% 11.65/2.01  
% 11.65/2.01  ------ BMC1 Options
% 11.65/2.01  
% 11.65/2.01  --bmc1_incremental                      false
% 11.65/2.01  --bmc1_axioms                           reachable_all
% 11.65/2.01  --bmc1_min_bound                        0
% 11.65/2.01  --bmc1_max_bound                        -1
% 11.65/2.01  --bmc1_max_bound_default                -1
% 11.65/2.01  --bmc1_symbol_reachability              true
% 11.65/2.01  --bmc1_property_lemmas                  false
% 11.65/2.01  --bmc1_k_induction                      false
% 11.65/2.01  --bmc1_non_equiv_states                 false
% 11.65/2.01  --bmc1_deadlock                         false
% 11.65/2.01  --bmc1_ucm                              false
% 11.65/2.01  --bmc1_add_unsat_core                   none
% 11.65/2.01  --bmc1_unsat_core_children              false
% 11.65/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/2.01  --bmc1_out_stat                         full
% 11.65/2.01  --bmc1_ground_init                      false
% 11.65/2.01  --bmc1_pre_inst_next_state              false
% 11.65/2.01  --bmc1_pre_inst_state                   false
% 11.65/2.01  --bmc1_pre_inst_reach_state             false
% 11.65/2.01  --bmc1_out_unsat_core                   false
% 11.65/2.01  --bmc1_aig_witness_out                  false
% 11.65/2.01  --bmc1_verbose                          false
% 11.65/2.01  --bmc1_dump_clauses_tptp                false
% 11.65/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.65/2.01  --bmc1_dump_file                        -
% 11.65/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.65/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.65/2.01  --bmc1_ucm_extend_mode                  1
% 11.65/2.01  --bmc1_ucm_init_mode                    2
% 11.65/2.01  --bmc1_ucm_cone_mode                    none
% 11.65/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.65/2.01  --bmc1_ucm_relax_model                  4
% 11.65/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.65/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/2.01  --bmc1_ucm_layered_model                none
% 11.65/2.01  --bmc1_ucm_max_lemma_size               10
% 11.65/2.01  
% 11.65/2.01  ------ AIG Options
% 11.65/2.01  
% 11.65/2.01  --aig_mode                              false
% 11.65/2.01  
% 11.65/2.01  ------ Instantiation Options
% 11.65/2.01  
% 11.65/2.01  --instantiation_flag                    true
% 11.65/2.01  --inst_sos_flag                         true
% 11.65/2.01  --inst_sos_phase                        true
% 11.65/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/2.01  --inst_lit_sel_side                     none
% 11.65/2.01  --inst_solver_per_active                1400
% 11.65/2.01  --inst_solver_calls_frac                1.
% 11.65/2.01  --inst_passive_queue_type               priority_queues
% 11.65/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/2.01  --inst_passive_queues_freq              [25;2]
% 11.65/2.01  --inst_dismatching                      true
% 11.65/2.01  --inst_eager_unprocessed_to_passive     true
% 11.65/2.01  --inst_prop_sim_given                   true
% 11.65/2.01  --inst_prop_sim_new                     false
% 11.65/2.01  --inst_subs_new                         false
% 11.65/2.01  --inst_eq_res_simp                      false
% 11.65/2.01  --inst_subs_given                       false
% 11.65/2.01  --inst_orphan_elimination               true
% 11.65/2.01  --inst_learning_loop_flag               true
% 11.65/2.01  --inst_learning_start                   3000
% 11.65/2.01  --inst_learning_factor                  2
% 11.65/2.01  --inst_start_prop_sim_after_learn       3
% 11.65/2.01  --inst_sel_renew                        solver
% 11.65/2.01  --inst_lit_activity_flag                true
% 11.65/2.01  --inst_restr_to_given                   false
% 11.65/2.01  --inst_activity_threshold               500
% 11.65/2.01  --inst_out_proof                        true
% 11.65/2.01  
% 11.65/2.01  ------ Resolution Options
% 11.65/2.01  
% 11.65/2.01  --resolution_flag                       false
% 11.65/2.01  --res_lit_sel                           adaptive
% 11.65/2.01  --res_lit_sel_side                      none
% 11.65/2.01  --res_ordering                          kbo
% 11.65/2.01  --res_to_prop_solver                    active
% 11.65/2.01  --res_prop_simpl_new                    false
% 11.65/2.01  --res_prop_simpl_given                  true
% 11.65/2.01  --res_passive_queue_type                priority_queues
% 11.65/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/2.01  --res_passive_queues_freq               [15;5]
% 11.65/2.01  --res_forward_subs                      full
% 11.65/2.01  --res_backward_subs                     full
% 11.65/2.01  --res_forward_subs_resolution           true
% 11.65/2.01  --res_backward_subs_resolution          true
% 11.65/2.01  --res_orphan_elimination                true
% 11.65/2.01  --res_time_limit                        2.
% 11.65/2.01  --res_out_proof                         true
% 11.65/2.01  
% 11.65/2.01  ------ Superposition Options
% 11.65/2.01  
% 11.65/2.01  --superposition_flag                    true
% 11.65/2.01  --sup_passive_queue_type                priority_queues
% 11.65/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.65/2.01  --demod_completeness_check              fast
% 11.65/2.01  --demod_use_ground                      true
% 11.65/2.01  --sup_to_prop_solver                    passive
% 11.65/2.01  --sup_prop_simpl_new                    true
% 11.65/2.01  --sup_prop_simpl_given                  true
% 11.65/2.01  --sup_fun_splitting                     true
% 11.65/2.01  --sup_smt_interval                      50000
% 11.65/2.01  
% 11.65/2.01  ------ Superposition Simplification Setup
% 11.65/2.01  
% 11.65/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.65/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.65/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.65/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.65/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.65/2.01  --sup_immed_triv                        [TrivRules]
% 11.65/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.01  --sup_immed_bw_main                     []
% 11.65/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.65/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.01  --sup_input_bw                          []
% 11.65/2.01  
% 11.65/2.01  ------ Combination Options
% 11.65/2.01  
% 11.65/2.01  --comb_res_mult                         3
% 11.65/2.01  --comb_sup_mult                         2
% 11.65/2.01  --comb_inst_mult                        10
% 11.65/2.01  
% 11.65/2.01  ------ Debug Options
% 11.65/2.01  
% 11.65/2.01  --dbg_backtrace                         false
% 11.65/2.01  --dbg_dump_prop_clauses                 false
% 11.65/2.01  --dbg_dump_prop_clauses_file            -
% 11.65/2.01  --dbg_out_stat                          false
% 11.65/2.01  
% 11.65/2.01  
% 11.65/2.01  
% 11.65/2.01  
% 11.65/2.01  ------ Proving...
% 11.65/2.01  
% 11.65/2.01  
% 11.65/2.01  % SZS status Theorem for theBenchmark.p
% 11.65/2.01  
% 11.65/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.65/2.01  
% 11.65/2.01  fof(f21,conjecture,(
% 11.65/2.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f22,negated_conjecture,(
% 11.65/2.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.65/2.01    inference(negated_conjecture,[],[f21])).
% 11.65/2.01  
% 11.65/2.01  fof(f23,plain,(
% 11.65/2.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.65/2.01    inference(pure_predicate_removal,[],[f22])).
% 11.65/2.01  
% 11.65/2.01  fof(f48,plain,(
% 11.65/2.01    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 11.65/2.01    inference(ennf_transformation,[],[f23])).
% 11.65/2.01  
% 11.65/2.01  fof(f49,plain,(
% 11.65/2.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 11.65/2.01    inference(flattening,[],[f48])).
% 11.65/2.01  
% 11.65/2.01  fof(f55,plain,(
% 11.65/2.01    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 11.65/2.01    introduced(choice_axiom,[])).
% 11.65/2.01  
% 11.65/2.01  fof(f54,plain,(
% 11.65/2.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 11.65/2.01    introduced(choice_axiom,[])).
% 11.65/2.01  
% 11.65/2.01  fof(f56,plain,(
% 11.65/2.01    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 11.65/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f55,f54])).
% 11.65/2.01  
% 11.65/2.01  fof(f89,plain,(
% 11.65/2.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.65/2.01    inference(cnf_transformation,[],[f56])).
% 11.65/2.01  
% 11.65/2.01  fof(f91,plain,(
% 11.65/2.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.65/2.01    inference(cnf_transformation,[],[f56])).
% 11.65/2.01  
% 11.65/2.01  fof(f19,axiom,(
% 11.65/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f46,plain,(
% 11.65/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.65/2.01    inference(ennf_transformation,[],[f19])).
% 11.65/2.01  
% 11.65/2.01  fof(f47,plain,(
% 11.65/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.65/2.01    inference(flattening,[],[f46])).
% 11.65/2.01  
% 11.65/2.01  fof(f86,plain,(
% 11.65/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f47])).
% 11.65/2.01  
% 11.65/2.01  fof(f90,plain,(
% 11.65/2.01    v1_funct_1(sK3)),
% 11.65/2.01    inference(cnf_transformation,[],[f56])).
% 11.65/2.01  
% 11.65/2.01  fof(f16,axiom,(
% 11.65/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f42,plain,(
% 11.65/2.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.65/2.01    inference(ennf_transformation,[],[f16])).
% 11.65/2.01  
% 11.65/2.01  fof(f43,plain,(
% 11.65/2.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.01    inference(flattening,[],[f42])).
% 11.65/2.01  
% 11.65/2.01  fof(f53,plain,(
% 11.65/2.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.01    inference(nnf_transformation,[],[f43])).
% 11.65/2.01  
% 11.65/2.01  fof(f81,plain,(
% 11.65/2.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.01    inference(cnf_transformation,[],[f53])).
% 11.65/2.01  
% 11.65/2.01  fof(f93,plain,(
% 11.65/2.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 11.65/2.01    inference(cnf_transformation,[],[f56])).
% 11.65/2.01  
% 11.65/2.01  fof(f17,axiom,(
% 11.65/2.01    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f83,plain,(
% 11.65/2.01    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.65/2.01    inference(cnf_transformation,[],[f17])).
% 11.65/2.01  
% 11.65/2.01  fof(f20,axiom,(
% 11.65/2.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f87,plain,(
% 11.65/2.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f20])).
% 11.65/2.01  
% 11.65/2.01  fof(f106,plain,(
% 11.65/2.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.65/2.01    inference(definition_unfolding,[],[f83,f87])).
% 11.65/2.01  
% 11.65/2.01  fof(f88,plain,(
% 11.65/2.01    v1_funct_1(sK2)),
% 11.65/2.01    inference(cnf_transformation,[],[f56])).
% 11.65/2.01  
% 11.65/2.01  fof(f18,axiom,(
% 11.65/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f44,plain,(
% 11.65/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.65/2.01    inference(ennf_transformation,[],[f18])).
% 11.65/2.01  
% 11.65/2.01  fof(f45,plain,(
% 11.65/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.65/2.01    inference(flattening,[],[f44])).
% 11.65/2.01  
% 11.65/2.01  fof(f85,plain,(
% 11.65/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f45])).
% 11.65/2.01  
% 11.65/2.01  fof(f9,axiom,(
% 11.65/2.01    ! [X0,X1,X2] : ((v1_relat_1(X2) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v4_relat_1(k5_relat_1(X1,X2),X0) & v1_relat_1(k5_relat_1(X1,X2))))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f33,plain,(
% 11.65/2.01    ! [X0,X1,X2] : ((v4_relat_1(k5_relat_1(X1,X2),X0) & v1_relat_1(k5_relat_1(X1,X2))) | (~v1_relat_1(X2) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.65/2.01    inference(ennf_transformation,[],[f9])).
% 11.65/2.01  
% 11.65/2.01  fof(f34,plain,(
% 11.65/2.01    ! [X0,X1,X2] : ((v4_relat_1(k5_relat_1(X1,X2),X0) & v1_relat_1(k5_relat_1(X1,X2))) | ~v1_relat_1(X2) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.65/2.01    inference(flattening,[],[f33])).
% 11.65/2.01  
% 11.65/2.01  fof(f71,plain,(
% 11.65/2.01    ( ! [X2,X0,X1] : (v4_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f34])).
% 11.65/2.01  
% 11.65/2.01  fof(f13,axiom,(
% 11.65/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f39,plain,(
% 11.65/2.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.01    inference(ennf_transformation,[],[f13])).
% 11.65/2.01  
% 11.65/2.01  fof(f78,plain,(
% 11.65/2.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.01    inference(cnf_transformation,[],[f39])).
% 11.65/2.01  
% 11.65/2.01  fof(f2,axiom,(
% 11.65/2.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f25,plain,(
% 11.65/2.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.65/2.01    inference(ennf_transformation,[],[f2])).
% 11.65/2.01  
% 11.65/2.01  fof(f52,plain,(
% 11.65/2.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.65/2.01    inference(nnf_transformation,[],[f25])).
% 11.65/2.01  
% 11.65/2.01  fof(f60,plain,(
% 11.65/2.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f52])).
% 11.65/2.01  
% 11.65/2.01  fof(f12,axiom,(
% 11.65/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f37,plain,(
% 11.65/2.01    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.65/2.01    inference(ennf_transformation,[],[f12])).
% 11.65/2.01  
% 11.65/2.01  fof(f38,plain,(
% 11.65/2.01    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.65/2.01    inference(flattening,[],[f37])).
% 11.65/2.01  
% 11.65/2.01  fof(f76,plain,(
% 11.65/2.01    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f38])).
% 11.65/2.01  
% 11.65/2.01  fof(f105,plain,(
% 11.65/2.01    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.01    inference(definition_unfolding,[],[f76,f87])).
% 11.65/2.01  
% 11.65/2.01  fof(f94,plain,(
% 11.65/2.01    v2_funct_1(sK2)),
% 11.65/2.01    inference(cnf_transformation,[],[f56])).
% 11.65/2.01  
% 11.65/2.01  fof(f8,axiom,(
% 11.65/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f31,plain,(
% 11.65/2.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.65/2.01    inference(ennf_transformation,[],[f8])).
% 11.65/2.01  
% 11.65/2.01  fof(f32,plain,(
% 11.65/2.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.65/2.01    inference(flattening,[],[f31])).
% 11.65/2.01  
% 11.65/2.01  fof(f68,plain,(
% 11.65/2.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f32])).
% 11.65/2.01  
% 11.65/2.01  fof(f5,axiom,(
% 11.65/2.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f64,plain,(
% 11.65/2.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.65/2.01    inference(cnf_transformation,[],[f5])).
% 11.65/2.01  
% 11.65/2.01  fof(f99,plain,(
% 11.65/2.01    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 11.65/2.01    inference(definition_unfolding,[],[f64,f87])).
% 11.65/2.01  
% 11.65/2.01  fof(f1,axiom,(
% 11.65/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f50,plain,(
% 11.65/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.65/2.01    inference(nnf_transformation,[],[f1])).
% 11.65/2.01  
% 11.65/2.01  fof(f51,plain,(
% 11.65/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.65/2.01    inference(flattening,[],[f50])).
% 11.65/2.01  
% 11.65/2.01  fof(f59,plain,(
% 11.65/2.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f51])).
% 11.65/2.01  
% 11.65/2.01  fof(f10,axiom,(
% 11.65/2.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f72,plain,(
% 11.65/2.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 11.65/2.01    inference(cnf_transformation,[],[f10])).
% 11.65/2.01  
% 11.65/2.01  fof(f103,plain,(
% 11.65/2.01    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 11.65/2.01    inference(definition_unfolding,[],[f72,f87])).
% 11.65/2.01  
% 11.65/2.01  fof(f14,axiom,(
% 11.65/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f24,plain,(
% 11.65/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.65/2.01    inference(pure_predicate_removal,[],[f14])).
% 11.65/2.01  
% 11.65/2.01  fof(f40,plain,(
% 11.65/2.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.01    inference(ennf_transformation,[],[f24])).
% 11.65/2.01  
% 11.65/2.01  fof(f79,plain,(
% 11.65/2.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.01    inference(cnf_transformation,[],[f40])).
% 11.65/2.01  
% 11.65/2.01  fof(f58,plain,(
% 11.65/2.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.65/2.01    inference(cnf_transformation,[],[f51])).
% 11.65/2.01  
% 11.65/2.01  fof(f107,plain,(
% 11.65/2.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.65/2.01    inference(equality_resolution,[],[f58])).
% 11.65/2.01  
% 11.65/2.01  fof(f61,plain,(
% 11.65/2.01    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f52])).
% 11.65/2.01  
% 11.65/2.01  fof(f6,axiom,(
% 11.65/2.01    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f29,plain,(
% 11.65/2.01    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 11.65/2.01    inference(ennf_transformation,[],[f6])).
% 11.65/2.01  
% 11.65/2.01  fof(f66,plain,(
% 11.65/2.01    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f29])).
% 11.65/2.01  
% 11.65/2.01  fof(f100,plain,(
% 11.65/2.01    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 11.65/2.01    inference(definition_unfolding,[],[f66,f87])).
% 11.65/2.01  
% 11.65/2.01  fof(f11,axiom,(
% 11.65/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f35,plain,(
% 11.65/2.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.65/2.01    inference(ennf_transformation,[],[f11])).
% 11.65/2.01  
% 11.65/2.01  fof(f36,plain,(
% 11.65/2.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.65/2.01    inference(flattening,[],[f35])).
% 11.65/2.01  
% 11.65/2.01  fof(f75,plain,(
% 11.65/2.01    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f36])).
% 11.65/2.01  
% 11.65/2.01  fof(f4,axiom,(
% 11.65/2.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f28,plain,(
% 11.65/2.01    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.65/2.01    inference(ennf_transformation,[],[f4])).
% 11.65/2.01  
% 11.65/2.01  fof(f63,plain,(
% 11.65/2.01    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f28])).
% 11.65/2.01  
% 11.65/2.01  fof(f15,axiom,(
% 11.65/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f41,plain,(
% 11.65/2.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.01    inference(ennf_transformation,[],[f15])).
% 11.65/2.01  
% 11.65/2.01  fof(f80,plain,(
% 11.65/2.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.01    inference(cnf_transformation,[],[f41])).
% 11.65/2.01  
% 11.65/2.01  fof(f92,plain,(
% 11.65/2.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 11.65/2.01    inference(cnf_transformation,[],[f56])).
% 11.65/2.01  
% 11.65/2.01  fof(f77,plain,(
% 11.65/2.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f38])).
% 11.65/2.01  
% 11.65/2.01  fof(f104,plain,(
% 11.65/2.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.01    inference(definition_unfolding,[],[f77,f87])).
% 11.65/2.01  
% 11.65/2.01  fof(f7,axiom,(
% 11.65/2.01    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f30,plain,(
% 11.65/2.01    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 11.65/2.01    inference(ennf_transformation,[],[f7])).
% 11.65/2.01  
% 11.65/2.01  fof(f67,plain,(
% 11.65/2.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f30])).
% 11.65/2.01  
% 11.65/2.01  fof(f101,plain,(
% 11.65/2.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(X1)) )),
% 11.65/2.01    inference(definition_unfolding,[],[f67,f87])).
% 11.65/2.01  
% 11.65/2.01  fof(f3,axiom,(
% 11.65/2.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 11.65/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.01  
% 11.65/2.01  fof(f26,plain,(
% 11.65/2.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.65/2.01    inference(ennf_transformation,[],[f3])).
% 11.65/2.01  
% 11.65/2.01  fof(f27,plain,(
% 11.65/2.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.65/2.01    inference(flattening,[],[f26])).
% 11.65/2.01  
% 11.65/2.01  fof(f62,plain,(
% 11.65/2.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.65/2.01    inference(cnf_transformation,[],[f27])).
% 11.65/2.01  
% 11.65/2.01  fof(f97,plain,(
% 11.65/2.01    k2_funct_1(sK2) != sK3),
% 11.65/2.01    inference(cnf_transformation,[],[f56])).
% 11.65/2.01  
% 11.65/2.01  cnf(c_38,negated_conjecture,
% 11.65/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.65/2.01      inference(cnf_transformation,[],[f89]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1358,plain,
% 11.65/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_36,negated_conjecture,
% 11.65/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.65/2.01      inference(cnf_transformation,[],[f91]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1360,plain,
% 11.65/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_29,plain,
% 11.65/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.65/2.01      | ~ v1_funct_1(X0)
% 11.65/2.01      | ~ v1_funct_1(X3)
% 11.65/2.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.65/2.01      inference(cnf_transformation,[],[f86]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1361,plain,
% 11.65/2.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.65/2.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.65/2.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.01      | v1_funct_1(X5) != iProver_top
% 11.65/2.01      | v1_funct_1(X4) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_5682,plain,
% 11.65/2.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.65/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.01      | v1_funct_1(X2) != iProver_top
% 11.65/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1360,c_1361]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_37,negated_conjecture,
% 11.65/2.01      ( v1_funct_1(sK3) ),
% 11.65/2.01      inference(cnf_transformation,[],[f90]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_42,plain,
% 11.65/2.01      ( v1_funct_1(sK3) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_5831,plain,
% 11.65/2.01      ( v1_funct_1(X2) != iProver_top
% 11.65/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.01      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_5682,c_42]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_5832,plain,
% 11.65/2.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.65/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.01      | v1_funct_1(X2) != iProver_top ),
% 11.65/2.01      inference(renaming,[status(thm)],[c_5831]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_5840,plain,
% 11.65/2.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 11.65/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1358,c_5832]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_25,plain,
% 11.65/2.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.65/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.65/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.65/2.01      | X3 = X2 ),
% 11.65/2.01      inference(cnf_transformation,[],[f81]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_34,negated_conjecture,
% 11.65/2.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 11.65/2.01      inference(cnf_transformation,[],[f93]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_391,plain,
% 11.65/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.01      | X3 = X0
% 11.65/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 11.65/2.01      | k6_partfun1(sK0) != X3
% 11.65/2.01      | sK0 != X2
% 11.65/2.01      | sK0 != X1 ),
% 11.65/2.01      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_392,plain,
% 11.65/2.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.65/2.01      inference(unflattening,[status(thm)],[c_391]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_26,plain,
% 11.65/2.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.65/2.01      inference(cnf_transformation,[],[f106]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_56,plain,
% 11.65/2.01      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.65/2.01      inference(instantiation,[status(thm)],[c_26]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_394,plain,
% 11.65/2.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_392,c_56]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1356,plain,
% 11.65/2.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.65/2.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_39,negated_conjecture,
% 11.65/2.01      ( v1_funct_1(sK2) ),
% 11.65/2.01      inference(cnf_transformation,[],[f88]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_27,plain,
% 11.65/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.65/2.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.65/2.01      | ~ v1_funct_1(X0)
% 11.65/2.01      | ~ v1_funct_1(X3) ),
% 11.65/2.01      inference(cnf_transformation,[],[f85]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1448,plain,
% 11.65/2.01      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.65/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.65/2.01      | ~ v1_funct_1(sK3)
% 11.65/2.01      | ~ v1_funct_1(sK2) ),
% 11.65/2.01      inference(instantiation,[status(thm)],[c_27]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1940,plain,
% 11.65/2.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_1356,c_39,c_38,c_37,c_36,c_56,c_392,c_1448]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_5841,plain,
% 11.65/2.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 11.65/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.01      inference(light_normalisation,[status(thm)],[c_5840,c_1940]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_40,plain,
% 11.65/2.01      ( v1_funct_1(sK2) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_6402,plain,
% 11.65/2.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_5841,c_40]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_13,plain,
% 11.65/2.01      ( ~ v4_relat_1(X0,X1)
% 11.65/2.01      | v4_relat_1(k5_relat_1(X0,X2),X1)
% 11.65/2.01      | ~ v1_relat_1(X0)
% 11.65/2.01      | ~ v1_relat_1(X2) ),
% 11.65/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1370,plain,
% 11.65/2.01      ( v4_relat_1(X0,X1) != iProver_top
% 11.65/2.01      | v4_relat_1(k5_relat_1(X0,X2),X1) = iProver_top
% 11.65/2.01      | v1_relat_1(X0) != iProver_top
% 11.65/2.01      | v1_relat_1(X2) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_6404,plain,
% 11.65/2.01      ( v4_relat_1(k6_partfun1(sK0),X0) = iProver_top
% 11.65/2.01      | v4_relat_1(sK2,X0) != iProver_top
% 11.65/2.01      | v1_relat_1(sK3) != iProver_top
% 11.65/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_6402,c_1370]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_41,plain,
% 11.65/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_43,plain,
% 11.65/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_21,plain,
% 11.65/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.01      | v1_relat_1(X0) ),
% 11.65/2.01      inference(cnf_transformation,[],[f78]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1461,plain,
% 11.65/2.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.65/2.01      | v1_relat_1(sK2) ),
% 11.65/2.01      inference(instantiation,[status(thm)],[c_21]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1527,plain,
% 11.65/2.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.65/2.01      | v1_relat_1(sK2) ),
% 11.65/2.01      inference(instantiation,[status(thm)],[c_1461]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1528,plain,
% 11.65/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.65/2.01      | v1_relat_1(sK2) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_1527]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1661,plain,
% 11.65/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.65/2.01      | v1_relat_1(sK3) ),
% 11.65/2.01      inference(instantiation,[status(thm)],[c_21]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1662,plain,
% 11.65/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.65/2.01      | v1_relat_1(sK3) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_1661]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_18160,plain,
% 11.65/2.01      ( v4_relat_1(k6_partfun1(sK0),X0) = iProver_top
% 11.65/2.01      | v4_relat_1(sK2,X0) != iProver_top ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_6404,c_41,c_43,c_1528,c_1662]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_4,plain,
% 11.65/2.01      ( ~ v4_relat_1(X0,X1)
% 11.65/2.01      | r1_tarski(k1_relat_1(X0),X1)
% 11.65/2.01      | ~ v1_relat_1(X0) ),
% 11.65/2.01      inference(cnf_transformation,[],[f60]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1377,plain,
% 11.65/2.01      ( v4_relat_1(X0,X1) != iProver_top
% 11.65/2.01      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 11.65/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_20,plain,
% 11.65/2.01      ( ~ v2_funct_1(X0)
% 11.65/2.01      | ~ v1_funct_1(X0)
% 11.65/2.01      | ~ v1_relat_1(X0)
% 11.65/2.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 11.65/2.01      inference(cnf_transformation,[],[f105]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_33,negated_conjecture,
% 11.65/2.01      ( v2_funct_1(sK2) ),
% 11.65/2.01      inference(cnf_transformation,[],[f94]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_480,plain,
% 11.65/2.01      ( ~ v1_funct_1(X0)
% 11.65/2.01      | ~ v1_relat_1(X0)
% 11.65/2.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 11.65/2.01      | sK2 != X0 ),
% 11.65/2.01      inference(resolution_lifted,[status(thm)],[c_20,c_33]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_481,plain,
% 11.65/2.01      ( ~ v1_funct_1(sK2)
% 11.65/2.01      | ~ v1_relat_1(sK2)
% 11.65/2.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 11.65/2.01      inference(unflattening,[status(thm)],[c_480]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_483,plain,
% 11.65/2.01      ( ~ v1_relat_1(sK2)
% 11.65/2.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_481,c_39]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1351,plain,
% 11.65/2.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 11.65/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1863,plain,
% 11.65/2.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_1351,c_39,c_38,c_481,c_1527]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_5497,plain,
% 11.65/2.01      ( v4_relat_1(k6_partfun1(k1_relat_1(sK2)),X0) = iProver_top
% 11.65/2.01      | v4_relat_1(sK2,X0) != iProver_top
% 11.65/2.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 11.65/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1863,c_1370]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_12,plain,
% 11.65/2.01      ( ~ v1_funct_1(X0)
% 11.65/2.01      | ~ v1_relat_1(X0)
% 11.65/2.01      | v1_relat_1(k2_funct_1(X0)) ),
% 11.65/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_2094,plain,
% 11.65/2.01      ( ~ v1_funct_1(sK2)
% 11.65/2.01      | v1_relat_1(k2_funct_1(sK2))
% 11.65/2.01      | ~ v1_relat_1(sK2) ),
% 11.65/2.01      inference(instantiation,[status(thm)],[c_12]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_2095,plain,
% 11.65/2.01      ( v1_funct_1(sK2) != iProver_top
% 11.65/2.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 11.65/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_2094]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_11345,plain,
% 11.65/2.01      ( v4_relat_1(k6_partfun1(k1_relat_1(sK2)),X0) = iProver_top
% 11.65/2.01      | v4_relat_1(sK2,X0) != iProver_top ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_5497,c_40,c_41,c_1528,c_2095]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_8,plain,
% 11.65/2.01      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 11.65/2.01      inference(cnf_transformation,[],[f99]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_0,plain,
% 11.65/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.65/2.01      inference(cnf_transformation,[],[f59]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1380,plain,
% 11.65/2.01      ( X0 = X1
% 11.65/2.01      | r1_tarski(X0,X1) != iProver_top
% 11.65/2.01      | r1_tarski(X1,X0) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_4744,plain,
% 11.65/2.01      ( k1_relat_1(X0) = X1
% 11.65/2.01      | v4_relat_1(X0,X1) != iProver_top
% 11.65/2.01      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 11.65/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1377,c_1380]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_16612,plain,
% 11.65/2.01      ( k1_relat_1(k6_partfun1(X0)) = X1
% 11.65/2.01      | v4_relat_1(k6_partfun1(X0),X1) != iProver_top
% 11.65/2.01      | r1_tarski(X1,X0) != iProver_top
% 11.65/2.01      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_8,c_4744]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_16617,plain,
% 11.65/2.01      ( X0 = X1
% 11.65/2.01      | v4_relat_1(k6_partfun1(X1),X0) != iProver_top
% 11.65/2.01      | r1_tarski(X0,X1) != iProver_top
% 11.65/2.01      | v1_relat_1(k6_partfun1(X1)) != iProver_top ),
% 11.65/2.01      inference(demodulation,[status(thm)],[c_16612,c_8]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_17187,plain,
% 11.65/2.01      ( k1_relat_1(sK2) = X0
% 11.65/2.01      | v4_relat_1(sK2,X0) != iProver_top
% 11.65/2.01      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 11.65/2.01      | v1_relat_1(k6_partfun1(k1_relat_1(sK2))) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_11345,c_16617]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_16,plain,
% 11.65/2.01      ( v1_relat_1(k6_partfun1(X0)) ),
% 11.65/2.01      inference(cnf_transformation,[],[f103]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_2514,plain,
% 11.65/2.01      ( v1_relat_1(k6_partfun1(k1_relat_1(sK2))) ),
% 11.65/2.01      inference(instantiation,[status(thm)],[c_16]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_2515,plain,
% 11.65/2.01      ( v1_relat_1(k6_partfun1(k1_relat_1(sK2))) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_2514]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_38625,plain,
% 11.65/2.01      ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 11.65/2.01      | v4_relat_1(sK2,X0) != iProver_top
% 11.65/2.01      | k1_relat_1(sK2) = X0 ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_17187,c_2515]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_38626,plain,
% 11.65/2.01      ( k1_relat_1(sK2) = X0
% 11.65/2.01      | v4_relat_1(sK2,X0) != iProver_top
% 11.65/2.01      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 11.65/2.01      inference(renaming,[status(thm)],[c_38625]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_38632,plain,
% 11.65/2.01      ( k1_relat_1(X0) = k1_relat_1(sK2)
% 11.65/2.01      | v4_relat_1(X0,k1_relat_1(sK2)) != iProver_top
% 11.65/2.01      | v4_relat_1(sK2,k1_relat_1(X0)) != iProver_top
% 11.65/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1377,c_38626]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_44713,plain,
% 11.65/2.01      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
% 11.65/2.01      | v4_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) != iProver_top
% 11.65/2.01      | v4_relat_1(sK2,k1_relat_1(sK2)) != iProver_top
% 11.65/2.01      | v1_relat_1(k6_partfun1(sK0)) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_18160,c_38632]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_44729,plain,
% 11.65/2.01      ( k1_relat_1(sK2) = sK0
% 11.65/2.01      | v4_relat_1(sK2,k1_relat_1(sK2)) != iProver_top
% 11.65/2.01      | v4_relat_1(sK2,sK0) != iProver_top
% 11.65/2.01      | v1_relat_1(k6_partfun1(sK0)) != iProver_top ),
% 11.65/2.01      inference(demodulation,[status(thm)],[c_44713,c_8]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_22,plain,
% 11.65/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.01      | v4_relat_1(X0,X1) ),
% 11.65/2.01      inference(cnf_transformation,[],[f79]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1366,plain,
% 11.65/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.65/2.01      | v4_relat_1(X0,X1) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_2307,plain,
% 11.65/2.01      ( v4_relat_1(sK2,sK0) = iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1358,c_1366]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_4741,plain,
% 11.65/2.01      ( v4_relat_1(k6_partfun1(X0),X1) != iProver_top
% 11.65/2.01      | r1_tarski(X0,X1) = iProver_top
% 11.65/2.01      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_8,c_1377]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_85,plain,
% 11.65/2.01      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_4788,plain,
% 11.65/2.01      ( r1_tarski(X0,X1) = iProver_top
% 11.65/2.01      | v4_relat_1(k6_partfun1(X0),X1) != iProver_top ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_4741,c_85]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_4789,plain,
% 11.65/2.01      ( v4_relat_1(k6_partfun1(X0),X1) != iProver_top
% 11.65/2.01      | r1_tarski(X0,X1) = iProver_top ),
% 11.65/2.01      inference(renaming,[status(thm)],[c_4788]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_11352,plain,
% 11.65/2.01      ( v4_relat_1(sK2,X0) != iProver_top
% 11.65/2.01      | r1_tarski(k1_relat_1(sK2),X0) = iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_11345,c_4789]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_11357,plain,
% 11.65/2.01      ( v4_relat_1(sK2,sK0) != iProver_top
% 11.65/2.01      | r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 11.65/2.01      inference(instantiation,[status(thm)],[c_11352]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1,plain,
% 11.65/2.01      ( r1_tarski(X0,X0) ),
% 11.65/2.01      inference(cnf_transformation,[],[f107]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1379,plain,
% 11.65/2.01      ( r1_tarski(X0,X0) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_3,plain,
% 11.65/2.01      ( v4_relat_1(X0,X1)
% 11.65/2.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 11.65/2.01      | ~ v1_relat_1(X0) ),
% 11.65/2.01      inference(cnf_transformation,[],[f61]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1378,plain,
% 11.65/2.01      ( v4_relat_1(X0,X1) = iProver_top
% 11.65/2.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 11.65/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_4772,plain,
% 11.65/2.01      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 11.65/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1379,c_1378]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_18167,plain,
% 11.65/2.01      ( sK0 = X0
% 11.65/2.01      | v4_relat_1(sK2,X0) != iProver_top
% 11.65/2.01      | r1_tarski(X0,sK0) != iProver_top
% 11.65/2.01      | v1_relat_1(k6_partfun1(sK0)) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_18160,c_16617]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_87,plain,
% 11.65/2.01      ( v1_relat_1(k6_partfun1(sK0)) = iProver_top ),
% 11.65/2.01      inference(instantiation,[status(thm)],[c_85]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_18837,plain,
% 11.65/2.01      ( r1_tarski(X0,sK0) != iProver_top
% 11.65/2.01      | v4_relat_1(sK2,X0) != iProver_top
% 11.65/2.01      | sK0 = X0 ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_18167,c_87]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_18838,plain,
% 11.65/2.01      ( sK0 = X0
% 11.65/2.01      | v4_relat_1(sK2,X0) != iProver_top
% 11.65/2.01      | r1_tarski(X0,sK0) != iProver_top ),
% 11.65/2.01      inference(renaming,[status(thm)],[c_18837]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_18842,plain,
% 11.65/2.01      ( k1_relat_1(sK2) = sK0
% 11.65/2.01      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top
% 11.65/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_4772,c_18838]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_44958,plain,
% 11.65/2.01      ( k1_relat_1(sK2) = sK0 ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_44729,c_41,c_1528,c_2307,c_11357,c_18842]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1357,plain,
% 11.65/2.01      ( v1_funct_1(sK2) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1371,plain,
% 11.65/2.01      ( v1_funct_1(X0) != iProver_top
% 11.65/2.01      | v1_relat_1(X0) != iProver_top
% 11.65/2.01      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_9,plain,
% 11.65/2.01      ( ~ v1_relat_1(X0)
% 11.65/2.01      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 11.65/2.01      inference(cnf_transformation,[],[f100]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1374,plain,
% 11.65/2.01      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 11.65/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_4366,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 11.65/2.01      | v1_funct_1(X0) != iProver_top
% 11.65/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1371,c_1374]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_9520,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
% 11.65/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1357,c_4366]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_17,plain,
% 11.65/2.01      ( ~ v2_funct_1(X0)
% 11.65/2.01      | ~ v1_funct_1(X0)
% 11.65/2.01      | ~ v1_relat_1(X0)
% 11.65/2.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 11.65/2.01      inference(cnf_transformation,[],[f75]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_522,plain,
% 11.65/2.01      ( ~ v1_funct_1(X0)
% 11.65/2.01      | ~ v1_relat_1(X0)
% 11.65/2.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 11.65/2.01      | sK2 != X0 ),
% 11.65/2.01      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_523,plain,
% 11.65/2.01      ( ~ v1_funct_1(sK2)
% 11.65/2.01      | ~ v1_relat_1(sK2)
% 11.65/2.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.65/2.01      inference(unflattening,[status(thm)],[c_522]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_525,plain,
% 11.65/2.01      ( ~ v1_relat_1(sK2)
% 11.65/2.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_523,c_39]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1348,plain,
% 11.65/2.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 11.65/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1645,plain,
% 11.65/2.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_1348,c_39,c_38,c_523,c_1527]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_9525,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
% 11.65/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.01      inference(light_normalisation,[status(thm)],[c_9520,c_1645]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_9600,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2) ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_9525,c_41,c_1528]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_44968,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 11.65/2.01      inference(demodulation,[status(thm)],[c_44958,c_9600]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1367,plain,
% 11.65/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.65/2.01      | v1_relat_1(X0) = iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_2263,plain,
% 11.65/2.01      ( v1_relat_1(sK3) = iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1360,c_1367]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_2264,plain,
% 11.65/2.01      ( v1_relat_1(sK2) = iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1358,c_1367]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_6,plain,
% 11.65/2.01      ( ~ v1_relat_1(X0)
% 11.65/2.01      | ~ v1_relat_1(X1)
% 11.65/2.01      | ~ v1_relat_1(X2)
% 11.65/2.01      | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
% 11.65/2.01      inference(cnf_transformation,[],[f63]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1375,plain,
% 11.65/2.01      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 11.65/2.01      | v1_relat_1(X1) != iProver_top
% 11.65/2.01      | v1_relat_1(X2) != iProver_top
% 11.65/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_5659,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 11.65/2.01      | v1_funct_1(X0) != iProver_top
% 11.65/2.01      | v1_relat_1(X0) != iProver_top
% 11.65/2.01      | v1_relat_1(X2) != iProver_top
% 11.65/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1371,c_1375]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_19714,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
% 11.65/2.01      | v1_relat_1(X0) != iProver_top
% 11.65/2.01      | v1_relat_1(X1) != iProver_top
% 11.65/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1357,c_5659]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_20705,plain,
% 11.65/2.01      ( v1_relat_1(X1) != iProver_top
% 11.65/2.01      | v1_relat_1(X0) != iProver_top
% 11.65/2.01      | k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_19714,c_41,c_1528]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_20706,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
% 11.65/2.01      | v1_relat_1(X0) != iProver_top
% 11.65/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.65/2.01      inference(renaming,[status(thm)],[c_20705]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_20713,plain,
% 11.65/2.01      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
% 11.65/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_2264,c_20706]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_23,plain,
% 11.65/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.65/2.01      inference(cnf_transformation,[],[f80]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1365,plain,
% 11.65/2.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.65/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_3325,plain,
% 11.65/2.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1358,c_1365]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_35,negated_conjecture,
% 11.65/2.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 11.65/2.01      inference(cnf_transformation,[],[f92]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_3326,plain,
% 11.65/2.01      ( k2_relat_1(sK2) = sK1 ),
% 11.65/2.01      inference(light_normalisation,[status(thm)],[c_3325,c_35]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_19,plain,
% 11.65/2.01      ( ~ v2_funct_1(X0)
% 11.65/2.01      | ~ v1_funct_1(X0)
% 11.65/2.01      | ~ v1_relat_1(X0)
% 11.65/2.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 11.65/2.01      inference(cnf_transformation,[],[f104]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_494,plain,
% 11.65/2.01      ( ~ v1_funct_1(X0)
% 11.65/2.01      | ~ v1_relat_1(X0)
% 11.65/2.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 11.65/2.01      | sK2 != X0 ),
% 11.65/2.01      inference(resolution_lifted,[status(thm)],[c_19,c_33]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_495,plain,
% 11.65/2.01      ( ~ v1_funct_1(sK2)
% 11.65/2.01      | ~ v1_relat_1(sK2)
% 11.65/2.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 11.65/2.01      inference(unflattening,[status(thm)],[c_494]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_497,plain,
% 11.65/2.01      ( ~ v1_relat_1(sK2)
% 11.65/2.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_495,c_39]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1350,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 11.65/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1860,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_1350,c_39,c_38,c_495,c_1527]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_3480,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 11.65/2.01      inference(demodulation,[status(thm)],[c_3326,c_1860]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_20732,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 11.65/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.01      inference(light_normalisation,[status(thm)],[c_20713,c_3480]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_20841,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_2263,c_20732]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_20865,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 11.65/2.01      inference(light_normalisation,[status(thm)],[c_20841,c_6402]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_10,plain,
% 11.65/2.01      ( ~ v1_relat_1(X0)
% 11.65/2.01      | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
% 11.65/2.01      inference(cnf_transformation,[],[f101]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1373,plain,
% 11.65/2.01      ( k5_relat_1(k6_partfun1(X0),X1) = k7_relat_1(X1,X0)
% 11.65/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_2441,plain,
% 11.65/2.01      ( k5_relat_1(k6_partfun1(X0),sK3) = k7_relat_1(sK3,X0) ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_2263,c_1373]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_2306,plain,
% 11.65/2.01      ( v4_relat_1(sK3,sK1) = iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_1360,c_1366]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_5,plain,
% 11.65/2.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 11.65/2.01      inference(cnf_transformation,[],[f62]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_1376,plain,
% 11.65/2.01      ( k7_relat_1(X0,X1) = X0
% 11.65/2.01      | v4_relat_1(X0,X1) != iProver_top
% 11.65/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_4550,plain,
% 11.65/2.01      ( k7_relat_1(sK3,sK1) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 11.65/2.01      inference(superposition,[status(thm)],[c_2306,c_1376]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_4587,plain,
% 11.65/2.01      ( k7_relat_1(sK3,sK1) = sK3 ),
% 11.65/2.01      inference(global_propositional_subsumption,
% 11.65/2.01                [status(thm)],
% 11.65/2.01                [c_4550,c_43,c_1662]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_20866,plain,
% 11.65/2.01      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = sK3 ),
% 11.65/2.01      inference(demodulation,[status(thm)],[c_20865,c_2441,c_4587]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_44972,plain,
% 11.65/2.01      ( k2_funct_1(sK2) = sK3 ),
% 11.65/2.01      inference(light_normalisation,[status(thm)],[c_44968,c_20866]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(c_30,negated_conjecture,
% 11.65/2.01      ( k2_funct_1(sK2) != sK3 ),
% 11.65/2.01      inference(cnf_transformation,[],[f97]) ).
% 11.65/2.01  
% 11.65/2.01  cnf(contradiction,plain,
% 11.65/2.01      ( $false ),
% 11.65/2.01      inference(minisat,[status(thm)],[c_44972,c_30]) ).
% 11.65/2.01  
% 11.65/2.01  
% 11.65/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.65/2.01  
% 11.65/2.01  ------                               Statistics
% 11.65/2.01  
% 11.65/2.01  ------ General
% 11.65/2.01  
% 11.65/2.01  abstr_ref_over_cycles:                  0
% 11.65/2.01  abstr_ref_under_cycles:                 0
% 11.65/2.01  gc_basic_clause_elim:                   0
% 11.65/2.01  forced_gc_time:                         0
% 11.65/2.01  parsing_time:                           0.011
% 11.65/2.01  unif_index_cands_time:                  0.
% 11.65/2.01  unif_index_add_time:                    0.
% 11.65/2.01  orderings_time:                         0.
% 11.65/2.01  out_proof_time:                         0.024
% 11.65/2.01  total_time:                             1.454
% 11.65/2.01  num_of_symbols:                         53
% 11.65/2.01  num_of_terms:                           71094
% 11.65/2.01  
% 11.65/2.01  ------ Preprocessing
% 11.65/2.01  
% 11.65/2.01  num_of_splits:                          0
% 11.65/2.01  num_of_split_atoms:                     0
% 11.65/2.01  num_of_reused_defs:                     0
% 11.65/2.01  num_eq_ax_congr_red:                    12
% 11.65/2.01  num_of_sem_filtered_clauses:            1
% 11.65/2.01  num_of_subtypes:                        0
% 11.65/2.01  monotx_restored_types:                  0
% 11.65/2.01  sat_num_of_epr_types:                   0
% 11.65/2.01  sat_num_of_non_cyclic_types:            0
% 11.65/2.01  sat_guarded_non_collapsed_types:        0
% 11.65/2.01  num_pure_diseq_elim:                    0
% 11.65/2.01  simp_replaced_by:                       0
% 11.65/2.01  res_preprocessed:                       189
% 11.65/2.01  prep_upred:                             0
% 11.65/2.01  prep_unflattend:                        16
% 11.65/2.01  smt_new_axioms:                         0
% 11.65/2.01  pred_elim_cands:                        5
% 11.65/2.01  pred_elim:                              2
% 11.65/2.01  pred_elim_cl:                           0
% 11.65/2.01  pred_elim_cycles:                       4
% 11.65/2.01  merged_defs:                            0
% 11.65/2.01  merged_defs_ncl:                        0
% 11.65/2.01  bin_hyper_res:                          0
% 11.65/2.01  prep_cycles:                            4
% 11.65/2.01  pred_elim_time:                         0.007
% 11.65/2.01  splitting_time:                         0.
% 11.65/2.01  sem_filter_time:                        0.
% 11.65/2.01  monotx_time:                            0.001
% 11.65/2.01  subtype_inf_time:                       0.
% 11.65/2.01  
% 11.65/2.01  ------ Problem properties
% 11.65/2.01  
% 11.65/2.01  clauses:                                39
% 11.65/2.01  conjectures:                            8
% 11.65/2.01  epr:                                    6
% 11.65/2.01  horn:                                   39
% 11.65/2.01  ground:                                 13
% 11.65/2.01  unary:                                  13
% 11.65/2.01  binary:                                 14
% 11.65/2.01  lits:                                   86
% 11.65/2.01  lits_eq:                                22
% 11.65/2.01  fd_pure:                                0
% 11.65/2.01  fd_pseudo:                              0
% 11.65/2.01  fd_cond:                                0
% 11.65/2.01  fd_pseudo_cond:                         1
% 11.65/2.01  ac_symbols:                             0
% 11.65/2.01  
% 11.65/2.01  ------ Propositional Solver
% 11.65/2.01  
% 11.65/2.01  prop_solver_calls:                      36
% 11.65/2.01  prop_fast_solver_calls:                 2170
% 11.65/2.01  smt_solver_calls:                       0
% 11.65/2.01  smt_fast_solver_calls:                  0
% 11.65/2.01  prop_num_of_clauses:                    24383
% 11.65/2.01  prop_preprocess_simplified:             34775
% 11.65/2.01  prop_fo_subsumed:                       224
% 11.65/2.01  prop_solver_time:                       0.
% 11.65/2.01  smt_solver_time:                        0.
% 11.65/2.01  smt_fast_solver_time:                   0.
% 11.65/2.01  prop_fast_solver_time:                  0.
% 11.65/2.01  prop_unsat_core_time:                   0.003
% 11.65/2.01  
% 11.65/2.01  ------ QBF
% 11.65/2.01  
% 11.65/2.01  qbf_q_res:                              0
% 11.65/2.01  qbf_num_tautologies:                    0
% 11.65/2.01  qbf_prep_cycles:                        0
% 11.65/2.01  
% 11.65/2.01  ------ BMC1
% 11.65/2.01  
% 11.65/2.01  bmc1_current_bound:                     -1
% 11.65/2.01  bmc1_last_solved_bound:                 -1
% 11.65/2.01  bmc1_unsat_core_size:                   -1
% 11.65/2.01  bmc1_unsat_core_parents_size:           -1
% 11.65/2.01  bmc1_merge_next_fun:                    0
% 11.65/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.65/2.01  
% 11.65/2.01  ------ Instantiation
% 11.65/2.01  
% 11.65/2.01  inst_num_of_clauses:                    4769
% 11.65/2.01  inst_num_in_passive:                    2025
% 11.65/2.01  inst_num_in_active:                     1973
% 11.65/2.01  inst_num_in_unprocessed:                771
% 11.65/2.01  inst_num_of_loops:                      2120
% 11.65/2.01  inst_num_of_learning_restarts:          0
% 11.65/2.01  inst_num_moves_active_passive:          143
% 11.65/2.01  inst_lit_activity:                      0
% 11.65/2.01  inst_lit_activity_moves:                2
% 11.65/2.01  inst_num_tautologies:                   0
% 11.65/2.01  inst_num_prop_implied:                  0
% 11.65/2.01  inst_num_existing_simplified:           0
% 11.65/2.01  inst_num_eq_res_simplified:             0
% 11.65/2.01  inst_num_child_elim:                    0
% 11.65/2.01  inst_num_of_dismatching_blockings:      6607
% 11.65/2.01  inst_num_of_non_proper_insts:           5242
% 11.65/2.01  inst_num_of_duplicates:                 0
% 11.65/2.01  inst_inst_num_from_inst_to_res:         0
% 11.65/2.01  inst_dismatching_checking_time:         0.
% 11.65/2.01  
% 11.65/2.01  ------ Resolution
% 11.65/2.01  
% 11.65/2.01  res_num_of_clauses:                     0
% 11.65/2.01  res_num_in_passive:                     0
% 11.65/2.01  res_num_in_active:                      0
% 11.65/2.01  res_num_of_loops:                       193
% 11.65/2.01  res_forward_subset_subsumed:            282
% 11.65/2.01  res_backward_subset_subsumed:           0
% 11.65/2.01  res_forward_subsumed:                   0
% 11.65/2.01  res_backward_subsumed:                  0
% 11.65/2.01  res_forward_subsumption_resolution:     0
% 11.65/2.01  res_backward_subsumption_resolution:    0
% 11.65/2.01  res_clause_to_clause_subsumption:       6713
% 11.65/2.01  res_orphan_elimination:                 0
% 11.65/2.01  res_tautology_del:                      245
% 11.65/2.01  res_num_eq_res_simplified:              0
% 11.65/2.01  res_num_sel_changes:                    0
% 11.65/2.01  res_moves_from_active_to_pass:          0
% 11.65/2.01  
% 11.65/2.01  ------ Superposition
% 11.65/2.01  
% 11.65/2.01  sup_time_total:                         0.
% 11.65/2.01  sup_time_generating:                    0.
% 11.65/2.01  sup_time_sim_full:                      0.
% 11.65/2.01  sup_time_sim_immed:                     0.
% 11.65/2.01  
% 11.65/2.01  sup_num_of_clauses:                     2725
% 11.65/2.01  sup_num_in_active:                      367
% 11.65/2.01  sup_num_in_passive:                     2358
% 11.65/2.01  sup_num_of_loops:                       422
% 11.65/2.01  sup_fw_superposition:                   2123
% 11.65/2.01  sup_bw_superposition:                   978
% 11.65/2.01  sup_immediate_simplified:               817
% 11.65/2.01  sup_given_eliminated:                   0
% 11.65/2.01  comparisons_done:                       0
% 11.65/2.01  comparisons_avoided:                    0
% 11.65/2.01  
% 11.65/2.01  ------ Simplifications
% 11.65/2.01  
% 11.65/2.01  
% 11.65/2.01  sim_fw_subset_subsumed:                 27
% 11.65/2.01  sim_bw_subset_subsumed:                 40
% 11.65/2.01  sim_fw_subsumed:                        62
% 11.65/2.01  sim_bw_subsumed:                        11
% 11.65/2.01  sim_fw_subsumption_res:                 0
% 11.65/2.01  sim_bw_subsumption_res:                 0
% 11.65/2.01  sim_tautology_del:                      55
% 11.65/2.01  sim_eq_tautology_del:                   103
% 11.65/2.01  sim_eq_res_simp:                        0
% 11.65/2.01  sim_fw_demodulated:                     222
% 11.65/2.01  sim_bw_demodulated:                     49
% 11.65/2.01  sim_light_normalised:                   548
% 11.65/2.01  sim_joinable_taut:                      0
% 11.65/2.01  sim_joinable_simp:                      0
% 11.65/2.01  sim_ac_normalised:                      0
% 11.65/2.01  sim_smt_subsumption:                    0
% 11.65/2.01  
%------------------------------------------------------------------------------
