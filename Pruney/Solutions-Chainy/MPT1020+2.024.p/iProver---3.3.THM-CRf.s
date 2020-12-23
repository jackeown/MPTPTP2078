%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:09 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :  253 (6823 expanded)
%              Number of clauses        :  171 (2035 expanded)
%              Number of leaves         :   23 (1654 expanded)
%              Depth                    :   31
%              Number of atoms          :  895 (46459 expanded)
%              Number of equality atoms :  417 (3698 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f47,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0))
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK2,X0,X0)
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f53,f52])).

fof(f90,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f93,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f62,f84])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f84])).

fof(f86,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f94,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_912,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_913,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_relset_1(sK0,sK0,sK2) = sK0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_912])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_915,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_913,c_31])).

cnf(c_1147,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_915])).

cnf(c_1167,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1662,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1167])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1172,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | k1_relset_1(X1_51,X2_51,X0_51) = k1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1657,plain,
    ( k1_relset_1(X0_51,X1_51,X2_51) = k1_relat_1(X2_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1172])).

cnf(c_2091,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1662,c_1657])).

cnf(c_2261,plain,
    ( k1_relat_1(sK2) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1147,c_2091])).

cnf(c_12,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_457,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_465,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_457,c_26])).

cnf(c_1162,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_465])).

cnf(c_1667,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1162])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1171,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X5_51)))
    | m1_subset_1(k1_partfun1(X4_51,X5_51,X1_51,X2_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1775,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_3099,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1667,c_38,c_35,c_34,c_31,c_1162,c_1775])).

cnf(c_1165,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1664,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1165])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1168,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X5_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51)
    | k1_partfun1(X4_51,X5_51,X1_51,X2_51,X3_51,X0_51) = k5_relat_1(X3_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1661,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X4_51,X5_51) = k5_relat_1(X4_51,X5_51)
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_funct_1(X4_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1168])).

cnf(c_2574,plain,
    ( k1_partfun1(X0_51,X1_51,sK0,sK0,X2_51,sK2) = k5_relat_1(X2_51,sK2)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_1661])).

cnf(c_43,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2662,plain,
    ( v1_funct_1(X2_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(X0_51,X1_51,sK0,sK0,X2_51,sK2) = k5_relat_1(X2_51,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2574,c_43])).

cnf(c_2663,plain,
    ( k1_partfun1(X0_51,X1_51,sK0,sK0,X2_51,sK2) = k5_relat_1(X2_51,sK2)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_2662])).

cnf(c_2669,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1664,c_2663])).

cnf(c_39,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2742,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2669,c_39])).

cnf(c_3101,plain,
    ( k5_relat_1(sK1,sK2) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_3099,c_2742])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_14,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_629,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_631,plain,
    ( v2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_34,c_31])).

cnf(c_696,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_631])).

cnf(c_697,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(sK2) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_696])).

cnf(c_701,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(sK2) != k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_697,c_34])).

cnf(c_1157,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(X0_51,sK2) != k6_partfun1(k2_relat_1(sK2))
    | k2_funct_1(sK2) = X0_51
    | k1_relat_1(sK2) != k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_701])).

cnf(c_1670,plain,
    ( k5_relat_1(X0_51,sK2) != k6_partfun1(k2_relat_1(sK2))
    | k2_funct_1(sK2) = X0_51
    | k1_relat_1(sK2) != k2_relat_1(X0_51)
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1157])).

cnf(c_46,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1241,plain,
    ( k5_relat_1(X0_51,sK2) != k6_partfun1(k2_relat_1(sK2))
    | k2_funct_1(sK2) = X0_51
    | k1_relat_1(sK2) != k2_relat_1(X0_51)
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1157])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1173,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1763,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1173])).

cnf(c_1841,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1763])).

cnf(c_1842,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1841])).

cnf(c_3614,plain,
    ( v1_relat_1(X0_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | k1_relat_1(sK2) != k2_relat_1(X0_51)
    | k2_funct_1(sK2) = X0_51
    | k5_relat_1(X0_51,sK2) != k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1670,c_46,c_1241,c_1842])).

cnf(c_3615,plain,
    ( k5_relat_1(X0_51,sK2) != k6_partfun1(k2_relat_1(sK2))
    | k2_funct_1(sK2) = X0_51
    | k1_relat_1(sK2) != k2_relat_1(X0_51)
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_3614])).

cnf(c_13,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_405,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_9,c_23])).

cnf(c_415,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_405,c_8])).

cnf(c_488,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_415])).

cnf(c_489,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_610,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_489,c_32])).

cnf(c_611,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_615,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_611,c_34,c_31])).

cnf(c_1161,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_615])).

cnf(c_1668,plain,
    ( k2_relat_1(sK2) = sK0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1161])).

cnf(c_1741,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_2021,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1668,c_31,c_1741])).

cnf(c_3620,plain,
    ( k5_relat_1(X0_51,sK2) != k6_partfun1(sK0)
    | k2_funct_1(sK2) = X0_51
    | k2_relat_1(X0_51) != k1_relat_1(sK2)
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3615,c_2021])).

cnf(c_3625,plain,
    ( k2_funct_1(sK2) = sK1
    | k1_relat_1(sK2) != k2_relat_1(sK1)
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3101,c_3620])).

cnf(c_36,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_489,c_36])).

cnf(c_640,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_644,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_640,c_38,c_35])).

cnf(c_1160,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_644])).

cnf(c_1669,plain,
    ( k2_relat_1(sK1) = sK0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1160])).

cnf(c_1733,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_2050,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1669,c_35,c_1733])).

cnf(c_3626,plain,
    ( k2_funct_1(sK2) = sK1
    | k1_relat_1(sK2) != sK0
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3625,c_2050])).

cnf(c_1751,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1173])).

cnf(c_1810,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1751])).

cnf(c_3627,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK2) = sK1
    | k1_relat_1(sK2) != sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3626])).

cnf(c_3736,plain,
    ( k2_funct_1(sK2) = sK1
    | k1_relat_1(sK2) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3626,c_38,c_35,c_1810,c_3627])).

cnf(c_3738,plain,
    ( k2_funct_1(sK2) = sK1
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2261,c_3736])).

cnf(c_1180,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1211,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1180])).

cnf(c_2,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1176,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1175,plain,
    ( ~ v1_relat_1(X0_51)
    | k2_relat_1(X0_51) != k1_xboole_0
    | k1_xboole_0 = X0_51 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1654,plain,
    ( k2_relat_1(X0_51) != k1_xboole_0
    | k1_xboole_0 = X0_51
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1175])).

cnf(c_2134,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2021,c_1654])).

cnf(c_1183,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_2001,plain,
    ( X0_51 != X1_51
    | X0_51 = sK0
    | sK0 != X1_51 ),
    inference(instantiation,[status(thm)],[c_1183])).

cnf(c_2300,plain,
    ( k1_relat_1(sK2) != X0_51
    | k1_relat_1(sK2) = sK0
    | sK0 != X0_51 ),
    inference(instantiation,[status(thm)],[c_2001])).

cnf(c_2301,plain,
    ( k1_relat_1(sK2) = sK0
    | k1_relat_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2300])).

cnf(c_1187,plain,
    ( X0_51 != X1_51
    | k1_relat_1(X0_51) = k1_relat_1(X1_51) ),
    theory(equality)).

cnf(c_2704,plain,
    ( k1_relat_1(sK2) = k1_relat_1(X0_51)
    | sK2 != X0_51 ),
    inference(instantiation,[status(thm)],[c_1187])).

cnf(c_2705,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2704])).

cnf(c_2303,plain,
    ( X0_51 != X1_51
    | k1_relat_1(sK2) != X1_51
    | k1_relat_1(sK2) = X0_51 ),
    inference(instantiation,[status(thm)],[c_1183])).

cnf(c_2801,plain,
    ( X0_51 != k1_relat_1(X1_51)
    | k1_relat_1(sK2) = X0_51
    | k1_relat_1(sK2) != k1_relat_1(X1_51) ),
    inference(instantiation,[status(thm)],[c_2303])).

cnf(c_2802,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2801])).

cnf(c_4280,plain,
    ( X0_51 != X1_51
    | X0_51 = k1_relat_1(X2_51)
    | k1_relat_1(X2_51) != X1_51 ),
    inference(instantiation,[status(thm)],[c_1183])).

cnf(c_4281,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4280])).

cnf(c_8028,plain,
    ( k2_funct_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3738,c_46,c_1211,c_1176,c_1842,c_2134,c_2261,c_2301,c_2705,c_2802,c_3736,c_4281])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_726,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_631])).

cnf(c_727,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_729,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_34])).

cnf(c_1156,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_729])).

cnf(c_1671,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1156])).

cnf(c_2485,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1671,c_31,c_1156,c_1841])).

cnf(c_8032,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_8028,c_2485])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_36])).

cnf(c_658,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_660,plain,
    ( v2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_658,c_38,c_35])).

cnf(c_754,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_660])).

cnf(c_755,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0,sK1) != k6_partfun1(k2_relat_1(sK1))
    | k2_funct_1(sK1) = X0
    | k1_relat_1(sK1) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_754])).

cnf(c_759,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0,sK1) != k6_partfun1(k2_relat_1(sK1))
    | k2_funct_1(sK1) = X0
    | k1_relat_1(sK1) != k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_755,c_38])).

cnf(c_1154,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0_51,sK1) != k6_partfun1(k2_relat_1(sK1))
    | k2_funct_1(sK1) = X0_51
    | k1_relat_1(sK1) != k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_759])).

cnf(c_1673,plain,
    ( k5_relat_1(X0_51,sK1) != k6_partfun1(k2_relat_1(sK1))
    | k2_funct_1(sK1) = X0_51
    | k1_relat_1(sK1) != k2_relat_1(X0_51)
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1154])).

cnf(c_42,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1246,plain,
    ( k5_relat_1(X0_51,sK1) != k6_partfun1(k2_relat_1(sK1))
    | k2_funct_1(sK1) = X0_51
    | k1_relat_1(sK1) != k2_relat_1(X0_51)
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1154])).

cnf(c_1811,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1810])).

cnf(c_3866,plain,
    ( v1_relat_1(X0_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | k1_relat_1(sK1) != k2_relat_1(X0_51)
    | k2_funct_1(sK1) = X0_51
    | k5_relat_1(X0_51,sK1) != k6_partfun1(k2_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1673,c_42,c_1246,c_1811])).

cnf(c_3867,plain,
    ( k5_relat_1(X0_51,sK1) != k6_partfun1(k2_relat_1(sK1))
    | k2_funct_1(sK1) = X0_51
    | k1_relat_1(sK1) != k2_relat_1(X0_51)
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_3866])).

cnf(c_3872,plain,
    ( k5_relat_1(X0_51,sK1) != k6_partfun1(sK0)
    | k2_funct_1(sK1) = X0_51
    | k2_relat_1(X0_51) != k1_relat_1(sK1)
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3867,c_2050])).

cnf(c_14473,plain,
    ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
    | k2_funct_1(sK1) = sK2
    | k1_relat_1(sK1) != k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8032,c_3872])).

cnf(c_14474,plain,
    ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
    | k2_funct_1(sK1) = sK2
    | k1_relat_1(sK1) != sK0
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14473,c_2021])).

cnf(c_2135,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_1654])).

cnf(c_2244,plain,
    ( k1_relat_1(sK1) != X0_51
    | k1_relat_1(sK1) = sK0
    | sK0 != X0_51 ),
    inference(instantiation,[status(thm)],[c_2001])).

cnf(c_2246,plain,
    ( k1_relat_1(sK1) = sK0
    | k1_relat_1(sK1) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2244])).

cnf(c_2293,plain,
    ( k1_relat_1(sK1) = k1_relat_1(X0_51)
    | sK1 != X0_51 ),
    inference(instantiation,[status(thm)],[c_1187])).

cnf(c_2294,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2293])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_923,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_37])).

cnf(c_924,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_relset_1(sK0,sK0,sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_923])).

cnf(c_926,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_924,c_35])).

cnf(c_1146,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_926])).

cnf(c_2092,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1664,c_1657])).

cnf(c_2295,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1146,c_2092])).

cnf(c_2058,plain,
    ( X0_51 != X1_51
    | k1_relat_1(sK1) != X1_51
    | k1_relat_1(sK1) = X0_51 ),
    inference(instantiation,[status(thm)],[c_1183])).

cnf(c_2779,plain,
    ( X0_51 != k1_relat_1(X1_51)
    | k1_relat_1(sK1) = X0_51
    | k1_relat_1(sK1) != k1_relat_1(X1_51) ),
    inference(instantiation,[status(thm)],[c_2058])).

cnf(c_2780,plain,
    ( k1_relat_1(sK1) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2779])).

cnf(c_1191,plain,
    ( X0_51 != X1_51
    | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
    theory(equality)).

cnf(c_4338,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
    | k1_relat_1(sK2) != sK0 ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_14986,plain,
    ( k2_funct_1(sK1) = sK2
    | k1_relat_1(sK1) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14474,c_42,c_43,c_46,c_1211,c_1176,c_1811,c_1842,c_2134,c_2135,c_2246,c_2261,c_2294,c_2295,c_2301,c_2705,c_2780,c_2802,c_4281,c_4338])).

cnf(c_14988,plain,
    ( k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14986,c_42,c_43,c_46,c_1211,c_1176,c_1811,c_1842,c_2134,c_2135,c_2246,c_2261,c_2294,c_2295,c_2301,c_2705,c_2780,c_2802,c_4281,c_4338,c_14474])).

cnf(c_11,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_29,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_funct_2(sK0,sK1) != X0
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_447,plain,
    ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k2_funct_2(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_1163,plain,
    ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k2_funct_2(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_1666,plain,
    ( sK2 != k2_funct_2(sK0,sK1)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1163])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_676,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_36])).

cnf(c_677,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_679,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_38,c_37,c_35])).

cnf(c_1158,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_679])).

cnf(c_1680,plain,
    ( k2_funct_1(sK1) != sK2
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1666,c_1158])).

cnf(c_14994,plain,
    ( sK2 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14988,c_1680])).

cnf(c_14996,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14994])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14996,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:12:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.69/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/1.50  
% 7.69/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.69/1.50  
% 7.69/1.50  ------  iProver source info
% 7.69/1.50  
% 7.69/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.69/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.69/1.50  git: non_committed_changes: false
% 7.69/1.50  git: last_make_outside_of_git: false
% 7.69/1.50  
% 7.69/1.50  ------ 
% 7.69/1.50  
% 7.69/1.50  ------ Input Options
% 7.69/1.50  
% 7.69/1.50  --out_options                           all
% 7.69/1.50  --tptp_safe_out                         true
% 7.69/1.50  --problem_path                          ""
% 7.69/1.50  --include_path                          ""
% 7.69/1.50  --clausifier                            res/vclausify_rel
% 7.69/1.50  --clausifier_options                    ""
% 7.69/1.50  --stdin                                 false
% 7.69/1.50  --stats_out                             all
% 7.69/1.50  
% 7.69/1.50  ------ General Options
% 7.69/1.50  
% 7.69/1.50  --fof                                   false
% 7.69/1.50  --time_out_real                         305.
% 7.69/1.50  --time_out_virtual                      -1.
% 7.69/1.50  --symbol_type_check                     false
% 7.69/1.50  --clausify_out                          false
% 7.69/1.50  --sig_cnt_out                           false
% 7.69/1.50  --trig_cnt_out                          false
% 7.69/1.50  --trig_cnt_out_tolerance                1.
% 7.69/1.50  --trig_cnt_out_sk_spl                   false
% 7.69/1.50  --abstr_cl_out                          false
% 7.69/1.50  
% 7.69/1.50  ------ Global Options
% 7.69/1.50  
% 7.69/1.50  --schedule                              default
% 7.69/1.50  --add_important_lit                     false
% 7.69/1.50  --prop_solver_per_cl                    1000
% 7.69/1.50  --min_unsat_core                        false
% 7.69/1.50  --soft_assumptions                      false
% 7.69/1.50  --soft_lemma_size                       3
% 7.69/1.50  --prop_impl_unit_size                   0
% 7.69/1.50  --prop_impl_unit                        []
% 7.69/1.50  --share_sel_clauses                     true
% 7.69/1.50  --reset_solvers                         false
% 7.69/1.50  --bc_imp_inh                            [conj_cone]
% 7.69/1.50  --conj_cone_tolerance                   3.
% 7.69/1.50  --extra_neg_conj                        none
% 7.69/1.50  --large_theory_mode                     true
% 7.69/1.50  --prolific_symb_bound                   200
% 7.69/1.50  --lt_threshold                          2000
% 7.69/1.50  --clause_weak_htbl                      true
% 7.69/1.50  --gc_record_bc_elim                     false
% 7.69/1.50  
% 7.69/1.50  ------ Preprocessing Options
% 7.69/1.50  
% 7.69/1.50  --preprocessing_flag                    true
% 7.69/1.50  --time_out_prep_mult                    0.1
% 7.69/1.50  --splitting_mode                        input
% 7.69/1.50  --splitting_grd                         true
% 7.69/1.50  --splitting_cvd                         false
% 7.69/1.50  --splitting_cvd_svl                     false
% 7.69/1.50  --splitting_nvd                         32
% 7.69/1.50  --sub_typing                            true
% 7.69/1.50  --prep_gs_sim                           true
% 7.69/1.50  --prep_unflatten                        true
% 7.69/1.50  --prep_res_sim                          true
% 7.69/1.50  --prep_upred                            true
% 7.69/1.50  --prep_sem_filter                       exhaustive
% 7.69/1.50  --prep_sem_filter_out                   false
% 7.69/1.50  --pred_elim                             true
% 7.69/1.50  --res_sim_input                         true
% 7.69/1.50  --eq_ax_congr_red                       true
% 7.69/1.50  --pure_diseq_elim                       true
% 7.69/1.50  --brand_transform                       false
% 7.69/1.50  --non_eq_to_eq                          false
% 7.69/1.50  --prep_def_merge                        true
% 7.69/1.50  --prep_def_merge_prop_impl              false
% 7.69/1.50  --prep_def_merge_mbd                    true
% 7.69/1.50  --prep_def_merge_tr_red                 false
% 7.69/1.50  --prep_def_merge_tr_cl                  false
% 7.69/1.50  --smt_preprocessing                     true
% 7.69/1.50  --smt_ac_axioms                         fast
% 7.69/1.50  --preprocessed_out                      false
% 7.69/1.50  --preprocessed_stats                    false
% 7.69/1.50  
% 7.69/1.50  ------ Abstraction refinement Options
% 7.69/1.50  
% 7.69/1.50  --abstr_ref                             []
% 7.69/1.50  --abstr_ref_prep                        false
% 7.69/1.50  --abstr_ref_until_sat                   false
% 7.69/1.50  --abstr_ref_sig_restrict                funpre
% 7.69/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.69/1.50  --abstr_ref_under                       []
% 7.69/1.50  
% 7.69/1.50  ------ SAT Options
% 7.69/1.50  
% 7.69/1.50  --sat_mode                              false
% 7.69/1.50  --sat_fm_restart_options                ""
% 7.69/1.50  --sat_gr_def                            false
% 7.69/1.50  --sat_epr_types                         true
% 7.69/1.50  --sat_non_cyclic_types                  false
% 7.69/1.50  --sat_finite_models                     false
% 7.69/1.50  --sat_fm_lemmas                         false
% 7.69/1.50  --sat_fm_prep                           false
% 7.69/1.50  --sat_fm_uc_incr                        true
% 7.69/1.50  --sat_out_model                         small
% 7.69/1.50  --sat_out_clauses                       false
% 7.69/1.50  
% 7.69/1.50  ------ QBF Options
% 7.69/1.50  
% 7.69/1.50  --qbf_mode                              false
% 7.69/1.50  --qbf_elim_univ                         false
% 7.69/1.50  --qbf_dom_inst                          none
% 7.69/1.50  --qbf_dom_pre_inst                      false
% 7.69/1.50  --qbf_sk_in                             false
% 7.69/1.50  --qbf_pred_elim                         true
% 7.69/1.50  --qbf_split                             512
% 7.69/1.50  
% 7.69/1.50  ------ BMC1 Options
% 7.69/1.50  
% 7.69/1.50  --bmc1_incremental                      false
% 7.69/1.50  --bmc1_axioms                           reachable_all
% 7.69/1.50  --bmc1_min_bound                        0
% 7.69/1.50  --bmc1_max_bound                        -1
% 7.69/1.50  --bmc1_max_bound_default                -1
% 7.69/1.50  --bmc1_symbol_reachability              true
% 7.69/1.50  --bmc1_property_lemmas                  false
% 7.69/1.50  --bmc1_k_induction                      false
% 7.69/1.50  --bmc1_non_equiv_states                 false
% 7.69/1.50  --bmc1_deadlock                         false
% 7.69/1.50  --bmc1_ucm                              false
% 7.69/1.50  --bmc1_add_unsat_core                   none
% 7.69/1.50  --bmc1_unsat_core_children              false
% 7.69/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.69/1.50  --bmc1_out_stat                         full
% 7.69/1.50  --bmc1_ground_init                      false
% 7.69/1.50  --bmc1_pre_inst_next_state              false
% 7.69/1.50  --bmc1_pre_inst_state                   false
% 7.69/1.50  --bmc1_pre_inst_reach_state             false
% 7.69/1.50  --bmc1_out_unsat_core                   false
% 7.69/1.50  --bmc1_aig_witness_out                  false
% 7.69/1.50  --bmc1_verbose                          false
% 7.69/1.50  --bmc1_dump_clauses_tptp                false
% 7.69/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.69/1.50  --bmc1_dump_file                        -
% 7.69/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.69/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.69/1.50  --bmc1_ucm_extend_mode                  1
% 7.69/1.50  --bmc1_ucm_init_mode                    2
% 7.69/1.50  --bmc1_ucm_cone_mode                    none
% 7.69/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.69/1.50  --bmc1_ucm_relax_model                  4
% 7.69/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.69/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.69/1.50  --bmc1_ucm_layered_model                none
% 7.69/1.50  --bmc1_ucm_max_lemma_size               10
% 7.69/1.50  
% 7.69/1.50  ------ AIG Options
% 7.69/1.50  
% 7.69/1.50  --aig_mode                              false
% 7.69/1.50  
% 7.69/1.50  ------ Instantiation Options
% 7.69/1.50  
% 7.69/1.50  --instantiation_flag                    true
% 7.69/1.50  --inst_sos_flag                         true
% 7.69/1.50  --inst_sos_phase                        true
% 7.69/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.69/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.69/1.50  --inst_lit_sel_side                     num_symb
% 7.69/1.50  --inst_solver_per_active                1400
% 7.69/1.50  --inst_solver_calls_frac                1.
% 7.69/1.50  --inst_passive_queue_type               priority_queues
% 7.69/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.69/1.50  --inst_passive_queues_freq              [25;2]
% 7.69/1.50  --inst_dismatching                      true
% 7.69/1.50  --inst_eager_unprocessed_to_passive     true
% 7.69/1.50  --inst_prop_sim_given                   true
% 7.69/1.50  --inst_prop_sim_new                     false
% 7.69/1.50  --inst_subs_new                         false
% 7.69/1.50  --inst_eq_res_simp                      false
% 7.69/1.50  --inst_subs_given                       false
% 7.69/1.50  --inst_orphan_elimination               true
% 7.69/1.50  --inst_learning_loop_flag               true
% 7.69/1.50  --inst_learning_start                   3000
% 7.69/1.50  --inst_learning_factor                  2
% 7.69/1.50  --inst_start_prop_sim_after_learn       3
% 7.69/1.50  --inst_sel_renew                        solver
% 7.69/1.50  --inst_lit_activity_flag                true
% 7.69/1.50  --inst_restr_to_given                   false
% 7.69/1.50  --inst_activity_threshold               500
% 7.69/1.50  --inst_out_proof                        true
% 7.69/1.50  
% 7.69/1.50  ------ Resolution Options
% 7.69/1.50  
% 7.69/1.50  --resolution_flag                       true
% 7.69/1.50  --res_lit_sel                           adaptive
% 7.69/1.50  --res_lit_sel_side                      none
% 7.69/1.50  --res_ordering                          kbo
% 7.69/1.50  --res_to_prop_solver                    active
% 7.69/1.50  --res_prop_simpl_new                    false
% 7.69/1.50  --res_prop_simpl_given                  true
% 7.69/1.50  --res_passive_queue_type                priority_queues
% 7.69/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.69/1.50  --res_passive_queues_freq               [15;5]
% 7.69/1.50  --res_forward_subs                      full
% 7.69/1.50  --res_backward_subs                     full
% 7.69/1.50  --res_forward_subs_resolution           true
% 7.69/1.50  --res_backward_subs_resolution          true
% 7.69/1.50  --res_orphan_elimination                true
% 7.69/1.50  --res_time_limit                        2.
% 7.69/1.50  --res_out_proof                         true
% 7.69/1.50  
% 7.69/1.50  ------ Superposition Options
% 7.69/1.50  
% 7.69/1.50  --superposition_flag                    true
% 7.69/1.50  --sup_passive_queue_type                priority_queues
% 7.69/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.69/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.69/1.50  --demod_completeness_check              fast
% 7.69/1.50  --demod_use_ground                      true
% 7.69/1.50  --sup_to_prop_solver                    passive
% 7.69/1.50  --sup_prop_simpl_new                    true
% 7.69/1.50  --sup_prop_simpl_given                  true
% 7.69/1.50  --sup_fun_splitting                     true
% 7.69/1.50  --sup_smt_interval                      50000
% 7.69/1.50  
% 7.69/1.50  ------ Superposition Simplification Setup
% 7.69/1.50  
% 7.69/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.69/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.69/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.69/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.69/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.69/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.69/1.50  --sup_immed_triv                        [TrivRules]
% 7.69/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.50  --sup_immed_bw_main                     []
% 7.69/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.69/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.69/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.50  --sup_input_bw                          []
% 7.69/1.50  
% 7.69/1.50  ------ Combination Options
% 7.69/1.50  
% 7.69/1.50  --comb_res_mult                         3
% 7.69/1.50  --comb_sup_mult                         2
% 7.69/1.50  --comb_inst_mult                        10
% 7.69/1.50  
% 7.69/1.50  ------ Debug Options
% 7.69/1.50  
% 7.69/1.50  --dbg_backtrace                         false
% 7.69/1.50  --dbg_dump_prop_clauses                 false
% 7.69/1.50  --dbg_dump_prop_clauses_file            -
% 7.69/1.50  --dbg_out_stat                          false
% 7.69/1.50  ------ Parsing...
% 7.69/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.69/1.50  
% 7.69/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 7.69/1.50  
% 7.69/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.69/1.50  
% 7.69/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.69/1.50  ------ Proving...
% 7.69/1.50  ------ Problem Properties 
% 7.69/1.50  
% 7.69/1.50  
% 7.69/1.50  clauses                                 34
% 7.69/1.50  conjectures                             4
% 7.69/1.50  EPR                                     2
% 7.69/1.50  Horn                                    30
% 7.69/1.50  unary                                   10
% 7.69/1.50  binary                                  13
% 7.69/1.50  lits                                    83
% 7.69/1.50  lits eq                                 40
% 7.69/1.50  fd_pure                                 0
% 7.69/1.50  fd_pseudo                               0
% 7.69/1.50  fd_cond                                 4
% 7.69/1.50  fd_pseudo_cond                          0
% 7.69/1.50  AC symbols                              0
% 7.69/1.50  
% 7.69/1.50  ------ Schedule dynamic 5 is on 
% 7.69/1.50  
% 7.69/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.69/1.50  
% 7.69/1.50  
% 7.69/1.50  ------ 
% 7.69/1.50  Current options:
% 7.69/1.50  ------ 
% 7.69/1.50  
% 7.69/1.50  ------ Input Options
% 7.69/1.50  
% 7.69/1.50  --out_options                           all
% 7.69/1.50  --tptp_safe_out                         true
% 7.69/1.50  --problem_path                          ""
% 7.69/1.50  --include_path                          ""
% 7.69/1.50  --clausifier                            res/vclausify_rel
% 7.69/1.50  --clausifier_options                    ""
% 7.69/1.50  --stdin                                 false
% 7.69/1.50  --stats_out                             all
% 7.69/1.50  
% 7.69/1.50  ------ General Options
% 7.69/1.50  
% 7.69/1.50  --fof                                   false
% 7.69/1.50  --time_out_real                         305.
% 7.69/1.50  --time_out_virtual                      -1.
% 7.69/1.50  --symbol_type_check                     false
% 7.69/1.50  --clausify_out                          false
% 7.69/1.50  --sig_cnt_out                           false
% 7.69/1.50  --trig_cnt_out                          false
% 7.69/1.50  --trig_cnt_out_tolerance                1.
% 7.69/1.50  --trig_cnt_out_sk_spl                   false
% 7.69/1.50  --abstr_cl_out                          false
% 7.69/1.50  
% 7.69/1.50  ------ Global Options
% 7.69/1.50  
% 7.69/1.50  --schedule                              default
% 7.69/1.50  --add_important_lit                     false
% 7.69/1.50  --prop_solver_per_cl                    1000
% 7.69/1.50  --min_unsat_core                        false
% 7.69/1.50  --soft_assumptions                      false
% 7.69/1.50  --soft_lemma_size                       3
% 7.69/1.50  --prop_impl_unit_size                   0
% 7.69/1.50  --prop_impl_unit                        []
% 7.69/1.50  --share_sel_clauses                     true
% 7.69/1.50  --reset_solvers                         false
% 7.69/1.50  --bc_imp_inh                            [conj_cone]
% 7.69/1.50  --conj_cone_tolerance                   3.
% 7.69/1.50  --extra_neg_conj                        none
% 7.69/1.50  --large_theory_mode                     true
% 7.69/1.50  --prolific_symb_bound                   200
% 7.69/1.50  --lt_threshold                          2000
% 7.69/1.50  --clause_weak_htbl                      true
% 7.69/1.50  --gc_record_bc_elim                     false
% 7.69/1.50  
% 7.69/1.50  ------ Preprocessing Options
% 7.69/1.50  
% 7.69/1.50  --preprocessing_flag                    true
% 7.69/1.50  --time_out_prep_mult                    0.1
% 7.69/1.50  --splitting_mode                        input
% 7.69/1.50  --splitting_grd                         true
% 7.69/1.50  --splitting_cvd                         false
% 7.69/1.50  --splitting_cvd_svl                     false
% 7.69/1.50  --splitting_nvd                         32
% 7.69/1.50  --sub_typing                            true
% 7.69/1.50  --prep_gs_sim                           true
% 7.69/1.50  --prep_unflatten                        true
% 7.69/1.50  --prep_res_sim                          true
% 7.69/1.50  --prep_upred                            true
% 7.69/1.50  --prep_sem_filter                       exhaustive
% 7.69/1.50  --prep_sem_filter_out                   false
% 7.69/1.50  --pred_elim                             true
% 7.69/1.50  --res_sim_input                         true
% 7.69/1.50  --eq_ax_congr_red                       true
% 7.69/1.50  --pure_diseq_elim                       true
% 7.69/1.50  --brand_transform                       false
% 7.69/1.50  --non_eq_to_eq                          false
% 7.69/1.50  --prep_def_merge                        true
% 7.69/1.50  --prep_def_merge_prop_impl              false
% 7.69/1.50  --prep_def_merge_mbd                    true
% 7.69/1.50  --prep_def_merge_tr_red                 false
% 7.69/1.50  --prep_def_merge_tr_cl                  false
% 7.69/1.50  --smt_preprocessing                     true
% 7.69/1.50  --smt_ac_axioms                         fast
% 7.69/1.50  --preprocessed_out                      false
% 7.69/1.50  --preprocessed_stats                    false
% 7.69/1.50  
% 7.69/1.50  ------ Abstraction refinement Options
% 7.69/1.50  
% 7.69/1.50  --abstr_ref                             []
% 7.69/1.50  --abstr_ref_prep                        false
% 7.69/1.50  --abstr_ref_until_sat                   false
% 7.69/1.50  --abstr_ref_sig_restrict                funpre
% 7.69/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.69/1.50  --abstr_ref_under                       []
% 7.69/1.50  
% 7.69/1.50  ------ SAT Options
% 7.69/1.50  
% 7.69/1.50  --sat_mode                              false
% 7.69/1.50  --sat_fm_restart_options                ""
% 7.69/1.50  --sat_gr_def                            false
% 7.69/1.50  --sat_epr_types                         true
% 7.69/1.50  --sat_non_cyclic_types                  false
% 7.69/1.50  --sat_finite_models                     false
% 7.69/1.50  --sat_fm_lemmas                         false
% 7.69/1.50  --sat_fm_prep                           false
% 7.69/1.50  --sat_fm_uc_incr                        true
% 7.69/1.50  --sat_out_model                         small
% 7.69/1.50  --sat_out_clauses                       false
% 7.69/1.50  
% 7.69/1.50  ------ QBF Options
% 7.69/1.50  
% 7.69/1.50  --qbf_mode                              false
% 7.69/1.50  --qbf_elim_univ                         false
% 7.69/1.50  --qbf_dom_inst                          none
% 7.69/1.50  --qbf_dom_pre_inst                      false
% 7.69/1.50  --qbf_sk_in                             false
% 7.69/1.50  --qbf_pred_elim                         true
% 7.69/1.50  --qbf_split                             512
% 7.69/1.50  
% 7.69/1.50  ------ BMC1 Options
% 7.69/1.50  
% 7.69/1.50  --bmc1_incremental                      false
% 7.69/1.50  --bmc1_axioms                           reachable_all
% 7.69/1.50  --bmc1_min_bound                        0
% 7.69/1.50  --bmc1_max_bound                        -1
% 7.69/1.50  --bmc1_max_bound_default                -1
% 7.69/1.50  --bmc1_symbol_reachability              true
% 7.69/1.50  --bmc1_property_lemmas                  false
% 7.69/1.50  --bmc1_k_induction                      false
% 7.69/1.50  --bmc1_non_equiv_states                 false
% 7.69/1.50  --bmc1_deadlock                         false
% 7.69/1.50  --bmc1_ucm                              false
% 7.69/1.50  --bmc1_add_unsat_core                   none
% 7.69/1.50  --bmc1_unsat_core_children              false
% 7.69/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.69/1.50  --bmc1_out_stat                         full
% 7.69/1.50  --bmc1_ground_init                      false
% 7.69/1.50  --bmc1_pre_inst_next_state              false
% 7.69/1.50  --bmc1_pre_inst_state                   false
% 7.69/1.50  --bmc1_pre_inst_reach_state             false
% 7.69/1.50  --bmc1_out_unsat_core                   false
% 7.69/1.50  --bmc1_aig_witness_out                  false
% 7.69/1.50  --bmc1_verbose                          false
% 7.69/1.50  --bmc1_dump_clauses_tptp                false
% 7.69/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.69/1.50  --bmc1_dump_file                        -
% 7.69/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.69/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.69/1.50  --bmc1_ucm_extend_mode                  1
% 7.69/1.50  --bmc1_ucm_init_mode                    2
% 7.69/1.50  --bmc1_ucm_cone_mode                    none
% 7.69/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.69/1.50  --bmc1_ucm_relax_model                  4
% 7.69/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.69/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.69/1.50  --bmc1_ucm_layered_model                none
% 7.69/1.50  --bmc1_ucm_max_lemma_size               10
% 7.69/1.50  
% 7.69/1.50  ------ AIG Options
% 7.69/1.50  
% 7.69/1.50  --aig_mode                              false
% 7.69/1.50  
% 7.69/1.50  ------ Instantiation Options
% 7.69/1.50  
% 7.69/1.50  --instantiation_flag                    true
% 7.69/1.50  --inst_sos_flag                         true
% 7.69/1.50  --inst_sos_phase                        true
% 7.69/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.69/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.69/1.50  --inst_lit_sel_side                     none
% 7.69/1.50  --inst_solver_per_active                1400
% 7.69/1.50  --inst_solver_calls_frac                1.
% 7.69/1.50  --inst_passive_queue_type               priority_queues
% 7.69/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.69/1.50  --inst_passive_queues_freq              [25;2]
% 7.69/1.50  --inst_dismatching                      true
% 7.69/1.50  --inst_eager_unprocessed_to_passive     true
% 7.69/1.50  --inst_prop_sim_given                   true
% 7.69/1.50  --inst_prop_sim_new                     false
% 7.69/1.50  --inst_subs_new                         false
% 7.69/1.50  --inst_eq_res_simp                      false
% 7.69/1.50  --inst_subs_given                       false
% 7.69/1.50  --inst_orphan_elimination               true
% 7.69/1.50  --inst_learning_loop_flag               true
% 7.69/1.50  --inst_learning_start                   3000
% 7.69/1.50  --inst_learning_factor                  2
% 7.69/1.50  --inst_start_prop_sim_after_learn       3
% 7.69/1.50  --inst_sel_renew                        solver
% 7.69/1.50  --inst_lit_activity_flag                true
% 7.69/1.50  --inst_restr_to_given                   false
% 7.69/1.50  --inst_activity_threshold               500
% 7.69/1.50  --inst_out_proof                        true
% 7.69/1.50  
% 7.69/1.50  ------ Resolution Options
% 7.69/1.50  
% 7.69/1.50  --resolution_flag                       false
% 7.69/1.50  --res_lit_sel                           adaptive
% 7.69/1.50  --res_lit_sel_side                      none
% 7.69/1.50  --res_ordering                          kbo
% 7.69/1.50  --res_to_prop_solver                    active
% 7.69/1.50  --res_prop_simpl_new                    false
% 7.69/1.50  --res_prop_simpl_given                  true
% 7.69/1.50  --res_passive_queue_type                priority_queues
% 7.69/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.69/1.50  --res_passive_queues_freq               [15;5]
% 7.69/1.50  --res_forward_subs                      full
% 7.69/1.50  --res_backward_subs                     full
% 7.69/1.50  --res_forward_subs_resolution           true
% 7.69/1.50  --res_backward_subs_resolution          true
% 7.69/1.50  --res_orphan_elimination                true
% 7.69/1.50  --res_time_limit                        2.
% 7.69/1.50  --res_out_proof                         true
% 7.69/1.50  
% 7.69/1.50  ------ Superposition Options
% 7.69/1.50  
% 7.69/1.50  --superposition_flag                    true
% 7.69/1.50  --sup_passive_queue_type                priority_queues
% 7.69/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.69/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.69/1.50  --demod_completeness_check              fast
% 7.69/1.50  --demod_use_ground                      true
% 7.69/1.50  --sup_to_prop_solver                    passive
% 7.69/1.50  --sup_prop_simpl_new                    true
% 7.69/1.50  --sup_prop_simpl_given                  true
% 7.69/1.50  --sup_fun_splitting                     true
% 7.69/1.50  --sup_smt_interval                      50000
% 7.69/1.50  
% 7.69/1.50  ------ Superposition Simplification Setup
% 7.69/1.50  
% 7.69/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.69/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.69/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.69/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.69/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.69/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.69/1.50  --sup_immed_triv                        [TrivRules]
% 7.69/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.50  --sup_immed_bw_main                     []
% 7.69/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.69/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.69/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.50  --sup_input_bw                          []
% 7.69/1.50  
% 7.69/1.50  ------ Combination Options
% 7.69/1.50  
% 7.69/1.50  --comb_res_mult                         3
% 7.69/1.50  --comb_sup_mult                         2
% 7.69/1.50  --comb_inst_mult                        10
% 7.69/1.50  
% 7.69/1.50  ------ Debug Options
% 7.69/1.50  
% 7.69/1.50  --dbg_backtrace                         false
% 7.69/1.50  --dbg_dump_prop_clauses                 false
% 7.69/1.50  --dbg_dump_prop_clauses_file            -
% 7.69/1.50  --dbg_out_stat                          false
% 7.69/1.50  
% 7.69/1.50  
% 7.69/1.50  
% 7.69/1.50  
% 7.69/1.50  ------ Proving...
% 7.69/1.50  
% 7.69/1.50  
% 7.69/1.50  % SZS status Theorem for theBenchmark.p
% 7.69/1.50  
% 7.69/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.69/1.50  
% 7.69/1.50  fof(f12,axiom,(
% 7.69/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f37,plain,(
% 7.69/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.50    inference(ennf_transformation,[],[f12])).
% 7.69/1.50  
% 7.69/1.50  fof(f38,plain,(
% 7.69/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.50    inference(flattening,[],[f37])).
% 7.69/1.50  
% 7.69/1.50  fof(f50,plain,(
% 7.69/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.50    inference(nnf_transformation,[],[f38])).
% 7.69/1.50  
% 7.69/1.50  fof(f71,plain,(
% 7.69/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.69/1.50    inference(cnf_transformation,[],[f50])).
% 7.69/1.50  
% 7.69/1.50  fof(f19,conjecture,(
% 7.69/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f20,negated_conjecture,(
% 7.69/1.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 7.69/1.50    inference(negated_conjecture,[],[f19])).
% 7.69/1.50  
% 7.69/1.50  fof(f47,plain,(
% 7.69/1.50    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 7.69/1.50    inference(ennf_transformation,[],[f20])).
% 7.69/1.50  
% 7.69/1.50  fof(f48,plain,(
% 7.69/1.50    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 7.69/1.50    inference(flattening,[],[f47])).
% 7.69/1.50  
% 7.69/1.50  fof(f53,plain,(
% 7.69/1.50    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 7.69/1.50    introduced(choice_axiom,[])).
% 7.69/1.50  
% 7.69/1.50  fof(f52,plain,(
% 7.69/1.50    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 7.69/1.50    introduced(choice_axiom,[])).
% 7.69/1.50  
% 7.69/1.50  fof(f54,plain,(
% 7.69/1.50    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 7.69/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f53,f52])).
% 7.69/1.50  
% 7.69/1.50  fof(f90,plain,(
% 7.69/1.50    v1_funct_2(sK2,sK0,sK0)),
% 7.69/1.50    inference(cnf_transformation,[],[f54])).
% 7.69/1.50  
% 7.69/1.50  fof(f92,plain,(
% 7.69/1.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 7.69/1.50    inference(cnf_transformation,[],[f54])).
% 7.69/1.50  
% 7.69/1.50  fof(f9,axiom,(
% 7.69/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f32,plain,(
% 7.69/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.50    inference(ennf_transformation,[],[f9])).
% 7.69/1.50  
% 7.69/1.50  fof(f65,plain,(
% 7.69/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.69/1.50    inference(cnf_transformation,[],[f32])).
% 7.69/1.50  
% 7.69/1.50  fof(f10,axiom,(
% 7.69/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f33,plain,(
% 7.69/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.69/1.50    inference(ennf_transformation,[],[f10])).
% 7.69/1.50  
% 7.69/1.50  fof(f34,plain,(
% 7.69/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.50    inference(flattening,[],[f33])).
% 7.69/1.50  
% 7.69/1.50  fof(f49,plain,(
% 7.69/1.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.50    inference(nnf_transformation,[],[f34])).
% 7.69/1.50  
% 7.69/1.50  fof(f66,plain,(
% 7.69/1.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.69/1.50    inference(cnf_transformation,[],[f49])).
% 7.69/1.50  
% 7.69/1.50  fof(f93,plain,(
% 7.69/1.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 7.69/1.50    inference(cnf_transformation,[],[f54])).
% 7.69/1.50  
% 7.69/1.50  fof(f15,axiom,(
% 7.69/1.50    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f21,plain,(
% 7.69/1.50    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.69/1.50    inference(pure_predicate_removal,[],[f15])).
% 7.69/1.50  
% 7.69/1.50  fof(f81,plain,(
% 7.69/1.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.69/1.50    inference(cnf_transformation,[],[f21])).
% 7.69/1.50  
% 7.69/1.50  fof(f85,plain,(
% 7.69/1.50    v1_funct_1(sK1)),
% 7.69/1.50    inference(cnf_transformation,[],[f54])).
% 7.69/1.50  
% 7.69/1.50  fof(f88,plain,(
% 7.69/1.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 7.69/1.50    inference(cnf_transformation,[],[f54])).
% 7.69/1.50  
% 7.69/1.50  fof(f89,plain,(
% 7.69/1.50    v1_funct_1(sK2)),
% 7.69/1.50    inference(cnf_transformation,[],[f54])).
% 7.69/1.50  
% 7.69/1.50  fof(f14,axiom,(
% 7.69/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f41,plain,(
% 7.69/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.69/1.50    inference(ennf_transformation,[],[f14])).
% 7.69/1.50  
% 7.69/1.50  fof(f42,plain,(
% 7.69/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.69/1.50    inference(flattening,[],[f41])).
% 7.69/1.50  
% 7.69/1.50  fof(f80,plain,(
% 7.69/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.69/1.50    inference(cnf_transformation,[],[f42])).
% 7.69/1.50  
% 7.69/1.50  fof(f16,axiom,(
% 7.69/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f43,plain,(
% 7.69/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.69/1.50    inference(ennf_transformation,[],[f16])).
% 7.69/1.50  
% 7.69/1.50  fof(f44,plain,(
% 7.69/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.69/1.50    inference(flattening,[],[f43])).
% 7.69/1.50  
% 7.69/1.50  fof(f82,plain,(
% 7.69/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.69/1.50    inference(cnf_transformation,[],[f44])).
% 7.69/1.50  
% 7.69/1.50  fof(f6,axiom,(
% 7.69/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f28,plain,(
% 7.69/1.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.69/1.50    inference(ennf_transformation,[],[f6])).
% 7.69/1.50  
% 7.69/1.50  fof(f29,plain,(
% 7.69/1.50    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.69/1.50    inference(flattening,[],[f28])).
% 7.69/1.50  
% 7.69/1.50  fof(f62,plain,(
% 7.69/1.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.69/1.50    inference(cnf_transformation,[],[f29])).
% 7.69/1.50  
% 7.69/1.50  fof(f18,axiom,(
% 7.69/1.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f84,plain,(
% 7.69/1.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.69/1.50    inference(cnf_transformation,[],[f18])).
% 7.69/1.50  
% 7.69/1.50  fof(f97,plain,(
% 7.69/1.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.69/1.50    inference(definition_unfolding,[],[f62,f84])).
% 7.69/1.50  
% 7.69/1.50  fof(f11,axiom,(
% 7.69/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f35,plain,(
% 7.69/1.50    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.50    inference(ennf_transformation,[],[f11])).
% 7.69/1.50  
% 7.69/1.50  fof(f36,plain,(
% 7.69/1.50    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.50    inference(flattening,[],[f35])).
% 7.69/1.50  
% 7.69/1.50  fof(f69,plain,(
% 7.69/1.50    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.69/1.50    inference(cnf_transformation,[],[f36])).
% 7.69/1.50  
% 7.69/1.50  fof(f91,plain,(
% 7.69/1.50    v3_funct_2(sK2,sK0,sK0)),
% 7.69/1.50    inference(cnf_transformation,[],[f54])).
% 7.69/1.50  
% 7.69/1.50  fof(f7,axiom,(
% 7.69/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f30,plain,(
% 7.69/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.50    inference(ennf_transformation,[],[f7])).
% 7.69/1.50  
% 7.69/1.50  fof(f63,plain,(
% 7.69/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.69/1.50    inference(cnf_transformation,[],[f30])).
% 7.69/1.50  
% 7.69/1.50  fof(f70,plain,(
% 7.69/1.50    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.69/1.50    inference(cnf_transformation,[],[f36])).
% 7.69/1.50  
% 7.69/1.50  fof(f8,axiom,(
% 7.69/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f22,plain,(
% 7.69/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.69/1.50    inference(pure_predicate_removal,[],[f8])).
% 7.69/1.50  
% 7.69/1.50  fof(f31,plain,(
% 7.69/1.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.50    inference(ennf_transformation,[],[f22])).
% 7.69/1.50  
% 7.69/1.50  fof(f64,plain,(
% 7.69/1.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.69/1.50    inference(cnf_transformation,[],[f31])).
% 7.69/1.50  
% 7.69/1.50  fof(f13,axiom,(
% 7.69/1.50    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f39,plain,(
% 7.69/1.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.69/1.50    inference(ennf_transformation,[],[f13])).
% 7.69/1.50  
% 7.69/1.50  fof(f40,plain,(
% 7.69/1.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.69/1.50    inference(flattening,[],[f39])).
% 7.69/1.50  
% 7.69/1.50  fof(f51,plain,(
% 7.69/1.50    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.69/1.50    inference(nnf_transformation,[],[f40])).
% 7.69/1.50  
% 7.69/1.50  fof(f77,plain,(
% 7.69/1.50    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.69/1.50    inference(cnf_transformation,[],[f51])).
% 7.69/1.50  
% 7.69/1.50  fof(f87,plain,(
% 7.69/1.50    v3_funct_2(sK1,sK0,sK0)),
% 7.69/1.50    inference(cnf_transformation,[],[f54])).
% 7.69/1.50  
% 7.69/1.50  fof(f3,axiom,(
% 7.69/1.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f56,plain,(
% 7.69/1.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.69/1.50    inference(cnf_transformation,[],[f3])).
% 7.69/1.50  
% 7.69/1.50  fof(f4,axiom,(
% 7.69/1.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f24,plain,(
% 7.69/1.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.69/1.50    inference(ennf_transformation,[],[f4])).
% 7.69/1.50  
% 7.69/1.50  fof(f25,plain,(
% 7.69/1.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.69/1.50    inference(flattening,[],[f24])).
% 7.69/1.50  
% 7.69/1.50  fof(f59,plain,(
% 7.69/1.50    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.69/1.50    inference(cnf_transformation,[],[f25])).
% 7.69/1.50  
% 7.69/1.50  fof(f5,axiom,(
% 7.69/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f26,plain,(
% 7.69/1.50    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.69/1.50    inference(ennf_transformation,[],[f5])).
% 7.69/1.50  
% 7.69/1.50  fof(f27,plain,(
% 7.69/1.50    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.69/1.50    inference(flattening,[],[f26])).
% 7.69/1.50  
% 7.69/1.50  fof(f60,plain,(
% 7.69/1.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.69/1.50    inference(cnf_transformation,[],[f27])).
% 7.69/1.50  
% 7.69/1.50  fof(f96,plain,(
% 7.69/1.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.69/1.50    inference(definition_unfolding,[],[f60,f84])).
% 7.69/1.50  
% 7.69/1.50  fof(f86,plain,(
% 7.69/1.50    v1_funct_2(sK1,sK0,sK0)),
% 7.69/1.50    inference(cnf_transformation,[],[f54])).
% 7.69/1.50  
% 7.69/1.50  fof(f67,plain,(
% 7.69/1.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.69/1.50    inference(cnf_transformation,[],[f49])).
% 7.69/1.50  
% 7.69/1.50  fof(f98,plain,(
% 7.69/1.50    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.69/1.50    inference(equality_resolution,[],[f67])).
% 7.69/1.50  
% 7.69/1.50  fof(f94,plain,(
% 7.69/1.50    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 7.69/1.50    inference(cnf_transformation,[],[f54])).
% 7.69/1.50  
% 7.69/1.50  fof(f17,axiom,(
% 7.69/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 7.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.50  
% 7.69/1.50  fof(f45,plain,(
% 7.69/1.50    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 7.69/1.50    inference(ennf_transformation,[],[f17])).
% 7.69/1.50  
% 7.69/1.50  fof(f46,plain,(
% 7.69/1.50    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 7.69/1.50    inference(flattening,[],[f45])).
% 7.69/1.50  
% 7.69/1.50  fof(f83,plain,(
% 7.69/1.50    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.69/1.50    inference(cnf_transformation,[],[f46])).
% 7.69/1.50  
% 7.69/1.50  cnf(c_21,plain,
% 7.69/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.69/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.69/1.50      | k1_xboole_0 = X2 ),
% 7.69/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.69/1.50  
% 7.69/1.50  cnf(c_33,negated_conjecture,
% 7.69/1.50      ( v1_funct_2(sK2,sK0,sK0) ),
% 7.69/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.69/1.50  
% 7.69/1.50  cnf(c_912,plain,
% 7.69/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.69/1.50      | sK2 != X0
% 7.69/1.50      | sK0 != X1
% 7.69/1.50      | sK0 != X2
% 7.69/1.50      | k1_xboole_0 = X2 ),
% 7.69/1.50      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 7.69/1.50  
% 7.69/1.50  cnf(c_913,plain,
% 7.69/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.50      | k1_relset_1(sK0,sK0,sK2) = sK0
% 7.69/1.50      | k1_xboole_0 = sK0 ),
% 7.69/1.50      inference(unflattening,[status(thm)],[c_912]) ).
% 7.69/1.50  
% 7.69/1.50  cnf(c_31,negated_conjecture,
% 7.69/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.69/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.69/1.50  
% 7.69/1.50  cnf(c_915,plain,
% 7.69/1.50      ( k1_relset_1(sK0,sK0,sK2) = sK0 | k1_xboole_0 = sK0 ),
% 7.69/1.50      inference(global_propositional_subsumption,
% 7.69/1.50                [status(thm)],
% 7.69/1.50                [c_913,c_31]) ).
% 7.69/1.50  
% 7.69/1.50  cnf(c_1147,plain,
% 7.69/1.50      ( k1_relset_1(sK0,sK0,sK2) = sK0 | k1_xboole_0 = sK0 ),
% 7.69/1.50      inference(subtyping,[status(esa)],[c_915]) ).
% 7.69/1.50  
% 7.69/1.50  cnf(c_1167,negated_conjecture,
% 7.69/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.69/1.50      inference(subtyping,[status(esa)],[c_31]) ).
% 7.69/1.50  
% 7.69/1.50  cnf(c_1662,plain,
% 7.69/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.69/1.50      inference(predicate_to_equality,[status(thm)],[c_1167]) ).
% 7.69/1.50  
% 7.69/1.50  cnf(c_10,plain,
% 7.69/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.69/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1172,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.69/1.51      | k1_relset_1(X1_51,X2_51,X0_51) = k1_relat_1(X0_51) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_10]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1657,plain,
% 7.69/1.51      ( k1_relset_1(X0_51,X1_51,X2_51) = k1_relat_1(X2_51)
% 7.69/1.51      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1172]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2091,plain,
% 7.69/1.51      ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1662,c_1657]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2261,plain,
% 7.69/1.51      ( k1_relat_1(sK2) = sK0 | sK0 = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1147,c_2091]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_12,plain,
% 7.69/1.51      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.69/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.69/1.51      | X3 = X2 ),
% 7.69/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_30,negated_conjecture,
% 7.69/1.51      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 7.69/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_456,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | X3 = X0
% 7.69/1.51      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
% 7.69/1.51      | k6_partfun1(sK0) != X3
% 7.69/1.51      | sK0 != X2
% 7.69/1.51      | sK0 != X1 ),
% 7.69/1.51      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_457,plain,
% 7.69/1.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 7.69/1.51      inference(unflattening,[status(thm)],[c_456]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_26,plain,
% 7.69/1.51      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.69/1.51      inference(cnf_transformation,[],[f81]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_465,plain,
% 7.69/1.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 7.69/1.51      inference(forward_subsumption_resolution,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_457,c_26]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1162,plain,
% 7.69/1.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_465]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1667,plain,
% 7.69/1.51      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
% 7.69/1.51      | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1162]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_38,negated_conjecture,
% 7.69/1.51      ( v1_funct_1(sK1) ),
% 7.69/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_35,negated_conjecture,
% 7.69/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.69/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_34,negated_conjecture,
% 7.69/1.51      ( v1_funct_1(sK2) ),
% 7.69/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_24,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.69/1.51      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(X3) ),
% 7.69/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1171,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.69/1.51      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X5_51)))
% 7.69/1.51      | m1_subset_1(k1_partfun1(X4_51,X5_51,X1_51,X2_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 7.69/1.51      | ~ v1_funct_1(X0_51)
% 7.69/1.51      | ~ v1_funct_1(X3_51) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_24]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1775,plain,
% 7.69/1.51      ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | ~ v1_funct_1(sK1)
% 7.69/1.51      | ~ v1_funct_1(sK2) ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1171]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3099,plain,
% 7.69/1.51      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_1667,c_38,c_35,c_34,c_31,c_1162,c_1775]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1165,negated_conjecture,
% 7.69/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_35]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1664,plain,
% 7.69/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1165]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_27,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(X3)
% 7.69/1.51      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.69/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1168,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.69/1.51      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X5_51)))
% 7.69/1.51      | ~ v1_funct_1(X0_51)
% 7.69/1.51      | ~ v1_funct_1(X3_51)
% 7.69/1.51      | k1_partfun1(X4_51,X5_51,X1_51,X2_51,X3_51,X0_51) = k5_relat_1(X3_51,X0_51) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_27]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1661,plain,
% 7.69/1.51      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X4_51,X5_51) = k5_relat_1(X4_51,X5_51)
% 7.69/1.51      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 7.69/1.51      | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.69/1.51      | v1_funct_1(X5_51) != iProver_top
% 7.69/1.51      | v1_funct_1(X4_51) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1168]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2574,plain,
% 7.69/1.51      ( k1_partfun1(X0_51,X1_51,sK0,sK0,X2_51,sK2) = k5_relat_1(X2_51,sK2)
% 7.69/1.51      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.69/1.51      | v1_funct_1(X2_51) != iProver_top
% 7.69/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1662,c_1661]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_43,plain,
% 7.69/1.51      ( v1_funct_1(sK2) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2662,plain,
% 7.69/1.51      ( v1_funct_1(X2_51) != iProver_top
% 7.69/1.51      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.69/1.51      | k1_partfun1(X0_51,X1_51,sK0,sK0,X2_51,sK2) = k5_relat_1(X2_51,sK2) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_2574,c_43]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2663,plain,
% 7.69/1.51      ( k1_partfun1(X0_51,X1_51,sK0,sK0,X2_51,sK2) = k5_relat_1(X2_51,sK2)
% 7.69/1.51      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.69/1.51      | v1_funct_1(X2_51) != iProver_top ),
% 7.69/1.51      inference(renaming,[status(thm)],[c_2662]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2669,plain,
% 7.69/1.51      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
% 7.69/1.51      | v1_funct_1(sK1) != iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1664,c_2663]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_39,plain,
% 7.69/1.51      ( v1_funct_1(sK1) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2742,plain,
% 7.69/1.51      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_2669,c_39]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3101,plain,
% 7.69/1.51      ( k5_relat_1(sK1,sK2) = k6_partfun1(sK0) ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_3099,c_2742]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7,plain,
% 7.69/1.51      ( ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(X1)
% 7.69/1.51      | ~ v2_funct_1(X0)
% 7.69/1.51      | ~ v1_relat_1(X0)
% 7.69/1.51      | ~ v1_relat_1(X1)
% 7.69/1.51      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 7.69/1.51      | k2_funct_1(X0) = X1
% 7.69/1.51      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 7.69/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_14,plain,
% 7.69/1.51      ( ~ v3_funct_2(X0,X1,X2)
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | v2_funct_1(X0) ),
% 7.69/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_32,negated_conjecture,
% 7.69/1.51      ( v3_funct_2(sK2,sK0,sK0) ),
% 7.69/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_628,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | v2_funct_1(X0)
% 7.69/1.51      | sK2 != X0
% 7.69/1.51      | sK0 != X1
% 7.69/1.51      | sK0 != X2 ),
% 7.69/1.51      inference(resolution_lifted,[status(thm)],[c_14,c_32]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_629,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | ~ v1_funct_1(sK2)
% 7.69/1.51      | v2_funct_1(sK2) ),
% 7.69/1.51      inference(unflattening,[status(thm)],[c_628]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_631,plain,
% 7.69/1.51      ( v2_funct_1(sK2) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_629,c_34,c_31]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_696,plain,
% 7.69/1.51      ( ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(X1)
% 7.69/1.51      | ~ v1_relat_1(X0)
% 7.69/1.51      | ~ v1_relat_1(X1)
% 7.69/1.51      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 7.69/1.51      | k2_funct_1(X0) = X1
% 7.69/1.51      | k1_relat_1(X0) != k2_relat_1(X1)
% 7.69/1.51      | sK2 != X0 ),
% 7.69/1.51      inference(resolution_lifted,[status(thm)],[c_7,c_631]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_697,plain,
% 7.69/1.51      ( ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(sK2)
% 7.69/1.51      | ~ v1_relat_1(X0)
% 7.69/1.51      | ~ v1_relat_1(sK2)
% 7.69/1.51      | k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2))
% 7.69/1.51      | k2_funct_1(sK2) = X0
% 7.69/1.51      | k1_relat_1(sK2) != k2_relat_1(X0) ),
% 7.69/1.51      inference(unflattening,[status(thm)],[c_696]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_701,plain,
% 7.69/1.51      ( ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_relat_1(X0)
% 7.69/1.51      | ~ v1_relat_1(sK2)
% 7.69/1.51      | k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2))
% 7.69/1.51      | k2_funct_1(sK2) = X0
% 7.69/1.51      | k1_relat_1(sK2) != k2_relat_1(X0) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_697,c_34]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1157,plain,
% 7.69/1.51      ( ~ v1_funct_1(X0_51)
% 7.69/1.51      | ~ v1_relat_1(X0_51)
% 7.69/1.51      | ~ v1_relat_1(sK2)
% 7.69/1.51      | k5_relat_1(X0_51,sK2) != k6_partfun1(k2_relat_1(sK2))
% 7.69/1.51      | k2_funct_1(sK2) = X0_51
% 7.69/1.51      | k1_relat_1(sK2) != k2_relat_1(X0_51) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_701]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1670,plain,
% 7.69/1.51      ( k5_relat_1(X0_51,sK2) != k6_partfun1(k2_relat_1(sK2))
% 7.69/1.51      | k2_funct_1(sK2) = X0_51
% 7.69/1.51      | k1_relat_1(sK2) != k2_relat_1(X0_51)
% 7.69/1.51      | v1_funct_1(X0_51) != iProver_top
% 7.69/1.51      | v1_relat_1(X0_51) != iProver_top
% 7.69/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1157]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_46,plain,
% 7.69/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1241,plain,
% 7.69/1.51      ( k5_relat_1(X0_51,sK2) != k6_partfun1(k2_relat_1(sK2))
% 7.69/1.51      | k2_funct_1(sK2) = X0_51
% 7.69/1.51      | k1_relat_1(sK2) != k2_relat_1(X0_51)
% 7.69/1.51      | v1_funct_1(X0_51) != iProver_top
% 7.69/1.51      | v1_relat_1(X0_51) != iProver_top
% 7.69/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1157]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_8,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | v1_relat_1(X0) ),
% 7.69/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1173,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.69/1.51      | v1_relat_1(X0_51) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_8]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1763,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.69/1.51      | v1_relat_1(sK2) ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1173]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1841,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | v1_relat_1(sK2) ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1763]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1842,plain,
% 7.69/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 7.69/1.51      | v1_relat_1(sK2) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1841]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3614,plain,
% 7.69/1.51      ( v1_relat_1(X0_51) != iProver_top
% 7.69/1.51      | v1_funct_1(X0_51) != iProver_top
% 7.69/1.51      | k1_relat_1(sK2) != k2_relat_1(X0_51)
% 7.69/1.51      | k2_funct_1(sK2) = X0_51
% 7.69/1.51      | k5_relat_1(X0_51,sK2) != k6_partfun1(k2_relat_1(sK2)) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_1670,c_46,c_1241,c_1842]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3615,plain,
% 7.69/1.51      ( k5_relat_1(X0_51,sK2) != k6_partfun1(k2_relat_1(sK2))
% 7.69/1.51      | k2_funct_1(sK2) = X0_51
% 7.69/1.51      | k1_relat_1(sK2) != k2_relat_1(X0_51)
% 7.69/1.51      | v1_funct_1(X0_51) != iProver_top
% 7.69/1.51      | v1_relat_1(X0_51) != iProver_top ),
% 7.69/1.51      inference(renaming,[status(thm)],[c_3614]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_13,plain,
% 7.69/1.51      ( ~ v3_funct_2(X0,X1,X2)
% 7.69/1.51      | v2_funct_2(X0,X2)
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ v1_funct_1(X0) ),
% 7.69/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_9,plain,
% 7.69/1.51      ( v5_relat_1(X0,X1)
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.69/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_23,plain,
% 7.69/1.51      ( ~ v2_funct_2(X0,X1)
% 7.69/1.51      | ~ v5_relat_1(X0,X1)
% 7.69/1.51      | ~ v1_relat_1(X0)
% 7.69/1.51      | k2_relat_1(X0) = X1 ),
% 7.69/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_405,plain,
% 7.69/1.51      ( ~ v2_funct_2(X0,X1)
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.69/1.51      | ~ v1_relat_1(X0)
% 7.69/1.51      | k2_relat_1(X0) = X1 ),
% 7.69/1.51      inference(resolution,[status(thm)],[c_9,c_23]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_415,plain,
% 7.69/1.51      ( ~ v2_funct_2(X0,X1)
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.69/1.51      | k2_relat_1(X0) = X1 ),
% 7.69/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_405,c_8]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_488,plain,
% 7.69/1.51      ( ~ v3_funct_2(X0,X1,X2)
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | X3 != X0
% 7.69/1.51      | X5 != X2
% 7.69/1.51      | k2_relat_1(X3) = X5 ),
% 7.69/1.51      inference(resolution_lifted,[status(thm)],[c_13,c_415]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_489,plain,
% 7.69/1.51      ( ~ v3_funct_2(X0,X1,X2)
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | k2_relat_1(X0) = X2 ),
% 7.69/1.51      inference(unflattening,[status(thm)],[c_488]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_610,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | k2_relat_1(X0) = X2
% 7.69/1.51      | sK2 != X0
% 7.69/1.51      | sK0 != X1
% 7.69/1.51      | sK0 != X2 ),
% 7.69/1.51      inference(resolution_lifted,[status(thm)],[c_489,c_32]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_611,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 7.69/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | ~ v1_funct_1(sK2)
% 7.69/1.51      | k2_relat_1(sK2) = sK0 ),
% 7.69/1.51      inference(unflattening,[status(thm)],[c_610]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_615,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 7.69/1.51      | k2_relat_1(sK2) = sK0 ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_611,c_34,c_31]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1161,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
% 7.69/1.51      | k2_relat_1(sK2) = sK0 ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_615]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1668,plain,
% 7.69/1.51      ( k2_relat_1(sK2) = sK0
% 7.69/1.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1161]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1741,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | k2_relat_1(sK2) = sK0 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1161]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2021,plain,
% 7.69/1.51      ( k2_relat_1(sK2) = sK0 ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_1668,c_31,c_1741]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3620,plain,
% 7.69/1.51      ( k5_relat_1(X0_51,sK2) != k6_partfun1(sK0)
% 7.69/1.51      | k2_funct_1(sK2) = X0_51
% 7.69/1.51      | k2_relat_1(X0_51) != k1_relat_1(sK2)
% 7.69/1.51      | v1_funct_1(X0_51) != iProver_top
% 7.69/1.51      | v1_relat_1(X0_51) != iProver_top ),
% 7.69/1.51      inference(light_normalisation,[status(thm)],[c_3615,c_2021]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3625,plain,
% 7.69/1.51      ( k2_funct_1(sK2) = sK1
% 7.69/1.51      | k1_relat_1(sK2) != k2_relat_1(sK1)
% 7.69/1.51      | v1_funct_1(sK1) != iProver_top
% 7.69/1.51      | v1_relat_1(sK1) != iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_3101,c_3620]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_36,negated_conjecture,
% 7.69/1.51      ( v3_funct_2(sK1,sK0,sK0) ),
% 7.69/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_639,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | k2_relat_1(X0) = X2
% 7.69/1.51      | sK1 != X0
% 7.69/1.51      | sK0 != X1
% 7.69/1.51      | sK0 != X2 ),
% 7.69/1.51      inference(resolution_lifted,[status(thm)],[c_489,c_36]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_640,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 7.69/1.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | ~ v1_funct_1(sK1)
% 7.69/1.51      | k2_relat_1(sK1) = sK0 ),
% 7.69/1.51      inference(unflattening,[status(thm)],[c_639]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_644,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 7.69/1.51      | k2_relat_1(sK1) = sK0 ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_640,c_38,c_35]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1160,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
% 7.69/1.51      | k2_relat_1(sK1) = sK0 ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_644]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1669,plain,
% 7.69/1.51      ( k2_relat_1(sK1) = sK0
% 7.69/1.51      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1160]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1733,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | k2_relat_1(sK1) = sK0 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1160]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2050,plain,
% 7.69/1.51      ( k2_relat_1(sK1) = sK0 ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_1669,c_35,c_1733]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3626,plain,
% 7.69/1.51      ( k2_funct_1(sK2) = sK1
% 7.69/1.51      | k1_relat_1(sK2) != sK0
% 7.69/1.51      | v1_funct_1(sK1) != iProver_top
% 7.69/1.51      | v1_relat_1(sK1) != iProver_top ),
% 7.69/1.51      inference(light_normalisation,[status(thm)],[c_3625,c_2050]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1751,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.69/1.51      | v1_relat_1(sK1) ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1173]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1810,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | v1_relat_1(sK1) ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1751]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3627,plain,
% 7.69/1.51      ( ~ v1_funct_1(sK1)
% 7.69/1.51      | ~ v1_relat_1(sK1)
% 7.69/1.51      | k2_funct_1(sK2) = sK1
% 7.69/1.51      | k1_relat_1(sK2) != sK0 ),
% 7.69/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_3626]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3736,plain,
% 7.69/1.51      ( k2_funct_1(sK2) = sK1 | k1_relat_1(sK2) != sK0 ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_3626,c_38,c_35,c_1810,c_3627]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3738,plain,
% 7.69/1.51      ( k2_funct_1(sK2) = sK1 | sK0 = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_2261,c_3736]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1180,plain,( X0_51 = X0_51 ),theory(equality) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1211,plain,
% 7.69/1.51      ( k1_xboole_0 = k1_xboole_0 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1180]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2,plain,
% 7.69/1.51      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.69/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1176,plain,
% 7.69/1.51      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_2]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3,plain,
% 7.69/1.51      ( ~ v1_relat_1(X0)
% 7.69/1.51      | k2_relat_1(X0) != k1_xboole_0
% 7.69/1.51      | k1_xboole_0 = X0 ),
% 7.69/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1175,plain,
% 7.69/1.51      ( ~ v1_relat_1(X0_51)
% 7.69/1.51      | k2_relat_1(X0_51) != k1_xboole_0
% 7.69/1.51      | k1_xboole_0 = X0_51 ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_3]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1654,plain,
% 7.69/1.51      ( k2_relat_1(X0_51) != k1_xboole_0
% 7.69/1.51      | k1_xboole_0 = X0_51
% 7.69/1.51      | v1_relat_1(X0_51) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1175]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2134,plain,
% 7.69/1.51      ( sK2 = k1_xboole_0
% 7.69/1.51      | sK0 != k1_xboole_0
% 7.69/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_2021,c_1654]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1183,plain,
% 7.69/1.51      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 7.69/1.51      theory(equality) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2001,plain,
% 7.69/1.51      ( X0_51 != X1_51 | X0_51 = sK0 | sK0 != X1_51 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1183]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2300,plain,
% 7.69/1.51      ( k1_relat_1(sK2) != X0_51 | k1_relat_1(sK2) = sK0 | sK0 != X0_51 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_2001]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2301,plain,
% 7.69/1.51      ( k1_relat_1(sK2) = sK0
% 7.69/1.51      | k1_relat_1(sK2) != k1_xboole_0
% 7.69/1.51      | sK0 != k1_xboole_0 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_2300]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1187,plain,
% 7.69/1.51      ( X0_51 != X1_51 | k1_relat_1(X0_51) = k1_relat_1(X1_51) ),
% 7.69/1.51      theory(equality) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2704,plain,
% 7.69/1.51      ( k1_relat_1(sK2) = k1_relat_1(X0_51) | sK2 != X0_51 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1187]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2705,plain,
% 7.69/1.51      ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_2704]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2303,plain,
% 7.69/1.51      ( X0_51 != X1_51
% 7.69/1.51      | k1_relat_1(sK2) != X1_51
% 7.69/1.51      | k1_relat_1(sK2) = X0_51 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1183]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2801,plain,
% 7.69/1.51      ( X0_51 != k1_relat_1(X1_51)
% 7.69/1.51      | k1_relat_1(sK2) = X0_51
% 7.69/1.51      | k1_relat_1(sK2) != k1_relat_1(X1_51) ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_2303]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2802,plain,
% 7.69/1.51      ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
% 7.69/1.51      | k1_relat_1(sK2) = k1_xboole_0
% 7.69/1.51      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_2801]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_4280,plain,
% 7.69/1.51      ( X0_51 != X1_51
% 7.69/1.51      | X0_51 = k1_relat_1(X2_51)
% 7.69/1.51      | k1_relat_1(X2_51) != X1_51 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1183]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_4281,plain,
% 7.69/1.51      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 7.69/1.51      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 7.69/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_4280]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_8028,plain,
% 7.69/1.51      ( k2_funct_1(sK2) = sK1 ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_3738,c_46,c_1211,c_1176,c_1842,c_2134,c_2261,c_2301,
% 7.69/1.51                 c_2705,c_2802,c_3736,c_4281]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6,plain,
% 7.69/1.51      ( ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v2_funct_1(X0)
% 7.69/1.51      | ~ v1_relat_1(X0)
% 7.69/1.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 7.69/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_726,plain,
% 7.69/1.51      ( ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_relat_1(X0)
% 7.69/1.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 7.69/1.51      | sK2 != X0 ),
% 7.69/1.51      inference(resolution_lifted,[status(thm)],[c_6,c_631]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_727,plain,
% 7.69/1.51      ( ~ v1_funct_1(sK2)
% 7.69/1.51      | ~ v1_relat_1(sK2)
% 7.69/1.51      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 7.69/1.51      inference(unflattening,[status(thm)],[c_726]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_729,plain,
% 7.69/1.51      ( ~ v1_relat_1(sK2)
% 7.69/1.51      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_727,c_34]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1156,plain,
% 7.69/1.51      ( ~ v1_relat_1(sK2)
% 7.69/1.51      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_729]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1671,plain,
% 7.69/1.51      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 7.69/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1156]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2485,plain,
% 7.69/1.51      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_1671,c_31,c_1156,c_1841]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_8032,plain,
% 7.69/1.51      ( k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK1) ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_8028,c_2485]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_657,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | v2_funct_1(X0)
% 7.69/1.51      | sK1 != X0
% 7.69/1.51      | sK0 != X1
% 7.69/1.51      | sK0 != X2 ),
% 7.69/1.51      inference(resolution_lifted,[status(thm)],[c_14,c_36]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_658,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | ~ v1_funct_1(sK1)
% 7.69/1.51      | v2_funct_1(sK1) ),
% 7.69/1.51      inference(unflattening,[status(thm)],[c_657]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_660,plain,
% 7.69/1.51      ( v2_funct_1(sK1) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_658,c_38,c_35]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_754,plain,
% 7.69/1.51      ( ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(X1)
% 7.69/1.51      | ~ v1_relat_1(X0)
% 7.69/1.51      | ~ v1_relat_1(X1)
% 7.69/1.51      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 7.69/1.51      | k2_funct_1(X0) = X1
% 7.69/1.51      | k1_relat_1(X0) != k2_relat_1(X1)
% 7.69/1.51      | sK1 != X0 ),
% 7.69/1.51      inference(resolution_lifted,[status(thm)],[c_7,c_660]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_755,plain,
% 7.69/1.51      ( ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_funct_1(sK1)
% 7.69/1.51      | ~ v1_relat_1(X0)
% 7.69/1.51      | ~ v1_relat_1(sK1)
% 7.69/1.51      | k5_relat_1(X0,sK1) != k6_partfun1(k2_relat_1(sK1))
% 7.69/1.51      | k2_funct_1(sK1) = X0
% 7.69/1.51      | k1_relat_1(sK1) != k2_relat_1(X0) ),
% 7.69/1.51      inference(unflattening,[status(thm)],[c_754]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_759,plain,
% 7.69/1.51      ( ~ v1_funct_1(X0)
% 7.69/1.51      | ~ v1_relat_1(X0)
% 7.69/1.51      | ~ v1_relat_1(sK1)
% 7.69/1.51      | k5_relat_1(X0,sK1) != k6_partfun1(k2_relat_1(sK1))
% 7.69/1.51      | k2_funct_1(sK1) = X0
% 7.69/1.51      | k1_relat_1(sK1) != k2_relat_1(X0) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_755,c_38]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1154,plain,
% 7.69/1.51      ( ~ v1_funct_1(X0_51)
% 7.69/1.51      | ~ v1_relat_1(X0_51)
% 7.69/1.51      | ~ v1_relat_1(sK1)
% 7.69/1.51      | k5_relat_1(X0_51,sK1) != k6_partfun1(k2_relat_1(sK1))
% 7.69/1.51      | k2_funct_1(sK1) = X0_51
% 7.69/1.51      | k1_relat_1(sK1) != k2_relat_1(X0_51) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_759]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1673,plain,
% 7.69/1.51      ( k5_relat_1(X0_51,sK1) != k6_partfun1(k2_relat_1(sK1))
% 7.69/1.51      | k2_funct_1(sK1) = X0_51
% 7.69/1.51      | k1_relat_1(sK1) != k2_relat_1(X0_51)
% 7.69/1.51      | v1_funct_1(X0_51) != iProver_top
% 7.69/1.51      | v1_relat_1(X0_51) != iProver_top
% 7.69/1.51      | v1_relat_1(sK1) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1154]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_42,plain,
% 7.69/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1246,plain,
% 7.69/1.51      ( k5_relat_1(X0_51,sK1) != k6_partfun1(k2_relat_1(sK1))
% 7.69/1.51      | k2_funct_1(sK1) = X0_51
% 7.69/1.51      | k1_relat_1(sK1) != k2_relat_1(X0_51)
% 7.69/1.51      | v1_funct_1(X0_51) != iProver_top
% 7.69/1.51      | v1_relat_1(X0_51) != iProver_top
% 7.69/1.51      | v1_relat_1(sK1) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1154]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1811,plain,
% 7.69/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 7.69/1.51      | v1_relat_1(sK1) = iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1810]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3866,plain,
% 7.69/1.51      ( v1_relat_1(X0_51) != iProver_top
% 7.69/1.51      | v1_funct_1(X0_51) != iProver_top
% 7.69/1.51      | k1_relat_1(sK1) != k2_relat_1(X0_51)
% 7.69/1.51      | k2_funct_1(sK1) = X0_51
% 7.69/1.51      | k5_relat_1(X0_51,sK1) != k6_partfun1(k2_relat_1(sK1)) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_1673,c_42,c_1246,c_1811]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3867,plain,
% 7.69/1.51      ( k5_relat_1(X0_51,sK1) != k6_partfun1(k2_relat_1(sK1))
% 7.69/1.51      | k2_funct_1(sK1) = X0_51
% 7.69/1.51      | k1_relat_1(sK1) != k2_relat_1(X0_51)
% 7.69/1.51      | v1_funct_1(X0_51) != iProver_top
% 7.69/1.51      | v1_relat_1(X0_51) != iProver_top ),
% 7.69/1.51      inference(renaming,[status(thm)],[c_3866]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3872,plain,
% 7.69/1.51      ( k5_relat_1(X0_51,sK1) != k6_partfun1(sK0)
% 7.69/1.51      | k2_funct_1(sK1) = X0_51
% 7.69/1.51      | k2_relat_1(X0_51) != k1_relat_1(sK1)
% 7.69/1.51      | v1_funct_1(X0_51) != iProver_top
% 7.69/1.51      | v1_relat_1(X0_51) != iProver_top ),
% 7.69/1.51      inference(light_normalisation,[status(thm)],[c_3867,c_2050]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_14473,plain,
% 7.69/1.51      ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
% 7.69/1.51      | k2_funct_1(sK1) = sK2
% 7.69/1.51      | k1_relat_1(sK1) != k2_relat_1(sK2)
% 7.69/1.51      | v1_funct_1(sK2) != iProver_top
% 7.69/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_8032,c_3872]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_14474,plain,
% 7.69/1.51      ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
% 7.69/1.51      | k2_funct_1(sK1) = sK2
% 7.69/1.51      | k1_relat_1(sK1) != sK0
% 7.69/1.51      | v1_funct_1(sK2) != iProver_top
% 7.69/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.69/1.51      inference(light_normalisation,[status(thm)],[c_14473,c_2021]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2135,plain,
% 7.69/1.51      ( sK1 = k1_xboole_0
% 7.69/1.51      | sK0 != k1_xboole_0
% 7.69/1.51      | v1_relat_1(sK1) != iProver_top ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_2050,c_1654]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2244,plain,
% 7.69/1.51      ( k1_relat_1(sK1) != X0_51 | k1_relat_1(sK1) = sK0 | sK0 != X0_51 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_2001]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2246,plain,
% 7.69/1.51      ( k1_relat_1(sK1) = sK0
% 7.69/1.51      | k1_relat_1(sK1) != k1_xboole_0
% 7.69/1.51      | sK0 != k1_xboole_0 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_2244]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2293,plain,
% 7.69/1.51      ( k1_relat_1(sK1) = k1_relat_1(X0_51) | sK1 != X0_51 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1187]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2294,plain,
% 7.69/1.51      ( k1_relat_1(sK1) = k1_relat_1(k1_xboole_0) | sK1 != k1_xboole_0 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_2293]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_37,negated_conjecture,
% 7.69/1.51      ( v1_funct_2(sK1,sK0,sK0) ),
% 7.69/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_923,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | k1_relset_1(X1,X2,X0) = X1
% 7.69/1.51      | sK1 != X0
% 7.69/1.51      | sK0 != X1
% 7.69/1.51      | sK0 != X2
% 7.69/1.51      | k1_xboole_0 = X2 ),
% 7.69/1.51      inference(resolution_lifted,[status(thm)],[c_21,c_37]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_924,plain,
% 7.69/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | k1_relset_1(sK0,sK0,sK1) = sK0
% 7.69/1.51      | k1_xboole_0 = sK0 ),
% 7.69/1.51      inference(unflattening,[status(thm)],[c_923]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_926,plain,
% 7.69/1.51      ( k1_relset_1(sK0,sK0,sK1) = sK0 | k1_xboole_0 = sK0 ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_924,c_35]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1146,plain,
% 7.69/1.51      ( k1_relset_1(sK0,sK0,sK1) = sK0 | k1_xboole_0 = sK0 ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_926]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2092,plain,
% 7.69/1.51      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1664,c_1657]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2295,plain,
% 7.69/1.51      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1146,c_2092]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2058,plain,
% 7.69/1.51      ( X0_51 != X1_51
% 7.69/1.51      | k1_relat_1(sK1) != X1_51
% 7.69/1.51      | k1_relat_1(sK1) = X0_51 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1183]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2779,plain,
% 7.69/1.51      ( X0_51 != k1_relat_1(X1_51)
% 7.69/1.51      | k1_relat_1(sK1) = X0_51
% 7.69/1.51      | k1_relat_1(sK1) != k1_relat_1(X1_51) ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_2058]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2780,plain,
% 7.69/1.51      ( k1_relat_1(sK1) != k1_relat_1(k1_xboole_0)
% 7.69/1.51      | k1_relat_1(sK1) = k1_xboole_0
% 7.69/1.51      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_2779]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1191,plain,
% 7.69/1.51      ( X0_51 != X1_51 | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
% 7.69/1.51      theory(equality) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_4338,plain,
% 7.69/1.51      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
% 7.69/1.51      | k1_relat_1(sK2) != sK0 ),
% 7.69/1.51      inference(instantiation,[status(thm)],[c_1191]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_14986,plain,
% 7.69/1.51      ( k2_funct_1(sK1) = sK2 | k1_relat_1(sK1) != sK0 ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_14474,c_42,c_43,c_46,c_1211,c_1176,c_1811,c_1842,
% 7.69/1.51                 c_2134,c_2135,c_2246,c_2261,c_2294,c_2295,c_2301,c_2705,
% 7.69/1.51                 c_2780,c_2802,c_4281,c_4338]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_14988,plain,
% 7.69/1.51      ( k2_funct_1(sK1) = sK2 ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_14986,c_42,c_43,c_46,c_1211,c_1176,c_1811,c_1842,
% 7.69/1.51                 c_2134,c_2135,c_2246,c_2261,c_2294,c_2295,c_2301,c_2705,
% 7.69/1.51                 c_2780,c_2802,c_4281,c_4338,c_14474]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_11,plain,
% 7.69/1.51      ( r2_relset_1(X0,X1,X2,X2)
% 7.69/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.69/1.51      inference(cnf_transformation,[],[f98]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_29,negated_conjecture,
% 7.69/1.51      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 7.69/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_446,plain,
% 7.69/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.51      | k2_funct_2(sK0,sK1) != X0
% 7.69/1.51      | sK2 != X0
% 7.69/1.51      | sK0 != X2
% 7.69/1.51      | sK0 != X1 ),
% 7.69/1.51      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_447,plain,
% 7.69/1.51      ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | sK2 != k2_funct_2(sK0,sK1) ),
% 7.69/1.51      inference(unflattening,[status(thm)],[c_446]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1163,plain,
% 7.69/1.51      ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | sK2 != k2_funct_2(sK0,sK1) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_447]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1666,plain,
% 7.69/1.51      ( sK2 != k2_funct_2(sK0,sK1)
% 7.69/1.51      | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.69/1.51      inference(predicate_to_equality,[status(thm)],[c_1163]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_28,plain,
% 7.69/1.51      ( ~ v1_funct_2(X0,X1,X1)
% 7.69/1.51      | ~ v3_funct_2(X0,X1,X1)
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 7.69/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_676,plain,
% 7.69/1.51      ( ~ v1_funct_2(X0,X1,X1)
% 7.69/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.69/1.51      | ~ v1_funct_1(X0)
% 7.69/1.51      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 7.69/1.51      | sK1 != X0
% 7.69/1.51      | sK0 != X1 ),
% 7.69/1.51      inference(resolution_lifted,[status(thm)],[c_28,c_36]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_677,plain,
% 7.69/1.51      ( ~ v1_funct_2(sK1,sK0,sK0)
% 7.69/1.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.69/1.51      | ~ v1_funct_1(sK1)
% 7.69/1.51      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 7.69/1.51      inference(unflattening,[status(thm)],[c_676]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_679,plain,
% 7.69/1.51      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 7.69/1.51      inference(global_propositional_subsumption,
% 7.69/1.51                [status(thm)],
% 7.69/1.51                [c_677,c_38,c_37,c_35]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1158,plain,
% 7.69/1.51      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 7.69/1.51      inference(subtyping,[status(esa)],[c_679]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1680,plain,
% 7.69/1.51      ( k2_funct_1(sK1) != sK2
% 7.69/1.51      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.69/1.51      inference(light_normalisation,[status(thm)],[c_1666,c_1158]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_14994,plain,
% 7.69/1.51      ( sK2 != sK2
% 7.69/1.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_14988,c_1680]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_14996,plain,
% 7.69/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.69/1.51      inference(equality_resolution_simp,[status(thm)],[c_14994]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(contradiction,plain,
% 7.69/1.51      ( $false ),
% 7.69/1.51      inference(minisat,[status(thm)],[c_14996,c_46]) ).
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.69/1.51  
% 7.69/1.51  ------                               Statistics
% 7.69/1.51  
% 7.69/1.51  ------ General
% 7.69/1.51  
% 7.69/1.51  abstr_ref_over_cycles:                  0
% 7.69/1.51  abstr_ref_under_cycles:                 0
% 7.69/1.51  gc_basic_clause_elim:                   0
% 7.69/1.51  forced_gc_time:                         0
% 7.69/1.51  parsing_time:                           0.011
% 7.69/1.51  unif_index_cands_time:                  0.
% 7.69/1.51  unif_index_add_time:                    0.
% 7.69/1.51  orderings_time:                         0.
% 7.69/1.51  out_proof_time:                         0.015
% 7.69/1.51  total_time:                             0.609
% 7.69/1.51  num_of_symbols:                         57
% 7.69/1.51  num_of_terms:                           15485
% 7.69/1.51  
% 7.69/1.51  ------ Preprocessing
% 7.69/1.51  
% 7.69/1.51  num_of_splits:                          0
% 7.69/1.51  num_of_split_atoms:                     0
% 7.69/1.51  num_of_reused_defs:                     0
% 7.69/1.51  num_eq_ax_congr_red:                    7
% 7.69/1.51  num_of_sem_filtered_clauses:            1
% 7.69/1.51  num_of_subtypes:                        3
% 7.69/1.51  monotx_restored_types:                  1
% 7.69/1.51  sat_num_of_epr_types:                   0
% 7.69/1.51  sat_num_of_non_cyclic_types:            0
% 7.69/1.51  sat_guarded_non_collapsed_types:        1
% 7.69/1.51  num_pure_diseq_elim:                    0
% 7.69/1.51  simp_replaced_by:                       0
% 7.69/1.51  res_preprocessed:                       175
% 7.69/1.51  prep_upred:                             0
% 7.69/1.51  prep_unflattend:                        73
% 7.69/1.51  smt_new_axioms:                         0
% 7.69/1.51  pred_elim_cands:                        3
% 7.69/1.51  pred_elim:                              6
% 7.69/1.51  pred_elim_cl:                           4
% 7.69/1.51  pred_elim_cycles:                       9
% 7.69/1.51  merged_defs:                            0
% 7.69/1.51  merged_defs_ncl:                        0
% 7.69/1.51  bin_hyper_res:                          0
% 7.69/1.51  prep_cycles:                            4
% 7.69/1.51  pred_elim_time:                         0.012
% 7.69/1.51  splitting_time:                         0.
% 7.69/1.51  sem_filter_time:                        0.
% 7.69/1.51  monotx_time:                            0.
% 7.69/1.51  subtype_inf_time:                       0.001
% 7.69/1.51  
% 7.69/1.51  ------ Problem properties
% 7.69/1.51  
% 7.69/1.51  clauses:                                34
% 7.69/1.51  conjectures:                            4
% 7.69/1.51  epr:                                    2
% 7.69/1.51  horn:                                   30
% 7.69/1.51  ground:                                 21
% 7.69/1.51  unary:                                  10
% 7.69/1.51  binary:                                 13
% 7.69/1.51  lits:                                   83
% 7.69/1.51  lits_eq:                                40
% 7.69/1.51  fd_pure:                                0
% 7.69/1.51  fd_pseudo:                              0
% 7.69/1.51  fd_cond:                                4
% 7.69/1.51  fd_pseudo_cond:                         0
% 7.69/1.51  ac_symbols:                             0
% 7.69/1.51  
% 7.69/1.51  ------ Propositional Solver
% 7.69/1.51  
% 7.69/1.51  prop_solver_calls:                      31
% 7.69/1.51  prop_fast_solver_calls:                 2066
% 7.69/1.51  smt_solver_calls:                       0
% 7.69/1.51  smt_fast_solver_calls:                  0
% 7.69/1.51  prop_num_of_clauses:                    7306
% 7.69/1.51  prop_preprocess_simplified:             11633
% 7.69/1.51  prop_fo_subsumed:                       313
% 7.69/1.51  prop_solver_time:                       0.
% 7.69/1.51  smt_solver_time:                        0.
% 7.69/1.51  smt_fast_solver_time:                   0.
% 7.69/1.51  prop_fast_solver_time:                  0.
% 7.69/1.51  prop_unsat_core_time:                   0.
% 7.69/1.51  
% 7.69/1.51  ------ QBF
% 7.69/1.51  
% 7.69/1.51  qbf_q_res:                              0
% 7.69/1.51  qbf_num_tautologies:                    0
% 7.69/1.51  qbf_prep_cycles:                        0
% 7.69/1.51  
% 7.69/1.51  ------ BMC1
% 7.69/1.51  
% 7.69/1.51  bmc1_current_bound:                     -1
% 7.69/1.51  bmc1_last_solved_bound:                 -1
% 7.69/1.51  bmc1_unsat_core_size:                   -1
% 7.69/1.51  bmc1_unsat_core_parents_size:           -1
% 7.69/1.51  bmc1_merge_next_fun:                    0
% 7.69/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.69/1.51  
% 7.69/1.51  ------ Instantiation
% 7.69/1.51  
% 7.69/1.51  inst_num_of_clauses:                    2201
% 7.69/1.51  inst_num_in_passive:                    777
% 7.69/1.51  inst_num_in_active:                     865
% 7.69/1.51  inst_num_in_unprocessed:                559
% 7.69/1.51  inst_num_of_loops:                      1360
% 7.69/1.51  inst_num_of_learning_restarts:          0
% 7.69/1.51  inst_num_moves_active_passive:          490
% 7.69/1.51  inst_lit_activity:                      0
% 7.69/1.51  inst_lit_activity_moves:                0
% 7.69/1.51  inst_num_tautologies:                   0
% 7.69/1.51  inst_num_prop_implied:                  0
% 7.69/1.51  inst_num_existing_simplified:           0
% 7.69/1.51  inst_num_eq_res_simplified:             0
% 7.69/1.51  inst_num_child_elim:                    0
% 7.69/1.51  inst_num_of_dismatching_blockings:      1022
% 7.69/1.51  inst_num_of_non_proper_insts:           2229
% 7.69/1.51  inst_num_of_duplicates:                 0
% 7.69/1.51  inst_inst_num_from_inst_to_res:         0
% 7.69/1.51  inst_dismatching_checking_time:         0.
% 7.69/1.51  
% 7.69/1.51  ------ Resolution
% 7.69/1.51  
% 7.69/1.51  res_num_of_clauses:                     0
% 7.69/1.51  res_num_in_passive:                     0
% 7.69/1.51  res_num_in_active:                      0
% 7.69/1.51  res_num_of_loops:                       179
% 7.69/1.51  res_forward_subset_subsumed:            147
% 7.69/1.51  res_backward_subset_subsumed:           8
% 7.69/1.51  res_forward_subsumed:                   0
% 7.69/1.51  res_backward_subsumed:                  0
% 7.69/1.51  res_forward_subsumption_resolution:     3
% 7.69/1.51  res_backward_subsumption_resolution:    0
% 7.69/1.51  res_clause_to_clause_subsumption:       1483
% 7.69/1.51  res_orphan_elimination:                 0
% 7.69/1.51  res_tautology_del:                      247
% 7.69/1.51  res_num_eq_res_simplified:              1
% 7.69/1.51  res_num_sel_changes:                    0
% 7.69/1.51  res_moves_from_active_to_pass:          0
% 7.69/1.51  
% 7.69/1.51  ------ Superposition
% 7.69/1.51  
% 7.69/1.51  sup_time_total:                         0.
% 7.69/1.51  sup_time_generating:                    0.
% 7.69/1.51  sup_time_sim_full:                      0.
% 7.69/1.51  sup_time_sim_immed:                     0.
% 7.69/1.51  
% 7.69/1.51  sup_num_of_clauses:                     610
% 7.69/1.51  sup_num_in_active:                      222
% 7.69/1.51  sup_num_in_passive:                     388
% 7.69/1.51  sup_num_of_loops:                       271
% 7.69/1.51  sup_fw_superposition:                   327
% 7.69/1.51  sup_bw_superposition:                   375
% 7.69/1.51  sup_immediate_simplified:               168
% 7.69/1.51  sup_given_eliminated:                   0
% 7.69/1.51  comparisons_done:                       0
% 7.69/1.51  comparisons_avoided:                    54
% 7.69/1.51  
% 7.69/1.51  ------ Simplifications
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  sim_fw_subset_subsumed:                 16
% 7.69/1.51  sim_bw_subset_subsumed:                 42
% 7.69/1.51  sim_fw_subsumed:                        10
% 7.69/1.51  sim_bw_subsumed:                        10
% 7.69/1.51  sim_fw_subsumption_res:                 0
% 7.69/1.51  sim_bw_subsumption_res:                 0
% 7.69/1.51  sim_tautology_del:                      0
% 7.69/1.51  sim_eq_tautology_del:                   33
% 7.69/1.51  sim_eq_res_simp:                        1
% 7.69/1.51  sim_fw_demodulated:                     11
% 7.69/1.51  sim_bw_demodulated:                     29
% 7.69/1.51  sim_light_normalised:                   171
% 7.69/1.51  sim_joinable_taut:                      0
% 7.69/1.51  sim_joinable_simp:                      0
% 7.69/1.51  sim_ac_normalised:                      0
% 7.69/1.51  sim_smt_subsumption:                    0
% 7.69/1.51  
%------------------------------------------------------------------------------
