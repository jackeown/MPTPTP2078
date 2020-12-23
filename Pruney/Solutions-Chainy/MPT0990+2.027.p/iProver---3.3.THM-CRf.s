%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:02 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  238 (2279 expanded)
%              Number of clauses        :  151 ( 623 expanded)
%              Number of leaves         :   21 ( 588 expanded)
%              Depth                    :   25
%              Number of atoms          :  847 (19187 expanded)
%              Number of equality atoms :  433 (6954 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f51,f50])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f18,axiom,(
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

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f96,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f62,f74])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

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

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f70,f74])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f58,f74])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1305,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1318,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2429,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_1318])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1303,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1324,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1328,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4213,plain,
    ( k5_relat_1(sK3,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK3,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2429,c_1328])).

cnf(c_5503,plain,
    ( k5_relat_1(k5_relat_1(sK3,k2_funct_1(X0)),X1) = k5_relat_1(sK3,k5_relat_1(k2_funct_1(X0),X1))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_4213])).

cnf(c_17474,plain,
    ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0)) = k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1303,c_5503])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_447,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_448,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_536,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_448])).

cnf(c_1297,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_1807,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1297])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_41,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_44,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2269,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1807,c_40,c_41,c_42,c_43,c_44,c_45])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1307,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3496,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2269,c_1307])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_120,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_124,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_733,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1423,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_1424,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1423])).

cnf(c_8,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3514,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3515,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3514])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_435,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_443,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_435,c_17])).

cnf(c_1298,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1425,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2218,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1298,c_39,c_37,c_36,c_34,c_443,c_1425])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f78])).

cnf(c_1311,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5232,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1311])).

cnf(c_5239,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5232,c_40,c_41,c_42])).

cnf(c_5240,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5239])).

cnf(c_5243,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2218,c_5240])).

cnf(c_5929,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3496,c_43,c_44,c_45,c_30,c_120,c_124,c_1424,c_3515,c_5243])).

cnf(c_5296,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5243,c_43,c_44,c_45,c_30,c_120,c_124,c_1424,c_3515])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1320,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5301,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5296,c_1320])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1317,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2435,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1305,c_1317])).

cnf(c_2438,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2435,c_2269])).

cnf(c_5303,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5301,c_2438])).

cnf(c_16528,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5303,c_43,c_2429])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1327,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2482,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0))),k2_funct_1(X0)) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_1327])).

cnf(c_5578,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) = k2_funct_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1303,c_2482])).

cnf(c_5673,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5578,c_2429])).

cnf(c_16530,plain,
    ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k2_funct_1(sK3) ),
    inference(demodulation,[status(thm)],[c_16528,c_5673])).

cnf(c_1302,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2430,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1302,c_1318])).

cnf(c_4214,plain,
    ( k5_relat_1(sK2,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK2,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2430,c_1328])).

cnf(c_5893,plain,
    ( k5_relat_1(k5_relat_1(sK2,sK3),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2429,c_4214])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1313,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4536,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_1313])).

cnf(c_4583,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4536,c_43])).

cnf(c_4584,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4583])).

cnf(c_4591,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1302,c_4584])).

cnf(c_4592,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4591,c_2218])).

cnf(c_5081,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4592,c_40])).

cnf(c_5895,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5893,c_5081])).

cnf(c_9648,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(X0))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_5895])).

cnf(c_9847,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1303,c_9648])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1329,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2436,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1302,c_1317])).

cnf(c_2437,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2436,c_33])).

cnf(c_5,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1326,plain,
    ( k5_relat_1(X0,k6_partfun1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3504,plain,
    ( k5_relat_1(sK2,k6_partfun1(X0)) = sK2
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_1326])).

cnf(c_3913,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | k5_relat_1(sK2,k6_partfun1(X0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3504,c_2430])).

cnf(c_3914,plain,
    ( k5_relat_1(sK2,k6_partfun1(X0)) = sK2
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3913])).

cnf(c_3919,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_1329,c_3914])).

cnf(c_9852,plain,
    ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = sK2
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9847,c_3919,c_5929])).

cnf(c_10125,plain,
    ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9852,c_2429])).

cnf(c_16531,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_16530,c_10125])).

cnf(c_17481,plain,
    ( k5_relat_1(sK3,k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17474,c_5929,c_16531])).

cnf(c_17844,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(sK3,k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17481,c_2429])).

cnf(c_17845,plain,
    ( k5_relat_1(sK3,k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_17844])).

cnf(c_17852,plain,
    ( k5_relat_1(sK3,k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2429,c_17845])).

cnf(c_3502,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1329,c_1326])).

cnf(c_5643,plain,
    ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
    inference(superposition,[status(thm)],[c_2429,c_3502])).

cnf(c_5646,plain,
    ( k5_relat_1(sK3,k6_partfun1(sK0)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_5643,c_2438])).

cnf(c_1300,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_4211,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_1328])).

cnf(c_11388,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_4211])).

cnf(c_11655,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11388,c_2430])).

cnf(c_11656,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11655])).

cnf(c_11664,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2430,c_11656])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1308,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4167,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1308])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1384,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1482,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_1640,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_4228,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4167,c_39,c_38,c_37,c_33,c_31,c_29,c_1640])).

cnf(c_11668,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11664,c_4228])).

cnf(c_11691,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k2_funct_1(X0))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_11668])).

cnf(c_12612,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k2_funct_1(sK2))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_11691])).

cnf(c_3495,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1307])).

cnf(c_1385,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1508,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_1653,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_3661,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3495,c_39,c_38,c_37,c_33,c_31,c_29,c_1653])).

cnf(c_5579,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_2482])).

cnf(c_1306,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3608,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1306,c_1320])).

cnf(c_3609,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3608,c_2437])).

cnf(c_3729,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3609,c_40,c_2430])).

cnf(c_5582,plain,
    ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5579,c_3729])).

cnf(c_5800,plain,
    ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5582,c_2430])).

cnf(c_11693,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2429,c_11668])).

cnf(c_11700,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(light_normalisation,[status(thm)],[c_11693,c_5081])).

cnf(c_12617,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12612,c_3661,c_5800,c_11700])).

cnf(c_12657,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12617,c_2430])).

cnf(c_17860,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_17852,c_5081,c_5646,c_12657])).

cnf(c_28,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f93])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17860,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:19:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.73/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.49  
% 7.73/1.49  ------  iProver source info
% 7.73/1.49  
% 7.73/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.49  git: non_committed_changes: false
% 7.73/1.49  git: last_make_outside_of_git: false
% 7.73/1.49  
% 7.73/1.49  ------ 
% 7.73/1.49  
% 7.73/1.49  ------ Input Options
% 7.73/1.49  
% 7.73/1.49  --out_options                           all
% 7.73/1.49  --tptp_safe_out                         true
% 7.73/1.49  --problem_path                          ""
% 7.73/1.49  --include_path                          ""
% 7.73/1.49  --clausifier                            res/vclausify_rel
% 7.73/1.49  --clausifier_options                    ""
% 7.73/1.49  --stdin                                 false
% 7.73/1.49  --stats_out                             all
% 7.73/1.49  
% 7.73/1.49  ------ General Options
% 7.73/1.49  
% 7.73/1.49  --fof                                   false
% 7.73/1.49  --time_out_real                         305.
% 7.73/1.49  --time_out_virtual                      -1.
% 7.73/1.49  --symbol_type_check                     false
% 7.73/1.49  --clausify_out                          false
% 7.73/1.49  --sig_cnt_out                           false
% 7.73/1.49  --trig_cnt_out                          false
% 7.73/1.49  --trig_cnt_out_tolerance                1.
% 7.73/1.49  --trig_cnt_out_sk_spl                   false
% 7.73/1.49  --abstr_cl_out                          false
% 7.73/1.49  
% 7.73/1.49  ------ Global Options
% 7.73/1.49  
% 7.73/1.49  --schedule                              default
% 7.73/1.49  --add_important_lit                     false
% 7.73/1.49  --prop_solver_per_cl                    1000
% 7.73/1.49  --min_unsat_core                        false
% 7.73/1.49  --soft_assumptions                      false
% 7.73/1.49  --soft_lemma_size                       3
% 7.73/1.49  --prop_impl_unit_size                   0
% 7.73/1.49  --prop_impl_unit                        []
% 7.73/1.49  --share_sel_clauses                     true
% 7.73/1.49  --reset_solvers                         false
% 7.73/1.49  --bc_imp_inh                            [conj_cone]
% 7.73/1.49  --conj_cone_tolerance                   3.
% 7.73/1.49  --extra_neg_conj                        none
% 7.73/1.49  --large_theory_mode                     true
% 7.73/1.49  --prolific_symb_bound                   200
% 7.73/1.49  --lt_threshold                          2000
% 7.73/1.49  --clause_weak_htbl                      true
% 7.73/1.49  --gc_record_bc_elim                     false
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing Options
% 7.73/1.49  
% 7.73/1.49  --preprocessing_flag                    true
% 7.73/1.49  --time_out_prep_mult                    0.1
% 7.73/1.49  --splitting_mode                        input
% 7.73/1.49  --splitting_grd                         true
% 7.73/1.49  --splitting_cvd                         false
% 7.73/1.49  --splitting_cvd_svl                     false
% 7.73/1.49  --splitting_nvd                         32
% 7.73/1.49  --sub_typing                            true
% 7.73/1.49  --prep_gs_sim                           true
% 7.73/1.49  --prep_unflatten                        true
% 7.73/1.49  --prep_res_sim                          true
% 7.73/1.49  --prep_upred                            true
% 7.73/1.49  --prep_sem_filter                       exhaustive
% 7.73/1.49  --prep_sem_filter_out                   false
% 7.73/1.49  --pred_elim                             true
% 7.73/1.49  --res_sim_input                         true
% 7.73/1.49  --eq_ax_congr_red                       true
% 7.73/1.49  --pure_diseq_elim                       true
% 7.73/1.49  --brand_transform                       false
% 7.73/1.49  --non_eq_to_eq                          false
% 7.73/1.49  --prep_def_merge                        true
% 7.73/1.49  --prep_def_merge_prop_impl              false
% 7.73/1.49  --prep_def_merge_mbd                    true
% 7.73/1.49  --prep_def_merge_tr_red                 false
% 7.73/1.49  --prep_def_merge_tr_cl                  false
% 7.73/1.49  --smt_preprocessing                     true
% 7.73/1.49  --smt_ac_axioms                         fast
% 7.73/1.49  --preprocessed_out                      false
% 7.73/1.49  --preprocessed_stats                    false
% 7.73/1.49  
% 7.73/1.49  ------ Abstraction refinement Options
% 7.73/1.49  
% 7.73/1.49  --abstr_ref                             []
% 7.73/1.49  --abstr_ref_prep                        false
% 7.73/1.49  --abstr_ref_until_sat                   false
% 7.73/1.49  --abstr_ref_sig_restrict                funpre
% 7.73/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.49  --abstr_ref_under                       []
% 7.73/1.49  
% 7.73/1.49  ------ SAT Options
% 7.73/1.49  
% 7.73/1.49  --sat_mode                              false
% 7.73/1.49  --sat_fm_restart_options                ""
% 7.73/1.49  --sat_gr_def                            false
% 7.73/1.49  --sat_epr_types                         true
% 7.73/1.49  --sat_non_cyclic_types                  false
% 7.73/1.49  --sat_finite_models                     false
% 7.73/1.49  --sat_fm_lemmas                         false
% 7.73/1.49  --sat_fm_prep                           false
% 7.73/1.49  --sat_fm_uc_incr                        true
% 7.73/1.49  --sat_out_model                         small
% 7.73/1.49  --sat_out_clauses                       false
% 7.73/1.49  
% 7.73/1.49  ------ QBF Options
% 7.73/1.49  
% 7.73/1.49  --qbf_mode                              false
% 7.73/1.49  --qbf_elim_univ                         false
% 7.73/1.49  --qbf_dom_inst                          none
% 7.73/1.49  --qbf_dom_pre_inst                      false
% 7.73/1.49  --qbf_sk_in                             false
% 7.73/1.49  --qbf_pred_elim                         true
% 7.73/1.49  --qbf_split                             512
% 7.73/1.49  
% 7.73/1.49  ------ BMC1 Options
% 7.73/1.49  
% 7.73/1.49  --bmc1_incremental                      false
% 7.73/1.49  --bmc1_axioms                           reachable_all
% 7.73/1.49  --bmc1_min_bound                        0
% 7.73/1.49  --bmc1_max_bound                        -1
% 7.73/1.49  --bmc1_max_bound_default                -1
% 7.73/1.49  --bmc1_symbol_reachability              true
% 7.73/1.49  --bmc1_property_lemmas                  false
% 7.73/1.49  --bmc1_k_induction                      false
% 7.73/1.49  --bmc1_non_equiv_states                 false
% 7.73/1.49  --bmc1_deadlock                         false
% 7.73/1.49  --bmc1_ucm                              false
% 7.73/1.49  --bmc1_add_unsat_core                   none
% 7.73/1.49  --bmc1_unsat_core_children              false
% 7.73/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.49  --bmc1_out_stat                         full
% 7.73/1.49  --bmc1_ground_init                      false
% 7.73/1.49  --bmc1_pre_inst_next_state              false
% 7.73/1.49  --bmc1_pre_inst_state                   false
% 7.73/1.49  --bmc1_pre_inst_reach_state             false
% 7.73/1.49  --bmc1_out_unsat_core                   false
% 7.73/1.49  --bmc1_aig_witness_out                  false
% 7.73/1.49  --bmc1_verbose                          false
% 7.73/1.49  --bmc1_dump_clauses_tptp                false
% 7.73/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.49  --bmc1_dump_file                        -
% 7.73/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.49  --bmc1_ucm_extend_mode                  1
% 7.73/1.49  --bmc1_ucm_init_mode                    2
% 7.73/1.49  --bmc1_ucm_cone_mode                    none
% 7.73/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.49  --bmc1_ucm_relax_model                  4
% 7.73/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.49  --bmc1_ucm_layered_model                none
% 7.73/1.49  --bmc1_ucm_max_lemma_size               10
% 7.73/1.49  
% 7.73/1.49  ------ AIG Options
% 7.73/1.49  
% 7.73/1.49  --aig_mode                              false
% 7.73/1.49  
% 7.73/1.49  ------ Instantiation Options
% 7.73/1.49  
% 7.73/1.49  --instantiation_flag                    true
% 7.73/1.49  --inst_sos_flag                         true
% 7.73/1.49  --inst_sos_phase                        true
% 7.73/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel_side                     num_symb
% 7.73/1.49  --inst_solver_per_active                1400
% 7.73/1.49  --inst_solver_calls_frac                1.
% 7.73/1.49  --inst_passive_queue_type               priority_queues
% 7.73/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.49  --inst_passive_queues_freq              [25;2]
% 7.73/1.49  --inst_dismatching                      true
% 7.73/1.49  --inst_eager_unprocessed_to_passive     true
% 7.73/1.49  --inst_prop_sim_given                   true
% 7.73/1.49  --inst_prop_sim_new                     false
% 7.73/1.49  --inst_subs_new                         false
% 7.73/1.49  --inst_eq_res_simp                      false
% 7.73/1.49  --inst_subs_given                       false
% 7.73/1.49  --inst_orphan_elimination               true
% 7.73/1.49  --inst_learning_loop_flag               true
% 7.73/1.49  --inst_learning_start                   3000
% 7.73/1.49  --inst_learning_factor                  2
% 7.73/1.49  --inst_start_prop_sim_after_learn       3
% 7.73/1.49  --inst_sel_renew                        solver
% 7.73/1.49  --inst_lit_activity_flag                true
% 7.73/1.49  --inst_restr_to_given                   false
% 7.73/1.49  --inst_activity_threshold               500
% 7.73/1.49  --inst_out_proof                        true
% 7.73/1.49  
% 7.73/1.49  ------ Resolution Options
% 7.73/1.49  
% 7.73/1.49  --resolution_flag                       true
% 7.73/1.49  --res_lit_sel                           adaptive
% 7.73/1.49  --res_lit_sel_side                      none
% 7.73/1.49  --res_ordering                          kbo
% 7.73/1.49  --res_to_prop_solver                    active
% 7.73/1.49  --res_prop_simpl_new                    false
% 7.73/1.49  --res_prop_simpl_given                  true
% 7.73/1.49  --res_passive_queue_type                priority_queues
% 7.73/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.49  --res_passive_queues_freq               [15;5]
% 7.73/1.49  --res_forward_subs                      full
% 7.73/1.49  --res_backward_subs                     full
% 7.73/1.49  --res_forward_subs_resolution           true
% 7.73/1.49  --res_backward_subs_resolution          true
% 7.73/1.49  --res_orphan_elimination                true
% 7.73/1.49  --res_time_limit                        2.
% 7.73/1.49  --res_out_proof                         true
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Options
% 7.73/1.49  
% 7.73/1.49  --superposition_flag                    true
% 7.73/1.49  --sup_passive_queue_type                priority_queues
% 7.73/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.49  --demod_completeness_check              fast
% 7.73/1.49  --demod_use_ground                      true
% 7.73/1.49  --sup_to_prop_solver                    passive
% 7.73/1.49  --sup_prop_simpl_new                    true
% 7.73/1.49  --sup_prop_simpl_given                  true
% 7.73/1.49  --sup_fun_splitting                     true
% 7.73/1.49  --sup_smt_interval                      50000
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Simplification Setup
% 7.73/1.49  
% 7.73/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.73/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.73/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.73/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.73/1.49  --sup_immed_triv                        [TrivRules]
% 7.73/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.49  --sup_immed_bw_main                     []
% 7.73/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.73/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.49  --sup_input_bw                          []
% 7.73/1.49  
% 7.73/1.49  ------ Combination Options
% 7.73/1.49  
% 7.73/1.49  --comb_res_mult                         3
% 7.73/1.49  --comb_sup_mult                         2
% 7.73/1.49  --comb_inst_mult                        10
% 7.73/1.49  
% 7.73/1.49  ------ Debug Options
% 7.73/1.49  
% 7.73/1.49  --dbg_backtrace                         false
% 7.73/1.49  --dbg_dump_prop_clauses                 false
% 7.73/1.49  --dbg_dump_prop_clauses_file            -
% 7.73/1.49  --dbg_out_stat                          false
% 7.73/1.49  ------ Parsing...
% 7.73/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  ------ Proving...
% 7.73/1.49  ------ Problem Properties 
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  clauses                                 38
% 7.73/1.49  conjectures                             11
% 7.73/1.49  EPR                                     9
% 7.73/1.49  Horn                                    34
% 7.73/1.49  unary                                   15
% 7.73/1.49  binary                                  4
% 7.73/1.49  lits                                    134
% 7.73/1.49  lits eq                                 30
% 7.73/1.49  fd_pure                                 0
% 7.73/1.49  fd_pseudo                               0
% 7.73/1.49  fd_cond                                 4
% 7.73/1.49  fd_pseudo_cond                          1
% 7.73/1.49  AC symbols                              0
% 7.73/1.49  
% 7.73/1.49  ------ Schedule dynamic 5 is on 
% 7.73/1.49  
% 7.73/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ 
% 7.73/1.49  Current options:
% 7.73/1.49  ------ 
% 7.73/1.49  
% 7.73/1.49  ------ Input Options
% 7.73/1.49  
% 7.73/1.49  --out_options                           all
% 7.73/1.49  --tptp_safe_out                         true
% 7.73/1.49  --problem_path                          ""
% 7.73/1.49  --include_path                          ""
% 7.73/1.49  --clausifier                            res/vclausify_rel
% 7.73/1.49  --clausifier_options                    ""
% 7.73/1.49  --stdin                                 false
% 7.73/1.49  --stats_out                             all
% 7.73/1.49  
% 7.73/1.49  ------ General Options
% 7.73/1.49  
% 7.73/1.49  --fof                                   false
% 7.73/1.49  --time_out_real                         305.
% 7.73/1.49  --time_out_virtual                      -1.
% 7.73/1.49  --symbol_type_check                     false
% 7.73/1.49  --clausify_out                          false
% 7.73/1.49  --sig_cnt_out                           false
% 7.73/1.49  --trig_cnt_out                          false
% 7.73/1.49  --trig_cnt_out_tolerance                1.
% 7.73/1.49  --trig_cnt_out_sk_spl                   false
% 7.73/1.49  --abstr_cl_out                          false
% 7.73/1.49  
% 7.73/1.49  ------ Global Options
% 7.73/1.49  
% 7.73/1.49  --schedule                              default
% 7.73/1.49  --add_important_lit                     false
% 7.73/1.49  --prop_solver_per_cl                    1000
% 7.73/1.49  --min_unsat_core                        false
% 7.73/1.49  --soft_assumptions                      false
% 7.73/1.49  --soft_lemma_size                       3
% 7.73/1.49  --prop_impl_unit_size                   0
% 7.73/1.49  --prop_impl_unit                        []
% 7.73/1.49  --share_sel_clauses                     true
% 7.73/1.49  --reset_solvers                         false
% 7.73/1.49  --bc_imp_inh                            [conj_cone]
% 7.73/1.49  --conj_cone_tolerance                   3.
% 7.73/1.49  --extra_neg_conj                        none
% 7.73/1.49  --large_theory_mode                     true
% 7.73/1.49  --prolific_symb_bound                   200
% 7.73/1.49  --lt_threshold                          2000
% 7.73/1.49  --clause_weak_htbl                      true
% 7.73/1.49  --gc_record_bc_elim                     false
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing Options
% 7.73/1.49  
% 7.73/1.49  --preprocessing_flag                    true
% 7.73/1.49  --time_out_prep_mult                    0.1
% 7.73/1.49  --splitting_mode                        input
% 7.73/1.49  --splitting_grd                         true
% 7.73/1.49  --splitting_cvd                         false
% 7.73/1.49  --splitting_cvd_svl                     false
% 7.73/1.49  --splitting_nvd                         32
% 7.73/1.49  --sub_typing                            true
% 7.73/1.49  --prep_gs_sim                           true
% 7.73/1.49  --prep_unflatten                        true
% 7.73/1.49  --prep_res_sim                          true
% 7.73/1.49  --prep_upred                            true
% 7.73/1.49  --prep_sem_filter                       exhaustive
% 7.73/1.49  --prep_sem_filter_out                   false
% 7.73/1.49  --pred_elim                             true
% 7.73/1.49  --res_sim_input                         true
% 7.73/1.49  --eq_ax_congr_red                       true
% 7.73/1.49  --pure_diseq_elim                       true
% 7.73/1.49  --brand_transform                       false
% 7.73/1.49  --non_eq_to_eq                          false
% 7.73/1.49  --prep_def_merge                        true
% 7.73/1.49  --prep_def_merge_prop_impl              false
% 7.73/1.49  --prep_def_merge_mbd                    true
% 7.73/1.49  --prep_def_merge_tr_red                 false
% 7.73/1.49  --prep_def_merge_tr_cl                  false
% 7.73/1.49  --smt_preprocessing                     true
% 7.73/1.49  --smt_ac_axioms                         fast
% 7.73/1.49  --preprocessed_out                      false
% 7.73/1.49  --preprocessed_stats                    false
% 7.73/1.49  
% 7.73/1.49  ------ Abstraction refinement Options
% 7.73/1.49  
% 7.73/1.49  --abstr_ref                             []
% 7.73/1.49  --abstr_ref_prep                        false
% 7.73/1.49  --abstr_ref_until_sat                   false
% 7.73/1.49  --abstr_ref_sig_restrict                funpre
% 7.73/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.49  --abstr_ref_under                       []
% 7.73/1.49  
% 7.73/1.49  ------ SAT Options
% 7.73/1.49  
% 7.73/1.49  --sat_mode                              false
% 7.73/1.49  --sat_fm_restart_options                ""
% 7.73/1.49  --sat_gr_def                            false
% 7.73/1.49  --sat_epr_types                         true
% 7.73/1.49  --sat_non_cyclic_types                  false
% 7.73/1.49  --sat_finite_models                     false
% 7.73/1.49  --sat_fm_lemmas                         false
% 7.73/1.49  --sat_fm_prep                           false
% 7.73/1.49  --sat_fm_uc_incr                        true
% 7.73/1.49  --sat_out_model                         small
% 7.73/1.49  --sat_out_clauses                       false
% 7.73/1.49  
% 7.73/1.49  ------ QBF Options
% 7.73/1.49  
% 7.73/1.49  --qbf_mode                              false
% 7.73/1.49  --qbf_elim_univ                         false
% 7.73/1.49  --qbf_dom_inst                          none
% 7.73/1.49  --qbf_dom_pre_inst                      false
% 7.73/1.49  --qbf_sk_in                             false
% 7.73/1.49  --qbf_pred_elim                         true
% 7.73/1.49  --qbf_split                             512
% 7.73/1.49  
% 7.73/1.49  ------ BMC1 Options
% 7.73/1.49  
% 7.73/1.49  --bmc1_incremental                      false
% 7.73/1.49  --bmc1_axioms                           reachable_all
% 7.73/1.49  --bmc1_min_bound                        0
% 7.73/1.49  --bmc1_max_bound                        -1
% 7.73/1.49  --bmc1_max_bound_default                -1
% 7.73/1.49  --bmc1_symbol_reachability              true
% 7.73/1.49  --bmc1_property_lemmas                  false
% 7.73/1.49  --bmc1_k_induction                      false
% 7.73/1.49  --bmc1_non_equiv_states                 false
% 7.73/1.49  --bmc1_deadlock                         false
% 7.73/1.49  --bmc1_ucm                              false
% 7.73/1.49  --bmc1_add_unsat_core                   none
% 7.73/1.49  --bmc1_unsat_core_children              false
% 7.73/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.49  --bmc1_out_stat                         full
% 7.73/1.49  --bmc1_ground_init                      false
% 7.73/1.49  --bmc1_pre_inst_next_state              false
% 7.73/1.49  --bmc1_pre_inst_state                   false
% 7.73/1.49  --bmc1_pre_inst_reach_state             false
% 7.73/1.49  --bmc1_out_unsat_core                   false
% 7.73/1.49  --bmc1_aig_witness_out                  false
% 7.73/1.49  --bmc1_verbose                          false
% 7.73/1.49  --bmc1_dump_clauses_tptp                false
% 7.73/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.49  --bmc1_dump_file                        -
% 7.73/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.49  --bmc1_ucm_extend_mode                  1
% 7.73/1.49  --bmc1_ucm_init_mode                    2
% 7.73/1.49  --bmc1_ucm_cone_mode                    none
% 7.73/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.49  --bmc1_ucm_relax_model                  4
% 7.73/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.49  --bmc1_ucm_layered_model                none
% 7.73/1.49  --bmc1_ucm_max_lemma_size               10
% 7.73/1.49  
% 7.73/1.49  ------ AIG Options
% 7.73/1.49  
% 7.73/1.49  --aig_mode                              false
% 7.73/1.49  
% 7.73/1.49  ------ Instantiation Options
% 7.73/1.49  
% 7.73/1.49  --instantiation_flag                    true
% 7.73/1.49  --inst_sos_flag                         true
% 7.73/1.49  --inst_sos_phase                        true
% 7.73/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel_side                     none
% 7.73/1.49  --inst_solver_per_active                1400
% 7.73/1.49  --inst_solver_calls_frac                1.
% 7.73/1.49  --inst_passive_queue_type               priority_queues
% 7.73/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.49  --inst_passive_queues_freq              [25;2]
% 7.73/1.49  --inst_dismatching                      true
% 7.73/1.49  --inst_eager_unprocessed_to_passive     true
% 7.73/1.50  --inst_prop_sim_given                   true
% 7.73/1.50  --inst_prop_sim_new                     false
% 7.73/1.50  --inst_subs_new                         false
% 7.73/1.50  --inst_eq_res_simp                      false
% 7.73/1.50  --inst_subs_given                       false
% 7.73/1.50  --inst_orphan_elimination               true
% 7.73/1.50  --inst_learning_loop_flag               true
% 7.73/1.50  --inst_learning_start                   3000
% 7.73/1.50  --inst_learning_factor                  2
% 7.73/1.50  --inst_start_prop_sim_after_learn       3
% 7.73/1.50  --inst_sel_renew                        solver
% 7.73/1.50  --inst_lit_activity_flag                true
% 7.73/1.50  --inst_restr_to_given                   false
% 7.73/1.50  --inst_activity_threshold               500
% 7.73/1.50  --inst_out_proof                        true
% 7.73/1.50  
% 7.73/1.50  ------ Resolution Options
% 7.73/1.50  
% 7.73/1.50  --resolution_flag                       false
% 7.73/1.50  --res_lit_sel                           adaptive
% 7.73/1.50  --res_lit_sel_side                      none
% 7.73/1.50  --res_ordering                          kbo
% 7.73/1.50  --res_to_prop_solver                    active
% 7.73/1.50  --res_prop_simpl_new                    false
% 7.73/1.50  --res_prop_simpl_given                  true
% 7.73/1.50  --res_passive_queue_type                priority_queues
% 7.73/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.50  --res_passive_queues_freq               [15;5]
% 7.73/1.50  --res_forward_subs                      full
% 7.73/1.50  --res_backward_subs                     full
% 7.73/1.50  --res_forward_subs_resolution           true
% 7.73/1.50  --res_backward_subs_resolution          true
% 7.73/1.50  --res_orphan_elimination                true
% 7.73/1.50  --res_time_limit                        2.
% 7.73/1.50  --res_out_proof                         true
% 7.73/1.50  
% 7.73/1.50  ------ Superposition Options
% 7.73/1.50  
% 7.73/1.50  --superposition_flag                    true
% 7.73/1.50  --sup_passive_queue_type                priority_queues
% 7.73/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.50  --demod_completeness_check              fast
% 7.73/1.50  --demod_use_ground                      true
% 7.73/1.50  --sup_to_prop_solver                    passive
% 7.73/1.50  --sup_prop_simpl_new                    true
% 7.73/1.50  --sup_prop_simpl_given                  true
% 7.73/1.50  --sup_fun_splitting                     true
% 7.73/1.50  --sup_smt_interval                      50000
% 7.73/1.50  
% 7.73/1.50  ------ Superposition Simplification Setup
% 7.73/1.50  
% 7.73/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.73/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.73/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.73/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.73/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.73/1.50  --sup_immed_triv                        [TrivRules]
% 7.73/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.50  --sup_immed_bw_main                     []
% 7.73/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.73/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.50  --sup_input_bw                          []
% 7.73/1.50  
% 7.73/1.50  ------ Combination Options
% 7.73/1.50  
% 7.73/1.50  --comb_res_mult                         3
% 7.73/1.50  --comb_sup_mult                         2
% 7.73/1.50  --comb_inst_mult                        10
% 7.73/1.50  
% 7.73/1.50  ------ Debug Options
% 7.73/1.50  
% 7.73/1.50  --dbg_backtrace                         false
% 7.73/1.50  --dbg_dump_prop_clauses                 false
% 7.73/1.50  --dbg_dump_prop_clauses_file            -
% 7.73/1.50  --dbg_out_stat                          false
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  % SZS status Theorem for theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  fof(f19,conjecture,(
% 7.73/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f20,negated_conjecture,(
% 7.73/1.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.73/1.50    inference(negated_conjecture,[],[f19])).
% 7.73/1.50  
% 7.73/1.50  fof(f45,plain,(
% 7.73/1.50    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.73/1.50    inference(ennf_transformation,[],[f20])).
% 7.73/1.50  
% 7.73/1.50  fof(f46,plain,(
% 7.73/1.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.73/1.50    inference(flattening,[],[f45])).
% 7.73/1.50  
% 7.73/1.50  fof(f51,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f50,plain,(
% 7.73/1.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f52,plain,(
% 7.73/1.50    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.73/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f51,f50])).
% 7.73/1.50  
% 7.73/1.50  fof(f87,plain,(
% 7.73/1.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.73/1.50    inference(cnf_transformation,[],[f52])).
% 7.73/1.50  
% 7.73/1.50  fof(f9,axiom,(
% 7.73/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f31,plain,(
% 7.73/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.50    inference(ennf_transformation,[],[f9])).
% 7.73/1.50  
% 7.73/1.50  fof(f66,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f31])).
% 7.73/1.50  
% 7.73/1.50  fof(f85,plain,(
% 7.73/1.50    v1_funct_1(sK3)),
% 7.73/1.50    inference(cnf_transformation,[],[f52])).
% 7.73/1.50  
% 7.73/1.50  fof(f5,axiom,(
% 7.73/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f25,plain,(
% 7.73/1.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.73/1.50    inference(ennf_transformation,[],[f5])).
% 7.73/1.50  
% 7.73/1.50  fof(f26,plain,(
% 7.73/1.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.73/1.50    inference(flattening,[],[f25])).
% 7.73/1.50  
% 7.73/1.50  fof(f59,plain,(
% 7.73/1.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f26])).
% 7.73/1.50  
% 7.73/1.50  fof(f2,axiom,(
% 7.73/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f21,plain,(
% 7.73/1.50    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.73/1.50    inference(ennf_transformation,[],[f2])).
% 7.73/1.50  
% 7.73/1.50  fof(f56,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f21])).
% 7.73/1.50  
% 7.73/1.50  fof(f16,axiom,(
% 7.73/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f39,plain,(
% 7.73/1.50    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.73/1.50    inference(ennf_transformation,[],[f16])).
% 7.73/1.50  
% 7.73/1.50  fof(f40,plain,(
% 7.73/1.50    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.73/1.50    inference(flattening,[],[f39])).
% 7.73/1.50  
% 7.73/1.50  fof(f75,plain,(
% 7.73/1.50    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f40])).
% 7.73/1.50  
% 7.73/1.50  fof(f89,plain,(
% 7.73/1.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.73/1.50    inference(cnf_transformation,[],[f52])).
% 7.73/1.50  
% 7.73/1.50  fof(f82,plain,(
% 7.73/1.50    v1_funct_1(sK2)),
% 7.73/1.50    inference(cnf_transformation,[],[f52])).
% 7.73/1.50  
% 7.73/1.50  fof(f83,plain,(
% 7.73/1.50    v1_funct_2(sK2,sK0,sK1)),
% 7.73/1.50    inference(cnf_transformation,[],[f52])).
% 7.73/1.50  
% 7.73/1.50  fof(f84,plain,(
% 7.73/1.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.73/1.50    inference(cnf_transformation,[],[f52])).
% 7.73/1.50  
% 7.73/1.50  fof(f86,plain,(
% 7.73/1.50    v1_funct_2(sK3,sK1,sK0)),
% 7.73/1.50    inference(cnf_transformation,[],[f52])).
% 7.73/1.50  
% 7.73/1.50  fof(f18,axiom,(
% 7.73/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f43,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.73/1.50    inference(ennf_transformation,[],[f18])).
% 7.73/1.50  
% 7.73/1.50  fof(f44,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.73/1.50    inference(flattening,[],[f43])).
% 7.73/1.50  
% 7.73/1.50  fof(f80,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f44])).
% 7.73/1.50  
% 7.73/1.50  fof(f91,plain,(
% 7.73/1.50    k1_xboole_0 != sK0),
% 7.73/1.50    inference(cnf_transformation,[],[f52])).
% 7.73/1.50  
% 7.73/1.50  fof(f1,axiom,(
% 7.73/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f47,plain,(
% 7.73/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.50    inference(nnf_transformation,[],[f1])).
% 7.73/1.50  
% 7.73/1.50  fof(f48,plain,(
% 7.73/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.50    inference(flattening,[],[f47])).
% 7.73/1.50  
% 7.73/1.50  fof(f53,plain,(
% 7.73/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.73/1.50    inference(cnf_transformation,[],[f48])).
% 7.73/1.50  
% 7.73/1.50  fof(f100,plain,(
% 7.73/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.73/1.50    inference(equality_resolution,[],[f53])).
% 7.73/1.50  
% 7.73/1.50  fof(f55,plain,(
% 7.73/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f48])).
% 7.73/1.50  
% 7.73/1.50  fof(f6,axiom,(
% 7.73/1.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f62,plain,(
% 7.73/1.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f6])).
% 7.73/1.50  
% 7.73/1.50  fof(f15,axiom,(
% 7.73/1.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f74,plain,(
% 7.73/1.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f15])).
% 7.73/1.50  
% 7.73/1.50  fof(f96,plain,(
% 7.73/1.50    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.73/1.50    inference(definition_unfolding,[],[f62,f74])).
% 7.73/1.50  
% 7.73/1.50  fof(f11,axiom,(
% 7.73/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f33,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.73/1.50    inference(ennf_transformation,[],[f11])).
% 7.73/1.50  
% 7.73/1.50  fof(f34,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.50    inference(flattening,[],[f33])).
% 7.73/1.50  
% 7.73/1.50  fof(f49,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.50    inference(nnf_transformation,[],[f34])).
% 7.73/1.50  
% 7.73/1.50  fof(f68,plain,(
% 7.73/1.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f49])).
% 7.73/1.50  
% 7.73/1.50  fof(f12,axiom,(
% 7.73/1.50    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f70,plain,(
% 7.73/1.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f12])).
% 7.73/1.50  
% 7.73/1.50  fof(f98,plain,(
% 7.73/1.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.73/1.50    inference(definition_unfolding,[],[f70,f74])).
% 7.73/1.50  
% 7.73/1.50  fof(f13,axiom,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f35,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.73/1.50    inference(ennf_transformation,[],[f13])).
% 7.73/1.50  
% 7.73/1.50  fof(f36,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.73/1.50    inference(flattening,[],[f35])).
% 7.73/1.50  
% 7.73/1.50  fof(f72,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f36])).
% 7.73/1.50  
% 7.73/1.50  fof(f88,plain,(
% 7.73/1.50    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.73/1.50    inference(cnf_transformation,[],[f52])).
% 7.73/1.50  
% 7.73/1.50  fof(f17,axiom,(
% 7.73/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f41,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.73/1.50    inference(ennf_transformation,[],[f17])).
% 7.73/1.50  
% 7.73/1.50  fof(f42,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.73/1.50    inference(flattening,[],[f41])).
% 7.73/1.50  
% 7.73/1.50  fof(f78,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f42])).
% 7.73/1.50  
% 7.73/1.50  fof(f7,axiom,(
% 7.73/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f27,plain,(
% 7.73/1.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.73/1.50    inference(ennf_transformation,[],[f7])).
% 7.73/1.50  
% 7.73/1.50  fof(f28,plain,(
% 7.73/1.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.73/1.50    inference(flattening,[],[f27])).
% 7.73/1.50  
% 7.73/1.50  fof(f63,plain,(
% 7.73/1.50    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f28])).
% 7.73/1.50  
% 7.73/1.50  fof(f10,axiom,(
% 7.73/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f32,plain,(
% 7.73/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.50    inference(ennf_transformation,[],[f10])).
% 7.73/1.50  
% 7.73/1.50  fof(f67,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f32])).
% 7.73/1.50  
% 7.73/1.50  fof(f3,axiom,(
% 7.73/1.50    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f22,plain,(
% 7.73/1.50    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 7.73/1.50    inference(ennf_transformation,[],[f3])).
% 7.73/1.50  
% 7.73/1.50  fof(f57,plain,(
% 7.73/1.50    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f22])).
% 7.73/1.50  
% 7.73/1.50  fof(f94,plain,(
% 7.73/1.50    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.73/1.50    inference(definition_unfolding,[],[f57,f74])).
% 7.73/1.50  
% 7.73/1.50  fof(f14,axiom,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f37,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.73/1.50    inference(ennf_transformation,[],[f14])).
% 7.73/1.50  
% 7.73/1.50  fof(f38,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.73/1.50    inference(flattening,[],[f37])).
% 7.73/1.50  
% 7.73/1.50  fof(f73,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f38])).
% 7.73/1.50  
% 7.73/1.50  fof(f54,plain,(
% 7.73/1.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.73/1.50    inference(cnf_transformation,[],[f48])).
% 7.73/1.50  
% 7.73/1.50  fof(f99,plain,(
% 7.73/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.73/1.50    inference(equality_resolution,[],[f54])).
% 7.73/1.50  
% 7.73/1.50  fof(f4,axiom,(
% 7.73/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.73/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f23,plain,(
% 7.73/1.50    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.73/1.50    inference(ennf_transformation,[],[f4])).
% 7.73/1.50  
% 7.73/1.50  fof(f24,plain,(
% 7.73/1.50    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.73/1.50    inference(flattening,[],[f23])).
% 7.73/1.50  
% 7.73/1.50  fof(f58,plain,(
% 7.73/1.50    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f24])).
% 7.73/1.50  
% 7.73/1.50  fof(f95,plain,(
% 7.73/1.50    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.73/1.50    inference(definition_unfolding,[],[f58,f74])).
% 7.73/1.50  
% 7.73/1.50  fof(f81,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f44])).
% 7.73/1.50  
% 7.73/1.50  fof(f90,plain,(
% 7.73/1.50    v2_funct_1(sK2)),
% 7.73/1.50    inference(cnf_transformation,[],[f52])).
% 7.73/1.50  
% 7.73/1.50  fof(f92,plain,(
% 7.73/1.50    k1_xboole_0 != sK1),
% 7.73/1.50    inference(cnf_transformation,[],[f52])).
% 7.73/1.50  
% 7.73/1.50  fof(f93,plain,(
% 7.73/1.50    k2_funct_1(sK2) != sK3),
% 7.73/1.50    inference(cnf_transformation,[],[f52])).
% 7.73/1.50  
% 7.73/1.50  cnf(c_34,negated_conjecture,
% 7.73/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.73/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1305,plain,
% 7.73/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_13,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | v1_relat_1(X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1318,plain,
% 7.73/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.73/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2429,plain,
% 7.73/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1305,c_1318]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_36,negated_conjecture,
% 7.73/1.50      ( v1_funct_1(sK3) ),
% 7.73/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1303,plain,
% 7.73/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_7,plain,
% 7.73/1.50      ( ~ v1_funct_1(X0)
% 7.73/1.50      | ~ v1_relat_1(X0)
% 7.73/1.50      | v1_relat_1(k2_funct_1(X0)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1324,plain,
% 7.73/1.50      ( v1_funct_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3,plain,
% 7.73/1.50      ( ~ v1_relat_1(X0)
% 7.73/1.50      | ~ v1_relat_1(X1)
% 7.73/1.50      | ~ v1_relat_1(X2)
% 7.73/1.50      | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1328,plain,
% 7.73/1.50      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.73/1.50      | v1_relat_1(X2) != iProver_top
% 7.73/1.50      | v1_relat_1(X1) != iProver_top
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4213,plain,
% 7.73/1.50      ( k5_relat_1(sK3,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK3,X0),X1)
% 7.73/1.50      | v1_relat_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2429,c_1328]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5503,plain,
% 7.73/1.50      ( k5_relat_1(k5_relat_1(sK3,k2_funct_1(X0)),X1) = k5_relat_1(sK3,k5_relat_1(k2_funct_1(X0),X1))
% 7.73/1.50      | v1_funct_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1324,c_4213]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_17474,plain,
% 7.73/1.50      ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0)) = k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0)
% 7.73/1.50      | v1_relat_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1303,c_5503]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_21,plain,
% 7.73/1.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.73/1.50      | ~ v1_funct_2(X2,X0,X1)
% 7.73/1.50      | ~ v1_funct_2(X3,X1,X0)
% 7.73/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.73/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.73/1.50      | ~ v1_funct_1(X2)
% 7.73/1.50      | ~ v1_funct_1(X3)
% 7.73/1.50      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.73/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_32,negated_conjecture,
% 7.73/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_447,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.73/1.50      | ~ v1_funct_2(X3,X2,X1)
% 7.73/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | ~ v1_funct_1(X3)
% 7.73/1.50      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.73/1.50      | k2_relset_1(X1,X2,X0) = X2
% 7.73/1.50      | k6_partfun1(X2) != k6_partfun1(sK0)
% 7.73/1.50      | sK0 != X2 ),
% 7.73/1.50      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_448,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,X1,sK0)
% 7.73/1.50      | ~ v1_funct_2(X2,sK0,X1)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.73/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | ~ v1_funct_1(X2)
% 7.73/1.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.73/1.50      | k2_relset_1(X1,sK0,X0) = sK0
% 7.73/1.50      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.73/1.50      inference(unflattening,[status(thm)],[c_447]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_536,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,X1,sK0)
% 7.73/1.50      | ~ v1_funct_2(X2,sK0,X1)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.73/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | ~ v1_funct_1(X2)
% 7.73/1.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.73/1.50      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.73/1.50      inference(equality_resolution_simp,[status(thm)],[c_448]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1297,plain,
% 7.73/1.50      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.73/1.50      | k2_relset_1(X0,sK0,X2) = sK0
% 7.73/1.50      | v1_funct_2(X2,X0,sK0) != iProver_top
% 7.73/1.50      | v1_funct_2(X1,sK0,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.73/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.73/1.50      | v1_funct_1(X2) != iProver_top
% 7.73/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1807,plain,
% 7.73/1.50      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.73/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.73/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.73/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.73/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.73/1.50      | v1_funct_1(sK3) != iProver_top
% 7.73/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.73/1.50      inference(equality_resolution,[status(thm)],[c_1297]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_39,negated_conjecture,
% 7.73/1.50      ( v1_funct_1(sK2) ),
% 7.73/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_40,plain,
% 7.73/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_38,negated_conjecture,
% 7.73/1.50      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_41,plain,
% 7.73/1.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_37,negated_conjecture,
% 7.73/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.73/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_42,plain,
% 7.73/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_43,plain,
% 7.73/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_35,negated_conjecture,
% 7.73/1.50      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_44,plain,
% 7.73/1.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_45,plain,
% 7.73/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2269,plain,
% 7.73/1.50      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_1807,c_40,c_41,c_42,c_43,c_44,c_45]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_27,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | ~ v2_funct_1(X0)
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | k2_relset_1(X1,X2,X0) != X2
% 7.73/1.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.73/1.50      | k1_xboole_0 = X2 ),
% 7.73/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1307,plain,
% 7.73/1.50      ( k2_relset_1(X0,X1,X2) != X1
% 7.73/1.50      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 7.73/1.50      | k1_xboole_0 = X1
% 7.73/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.73/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.73/1.50      | v2_funct_1(X2) != iProver_top
% 7.73/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3496,plain,
% 7.73/1.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.73/1.50      | sK0 = k1_xboole_0
% 7.73/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.73/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.73/1.50      | v2_funct_1(sK3) != iProver_top
% 7.73/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2269,c_1307]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_30,negated_conjecture,
% 7.73/1.50      ( k1_xboole_0 != sK0 ),
% 7.73/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2,plain,
% 7.73/1.50      ( r1_tarski(X0,X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_120,plain,
% 7.73/1.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_0,plain,
% 7.73/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.73/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_124,plain,
% 7.73/1.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.73/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_733,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1423,plain,
% 7.73/1.50      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_733]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1424,plain,
% 7.73/1.50      ( sK0 != k1_xboole_0
% 7.73/1.50      | k1_xboole_0 = sK0
% 7.73/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_1423]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_8,plain,
% 7.73/1.50      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3514,plain,
% 7.73/1.50      ( v2_funct_1(k6_partfun1(sK0)) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3515,plain,
% 7.73/1.50      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_3514]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_16,plain,
% 7.73/1.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.73/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.73/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.73/1.50      | X3 = X2 ),
% 7.73/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_434,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | X3 = X0
% 7.73/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.73/1.50      | k6_partfun1(sK0) != X3
% 7.73/1.50      | sK0 != X2
% 7.73/1.50      | sK0 != X1 ),
% 7.73/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_435,plain,
% 7.73/1.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.73/1.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.73/1.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.73/1.50      inference(unflattening,[status(thm)],[c_434]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_17,plain,
% 7.73/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.73/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_443,plain,
% 7.73/1.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.73/1.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.73/1.50      inference(forward_subsumption_resolution,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_435,c_17]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1298,plain,
% 7.73/1.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.73/1.50      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_18,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.73/1.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | ~ v1_funct_1(X3) ),
% 7.73/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1425,plain,
% 7.73/1.50      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.73/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.73/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.73/1.50      | ~ v1_funct_1(sK3)
% 7.73/1.50      | ~ v1_funct_1(sK2) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2218,plain,
% 7.73/1.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_1298,c_39,c_37,c_36,c_34,c_443,c_1425]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_33,negated_conjecture,
% 7.73/1.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.73/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_23,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.73/1.50      | ~ v1_funct_2(X3,X4,X1)
% 7.73/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | v2_funct_1(X0)
% 7.73/1.50      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | ~ v1_funct_1(X3)
% 7.73/1.50      | k2_relset_1(X4,X1,X3) != X1
% 7.73/1.50      | k1_xboole_0 = X2 ),
% 7.73/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1311,plain,
% 7.73/1.50      ( k2_relset_1(X0,X1,X2) != X1
% 7.73/1.50      | k1_xboole_0 = X3
% 7.73/1.50      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.73/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.73/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.73/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.73/1.50      | v2_funct_1(X4) = iProver_top
% 7.73/1.50      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 7.73/1.50      | v1_funct_1(X4) != iProver_top
% 7.73/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5232,plain,
% 7.73/1.50      ( k1_xboole_0 = X0
% 7.73/1.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.73/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.73/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.73/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.73/1.50      | v2_funct_1(X1) = iProver_top
% 7.73/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.73/1.50      | v1_funct_1(X1) != iProver_top
% 7.73/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_33,c_1311]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5239,plain,
% 7.73/1.50      ( v1_funct_1(X1) != iProver_top
% 7.73/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.73/1.50      | v2_funct_1(X1) = iProver_top
% 7.73/1.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.73/1.50      | k1_xboole_0 = X0
% 7.73/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_5232,c_40,c_41,c_42]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5240,plain,
% 7.73/1.50      ( k1_xboole_0 = X0
% 7.73/1.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.73/1.50      | v2_funct_1(X1) = iProver_top
% 7.73/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.73/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_5239]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5243,plain,
% 7.73/1.50      ( sK0 = k1_xboole_0
% 7.73/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.73/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.73/1.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.73/1.50      | v2_funct_1(sK3) = iProver_top
% 7.73/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2218,c_5240]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5929,plain,
% 7.73/1.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_3496,c_43,c_44,c_45,c_30,c_120,c_124,c_1424,c_3515,
% 7.73/1.50                 c_5243]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5296,plain,
% 7.73/1.50      ( v2_funct_1(sK3) = iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_5243,c_43,c_44,c_45,c_30,c_120,c_124,c_1424,c_3515]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11,plain,
% 7.73/1.50      ( ~ v2_funct_1(X0)
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | ~ v1_relat_1(X0)
% 7.73/1.50      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1320,plain,
% 7.73/1.50      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 7.73/1.50      | v2_funct_1(X0) != iProver_top
% 7.73/1.50      | v1_funct_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5301,plain,
% 7.73/1.50      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 7.73/1.50      | v1_funct_1(sK3) != iProver_top
% 7.73/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_5296,c_1320]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_14,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1317,plain,
% 7.73/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.73/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2435,plain,
% 7.73/1.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1305,c_1317]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2438,plain,
% 7.73/1.50      ( k2_relat_1(sK3) = sK0 ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_2435,c_2269]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5303,plain,
% 7.73/1.50      ( k1_relat_1(k2_funct_1(sK3)) = sK0
% 7.73/1.50      | v1_funct_1(sK3) != iProver_top
% 7.73/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_5301,c_2438]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_16528,plain,
% 7.73/1.50      ( k1_relat_1(k2_funct_1(sK3)) = sK0 ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_5303,c_43,c_2429]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4,plain,
% 7.73/1.50      ( ~ v1_relat_1(X0)
% 7.73/1.50      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 7.73/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1327,plain,
% 7.73/1.50      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2482,plain,
% 7.73/1.50      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0))),k2_funct_1(X0)) = k2_funct_1(X0)
% 7.73/1.50      | v1_funct_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1324,c_1327]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5578,plain,
% 7.73/1.50      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) = k2_funct_1(sK3)
% 7.73/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1303,c_2482]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5673,plain,
% 7.73/1.50      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) = k2_funct_1(sK3) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_5578,c_2429]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_16530,plain,
% 7.73/1.50      ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k2_funct_1(sK3) ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_16528,c_5673]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1302,plain,
% 7.73/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2430,plain,
% 7.73/1.50      ( v1_relat_1(sK2) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1302,c_1318]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4214,plain,
% 7.73/1.50      ( k5_relat_1(sK2,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK2,X0),X1)
% 7.73/1.50      | v1_relat_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2430,c_1328]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5893,plain,
% 7.73/1.50      ( k5_relat_1(k5_relat_1(sK2,sK3),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0))
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2429,c_4214]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_20,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | ~ v1_funct_1(X3)
% 7.73/1.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1313,plain,
% 7.73/1.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.73/1.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.73/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.73/1.50      | v1_funct_1(X5) != iProver_top
% 7.73/1.50      | v1_funct_1(X4) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4536,plain,
% 7.73/1.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.73/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.73/1.50      | v1_funct_1(X2) != iProver_top
% 7.73/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1305,c_1313]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4583,plain,
% 7.73/1.50      ( v1_funct_1(X2) != iProver_top
% 7.73/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.73/1.50      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_4536,c_43]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4584,plain,
% 7.73/1.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.73/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.73/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_4583]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4591,plain,
% 7.73/1.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.73/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1302,c_4584]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4592,plain,
% 7.73/1.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.73/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_4591,c_2218]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5081,plain,
% 7.73/1.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_4592,c_40]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5895,plain,
% 7.73/1.50      ( k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0)
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_5893,c_5081]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9648,plain,
% 7.73/1.50      ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(X0))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(X0))
% 7.73/1.50      | v1_funct_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1324,c_5895]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9847,plain,
% 7.73/1.50      ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
% 7.73/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1303,c_9648]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1,plain,
% 7.73/1.50      ( r1_tarski(X0,X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1329,plain,
% 7.73/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2436,plain,
% 7.73/1.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1302,c_1317]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2437,plain,
% 7.73/1.50      ( k2_relat_1(sK2) = sK1 ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_2436,c_33]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5,plain,
% 7.73/1.50      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.73/1.50      | ~ v1_relat_1(X0)
% 7.73/1.50      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 7.73/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1326,plain,
% 7.73/1.50      ( k5_relat_1(X0,k6_partfun1(X1)) = X0
% 7.73/1.50      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3504,plain,
% 7.73/1.50      ( k5_relat_1(sK2,k6_partfun1(X0)) = sK2
% 7.73/1.50      | r1_tarski(sK1,X0) != iProver_top
% 7.73/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2437,c_1326]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3913,plain,
% 7.73/1.50      ( r1_tarski(sK1,X0) != iProver_top
% 7.73/1.50      | k5_relat_1(sK2,k6_partfun1(X0)) = sK2 ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_3504,c_2430]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3914,plain,
% 7.73/1.50      ( k5_relat_1(sK2,k6_partfun1(X0)) = sK2
% 7.73/1.50      | r1_tarski(sK1,X0) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_3913]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3919,plain,
% 7.73/1.50      ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1329,c_3914]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9852,plain,
% 7.73/1.50      ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = sK2
% 7.73/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_9847,c_3919,c_5929]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10125,plain,
% 7.73/1.50      ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = sK2 ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_9852,c_2429]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_16531,plain,
% 7.73/1.50      ( k2_funct_1(sK3) = sK2 ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_16530,c_10125]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_17481,plain,
% 7.73/1.50      ( k5_relat_1(sK3,k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.73/1.50      | v1_relat_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_17474,c_5929,c_16531]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_17844,plain,
% 7.73/1.50      ( v1_relat_1(X0) != iProver_top
% 7.73/1.50      | k5_relat_1(sK3,k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_17481,c_2429]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_17845,plain,
% 7.73/1.50      ( k5_relat_1(sK3,k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_17844]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_17852,plain,
% 7.73/1.50      ( k5_relat_1(sK3,k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2429,c_17845]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3502,plain,
% 7.73/1.50      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1329,c_1326]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5643,plain,
% 7.73/1.50      ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2429,c_3502]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5646,plain,
% 7.73/1.50      ( k5_relat_1(sK3,k6_partfun1(sK0)) = sK3 ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_5643,c_2438]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1300,plain,
% 7.73/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4211,plain,
% 7.73/1.50      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 7.73/1.50      | v1_funct_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X1) != iProver_top
% 7.73/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1324,c_1328]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11388,plain,
% 7.73/1.50      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.73/1.50      | v1_relat_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X1) != iProver_top
% 7.73/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1300,c_4211]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11655,plain,
% 7.73/1.50      ( v1_relat_1(X1) != iProver_top
% 7.73/1.50      | v1_relat_1(X0) != iProver_top
% 7.73/1.50      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_11388,c_2430]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11656,plain,
% 7.73/1.50      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.73/1.50      | v1_relat_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_11655]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11664,plain,
% 7.73/1.50      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2430,c_11656]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_26,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.50      | ~ v2_funct_1(X0)
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | k2_relset_1(X1,X2,X0) != X2
% 7.73/1.50      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 7.73/1.50      | k1_xboole_0 = X2 ),
% 7.73/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1308,plain,
% 7.73/1.50      ( k2_relset_1(X0,X1,X2) != X1
% 7.73/1.50      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 7.73/1.50      | k1_xboole_0 = X1
% 7.73/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.73/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.73/1.50      | v2_funct_1(X2) != iProver_top
% 7.73/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4167,plain,
% 7.73/1.50      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.73/1.50      | sK1 = k1_xboole_0
% 7.73/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.73/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.73/1.50      | v2_funct_1(sK2) != iProver_top
% 7.73/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_33,c_1308]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_31,negated_conjecture,
% 7.73/1.50      ( v2_funct_1(sK2) ),
% 7.73/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_29,negated_conjecture,
% 7.73/1.50      ( k1_xboole_0 != sK1 ),
% 7.73/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1384,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,X1,sK1)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.73/1.50      | ~ v2_funct_1(X0)
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | k2_relset_1(X1,sK1,X0) != sK1
% 7.73/1.50      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 7.73/1.50      | k1_xboole_0 = sK1 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_26]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1482,plain,
% 7.73/1.50      ( ~ v1_funct_2(sK2,X0,sK1)
% 7.73/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 7.73/1.50      | ~ v2_funct_1(sK2)
% 7.73/1.50      | ~ v1_funct_1(sK2)
% 7.73/1.50      | k2_relset_1(X0,sK1,sK2) != sK1
% 7.73/1.50      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.73/1.50      | k1_xboole_0 = sK1 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_1384]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1640,plain,
% 7.73/1.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.73/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.73/1.50      | ~ v2_funct_1(sK2)
% 7.73/1.50      | ~ v1_funct_1(sK2)
% 7.73/1.50      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.73/1.50      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.73/1.50      | k1_xboole_0 = sK1 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_1482]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4228,plain,
% 7.73/1.50      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_4167,c_39,c_38,c_37,c_33,c_31,c_29,c_1640]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11668,plain,
% 7.73/1.50      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_11664,c_4228]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11691,plain,
% 7.73/1.50      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k2_funct_1(X0))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(X0))
% 7.73/1.50      | v1_funct_1(X0) != iProver_top
% 7.73/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1324,c_11668]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_12612,plain,
% 7.73/1.50      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k2_funct_1(sK2))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))
% 7.73/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1300,c_11691]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3495,plain,
% 7.73/1.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.73/1.50      | sK1 = k1_xboole_0
% 7.73/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.73/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.73/1.50      | v2_funct_1(sK2) != iProver_top
% 7.73/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_33,c_1307]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1385,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,X1,sK1)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.73/1.50      | ~ v2_funct_1(X0)
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | k2_relset_1(X1,sK1,X0) != sK1
% 7.73/1.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.73/1.50      | k1_xboole_0 = sK1 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_27]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1508,plain,
% 7.73/1.50      ( ~ v1_funct_2(sK2,X0,sK1)
% 7.73/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 7.73/1.50      | ~ v2_funct_1(sK2)
% 7.73/1.50      | ~ v1_funct_1(sK2)
% 7.73/1.50      | k2_relset_1(X0,sK1,sK2) != sK1
% 7.73/1.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 7.73/1.50      | k1_xboole_0 = sK1 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_1385]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1653,plain,
% 7.73/1.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.73/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.73/1.50      | ~ v2_funct_1(sK2)
% 7.73/1.50      | ~ v1_funct_1(sK2)
% 7.73/1.50      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.73/1.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.73/1.50      | k1_xboole_0 = sK1 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_1508]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3661,plain,
% 7.73/1.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_3495,c_39,c_38,c_37,c_33,c_31,c_29,c_1653]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5579,plain,
% 7.73/1.50      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) = k2_funct_1(sK2)
% 7.73/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1300,c_2482]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1306,plain,
% 7.73/1.50      ( v2_funct_1(sK2) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3608,plain,
% 7.73/1.50      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 7.73/1.50      | v1_funct_1(sK2) != iProver_top
% 7.73/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_1306,c_1320]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3609,plain,
% 7.73/1.50      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 7.73/1.50      | v1_funct_1(sK2) != iProver_top
% 7.73/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_3608,c_2437]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3729,plain,
% 7.73/1.50      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_3609,c_40,c_2430]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5582,plain,
% 7.73/1.50      ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2)
% 7.73/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_5579,c_3729]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_5800,plain,
% 7.73/1.50      ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_5582,c_2430]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11693,plain,
% 7.73/1.50      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2429,c_11668]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11700,plain,
% 7.73/1.50      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_11693,c_5081]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_12617,plain,
% 7.73/1.50      ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2)
% 7.73/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_12612,c_3661,c_5800,c_11700]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_12657,plain,
% 7.73/1.50      ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_12617,c_2430]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_17860,plain,
% 7.73/1.50      ( k2_funct_1(sK2) = sK3 ),
% 7.73/1.50      inference(light_normalisation,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_17852,c_5081,c_5646,c_12657]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_28,negated_conjecture,
% 7.73/1.50      ( k2_funct_1(sK2) != sK3 ),
% 7.73/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(contradiction,plain,
% 7.73/1.50      ( $false ),
% 7.73/1.50      inference(minisat,[status(thm)],[c_17860,c_28]) ).
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  ------                               Statistics
% 7.73/1.50  
% 7.73/1.50  ------ General
% 7.73/1.50  
% 7.73/1.50  abstr_ref_over_cycles:                  0
% 7.73/1.50  abstr_ref_under_cycles:                 0
% 7.73/1.50  gc_basic_clause_elim:                   0
% 7.73/1.50  forced_gc_time:                         0
% 7.73/1.50  parsing_time:                           0.013
% 7.73/1.50  unif_index_cands_time:                  0.
% 7.73/1.50  unif_index_add_time:                    0.
% 7.73/1.50  orderings_time:                         0.
% 7.73/1.50  out_proof_time:                         0.019
% 7.73/1.50  total_time:                             0.755
% 7.73/1.50  num_of_symbols:                         52
% 7.73/1.50  num_of_terms:                           31218
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing
% 7.73/1.50  
% 7.73/1.50  num_of_splits:                          0
% 7.73/1.50  num_of_split_atoms:                     0
% 7.73/1.50  num_of_reused_defs:                     0
% 7.73/1.50  num_eq_ax_congr_red:                    3
% 7.73/1.50  num_of_sem_filtered_clauses:            1
% 7.73/1.50  num_of_subtypes:                        0
% 7.73/1.50  monotx_restored_types:                  0
% 7.73/1.50  sat_num_of_epr_types:                   0
% 7.73/1.50  sat_num_of_non_cyclic_types:            0
% 7.73/1.50  sat_guarded_non_collapsed_types:        0
% 7.73/1.50  num_pure_diseq_elim:                    0
% 7.73/1.50  simp_replaced_by:                       0
% 7.73/1.50  res_preprocessed:                       188
% 7.73/1.50  prep_upred:                             0
% 7.73/1.50  prep_unflattend:                        12
% 7.73/1.50  smt_new_axioms:                         0
% 7.73/1.50  pred_elim_cands:                        6
% 7.73/1.50  pred_elim:                              1
% 7.73/1.50  pred_elim_cl:                           1
% 7.73/1.50  pred_elim_cycles:                       3
% 7.73/1.50  merged_defs:                            0
% 7.73/1.50  merged_defs_ncl:                        0
% 7.73/1.50  bin_hyper_res:                          0
% 7.73/1.50  prep_cycles:                            4
% 7.73/1.50  pred_elim_time:                         0.004
% 7.73/1.50  splitting_time:                         0.
% 7.73/1.50  sem_filter_time:                        0.
% 7.73/1.50  monotx_time:                            0.001
% 7.73/1.50  subtype_inf_time:                       0.
% 7.73/1.50  
% 7.73/1.50  ------ Problem properties
% 7.73/1.50  
% 7.73/1.50  clauses:                                38
% 7.73/1.50  conjectures:                            11
% 7.73/1.50  epr:                                    9
% 7.73/1.50  horn:                                   34
% 7.73/1.50  ground:                                 12
% 7.73/1.50  unary:                                  15
% 7.73/1.50  binary:                                 4
% 7.73/1.50  lits:                                   134
% 7.73/1.50  lits_eq:                                30
% 7.73/1.50  fd_pure:                                0
% 7.73/1.50  fd_pseudo:                              0
% 7.73/1.50  fd_cond:                                4
% 7.73/1.50  fd_pseudo_cond:                         1
% 7.73/1.50  ac_symbols:                             0
% 7.73/1.50  
% 7.73/1.50  ------ Propositional Solver
% 7.73/1.50  
% 7.73/1.50  prop_solver_calls:                      31
% 7.73/1.50  prop_fast_solver_calls:                 2240
% 7.73/1.50  smt_solver_calls:                       0
% 7.73/1.50  smt_fast_solver_calls:                  0
% 7.73/1.50  prop_num_of_clauses:                    9551
% 7.73/1.50  prop_preprocess_simplified:             16835
% 7.73/1.50  prop_fo_subsumed:                       166
% 7.73/1.50  prop_solver_time:                       0.
% 7.73/1.50  smt_solver_time:                        0.
% 7.73/1.50  smt_fast_solver_time:                   0.
% 7.73/1.50  prop_fast_solver_time:                  0.
% 7.73/1.50  prop_unsat_core_time:                   0.001
% 7.73/1.50  
% 7.73/1.50  ------ QBF
% 7.73/1.50  
% 7.73/1.50  qbf_q_res:                              0
% 7.73/1.50  qbf_num_tautologies:                    0
% 7.73/1.50  qbf_prep_cycles:                        0
% 7.73/1.50  
% 7.73/1.50  ------ BMC1
% 7.73/1.50  
% 7.73/1.50  bmc1_current_bound:                     -1
% 7.73/1.50  bmc1_last_solved_bound:                 -1
% 7.73/1.50  bmc1_unsat_core_size:                   -1
% 7.73/1.50  bmc1_unsat_core_parents_size:           -1
% 7.73/1.50  bmc1_merge_next_fun:                    0
% 7.73/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.73/1.50  
% 7.73/1.50  ------ Instantiation
% 7.73/1.50  
% 7.73/1.50  inst_num_of_clauses:                    2256
% 7.73/1.50  inst_num_in_passive:                    663
% 7.73/1.50  inst_num_in_active:                     1491
% 7.73/1.50  inst_num_in_unprocessed:                103
% 7.73/1.50  inst_num_of_loops:                      1630
% 7.73/1.50  inst_num_of_learning_restarts:          0
% 7.73/1.50  inst_num_moves_active_passive:          136
% 7.73/1.50  inst_lit_activity:                      0
% 7.73/1.50  inst_lit_activity_moves:                1
% 7.73/1.50  inst_num_tautologies:                   0
% 7.73/1.50  inst_num_prop_implied:                  0
% 7.73/1.50  inst_num_existing_simplified:           0
% 7.73/1.50  inst_num_eq_res_simplified:             0
% 7.73/1.50  inst_num_child_elim:                    0
% 7.73/1.50  inst_num_of_dismatching_blockings:      707
% 7.73/1.50  inst_num_of_non_proper_insts:           2560
% 7.73/1.50  inst_num_of_duplicates:                 0
% 7.73/1.50  inst_inst_num_from_inst_to_res:         0
% 7.73/1.50  inst_dismatching_checking_time:         0.
% 7.73/1.50  
% 7.73/1.50  ------ Resolution
% 7.73/1.50  
% 7.73/1.50  res_num_of_clauses:                     0
% 7.73/1.50  res_num_in_passive:                     0
% 7.73/1.50  res_num_in_active:                      0
% 7.73/1.50  res_num_of_loops:                       192
% 7.73/1.50  res_forward_subset_subsumed:            152
% 7.73/1.50  res_backward_subset_subsumed:           2
% 7.73/1.50  res_forward_subsumed:                   0
% 7.73/1.50  res_backward_subsumed:                  0
% 7.73/1.50  res_forward_subsumption_resolution:     2
% 7.73/1.50  res_backward_subsumption_resolution:    0
% 7.73/1.50  res_clause_to_clause_subsumption:       1628
% 7.73/1.50  res_orphan_elimination:                 0
% 7.73/1.50  res_tautology_del:                      84
% 7.73/1.50  res_num_eq_res_simplified:              1
% 7.73/1.50  res_num_sel_changes:                    0
% 7.73/1.50  res_moves_from_active_to_pass:          0
% 7.73/1.50  
% 7.73/1.50  ------ Superposition
% 7.73/1.50  
% 7.73/1.50  sup_time_total:                         0.
% 7.73/1.50  sup_time_generating:                    0.
% 7.73/1.50  sup_time_sim_full:                      0.
% 7.73/1.50  sup_time_sim_immed:                     0.
% 7.73/1.50  
% 7.73/1.50  sup_num_of_clauses:                     720
% 7.73/1.50  sup_num_in_active:                      313
% 7.73/1.50  sup_num_in_passive:                     407
% 7.73/1.50  sup_num_of_loops:                       324
% 7.73/1.50  sup_fw_superposition:                   627
% 7.73/1.50  sup_bw_superposition:                   154
% 7.73/1.50  sup_immediate_simplified:               233
% 7.73/1.50  sup_given_eliminated:                   0
% 7.73/1.50  comparisons_done:                       0
% 7.73/1.50  comparisons_avoided:                    0
% 7.73/1.50  
% 7.73/1.50  ------ Simplifications
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  sim_fw_subset_subsumed:                 14
% 7.73/1.50  sim_bw_subset_subsumed:                 14
% 7.73/1.50  sim_fw_subsumed:                        17
% 7.73/1.50  sim_bw_subsumed:                        4
% 7.73/1.50  sim_fw_subsumption_res:                 0
% 7.73/1.50  sim_bw_subsumption_res:                 0
% 7.73/1.50  sim_tautology_del:                      2
% 7.73/1.50  sim_eq_tautology_del:                   25
% 7.73/1.50  sim_eq_res_simp:                        0
% 7.73/1.50  sim_fw_demodulated:                     18
% 7.73/1.50  sim_bw_demodulated:                     11
% 7.73/1.50  sim_light_normalised:                   207
% 7.73/1.50  sim_joinable_taut:                      0
% 7.73/1.50  sim_joinable_simp:                      0
% 7.73/1.50  sim_ac_normalised:                      0
% 7.73/1.50  sim_smt_subsumption:                    0
% 7.73/1.50  
%------------------------------------------------------------------------------
