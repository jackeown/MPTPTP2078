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
% DateTime   : Thu Dec  3 12:03:30 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 461 expanded)
%              Number of clauses        :   92 ( 150 expanded)
%              Number of leaves         :   14 ( 111 expanded)
%              Depth                    :   19
%              Number of atoms          :  536 (3858 expanded)
%              Number of equality atoms :  258 (1444 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f33,f32])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f61,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_581,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_944,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_583,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_942,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ m1_subset_1(X3_49,k1_zfmisc_1(k2_zfmisc_1(X4_49,X5_49)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X3_49)
    | k1_partfun1(X4_49,X5_49,X1_49,X2_49,X3_49,X0_49) = k5_relat_1(X3_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_941,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X4_49,X5_49) = k5_relat_1(X4_49,X5_49)
    | m1_subset_1(X5_49,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | m1_subset_1(X4_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X5_49) != iProver_top
    | v1_funct_1(X4_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_1967,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X2_49,sK3) = k5_relat_1(X2_49,sK3)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X2_49) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_942,c_941])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2189,plain,
    ( v1_funct_1(X2_49) != iProver_top
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK1,sK0,X2_49,sK3) = k5_relat_1(X2_49,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1967,c_32])).

cnf(c_2190,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X2_49,sK3) = k5_relat_1(X2_49,sK3)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X2_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_2189])).

cnf(c_2199,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_944,c_2190])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_29,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2235,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2199,c_29])).

cnf(c_6,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_21,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_320,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_328,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_320,c_15])).

cnf(c_578,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_328])).

cnf(c_947,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_2238,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2235,c_947])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ m1_subset_1(X3_49,k1_zfmisc_1(k2_zfmisc_1(X4_49,X5_49)))
    | m1_subset_1(k1_partfun1(X4_49,X5_49,X1_49,X2_49,X3_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X4_49,X2_49)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X3_49) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_938,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
    | m1_subset_1(X3_49,k1_zfmisc_1(k2_zfmisc_1(X4_49,X5_49))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_49,X5_49,X1_49,X2_49,X3_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X4_49,X2_49))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(X3_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_2305,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2235,c_938])).

cnf(c_2578,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2238,c_29,c_31,c_32,c_34,c_2305])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | k2_relset_1(X1_49,X2_49,X0_49) = k2_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_937,plain,
    ( k2_relset_1(X0_49,X1_49,X2_49) = k2_relat_1(X2_49)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_1909,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_944,c_937])).

cnf(c_22,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_584,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1914,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1909,c_584])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k2_funct_1(X1) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_280,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k2_funct_1(X1) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_281,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0)
    | k2_funct_1(sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_285,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0)
    | k2_funct_1(sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_281,c_28])).

cnf(c_579,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,X0_49) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0_49)
    | k2_funct_1(sK2) = X0_49 ),
    inference(subtyping,[status(esa)],[c_285])).

cnf(c_946,plain,
    ( k5_relat_1(sK2,X0_49) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0_49)
    | k2_funct_1(sK2) = X0_49
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_647,plain,
    ( k5_relat_1(sK2,X0_49) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0_49)
    | k2_funct_1(sK2) = X0_49
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_595,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
    | ~ v1_relat_1(X1_49)
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1103,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | v1_relat_1(X0_49)
    | ~ v1_relat_1(k2_zfmisc_1(X1_49,X2_49)) ),
    inference(instantiation,[status(thm)],[c_595])).

cnf(c_1264,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_1265,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1264])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_594,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1290,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_1291,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1290])).

cnf(c_1681,plain,
    ( v1_relat_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | k2_funct_1(sK2) = X0_49
    | k2_relat_1(sK2) != k1_relat_1(X0_49)
    | k5_relat_1(sK2,X0_49) != k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_946,c_31,c_647,c_1265,c_1291])).

cnf(c_1682,plain,
    ( k5_relat_1(sK2,X0_49) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0_49)
    | k2_funct_1(sK2) = X0_49
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_1681])).

cnf(c_1920,plain,
    ( k5_relat_1(sK2,X0_49) != k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(X0_49) != sK1
    | k2_funct_1(sK2) = X0_49
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1914,c_1682])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_593,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | k1_relset_1(X1_49,X2_49,X0_49) = k1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_936,plain,
    ( k1_relset_1(X0_49,X1_49,X2_49) = k1_relat_1(X2_49)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_1844,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_944,c_936])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_420,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_422,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_26,c_18])).

cnf(c_572,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_422])).

cnf(c_1849,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1844,c_572])).

cnf(c_2114,plain,
    ( k5_relat_1(sK2,X0_49) != k6_partfun1(sK0)
    | k1_relat_1(X0_49) != sK1
    | k2_funct_1(sK2) = X0_49
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1920,c_1849])).

cnf(c_2582,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2578,c_2114])).

cnf(c_1843,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_942,c_936])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X2
    | sK1 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_412,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_414,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_412,c_23,c_19])).

cnf(c_573,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(subtyping,[status(esa)],[c_414])).

cnf(c_1852,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1843,c_573])).

cnf(c_2583,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2582,c_1852])).

cnf(c_2584,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2583])).

cnf(c_1287,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_1288,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1287])).

cnf(c_1261,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_1262,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1261])).

cnf(c_17,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_587,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2584,c_1288,c_1262,c_587,c_34,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.86/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.00  
% 2.86/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.86/1.00  
% 2.86/1.00  ------  iProver source info
% 2.86/1.00  
% 2.86/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.86/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.86/1.00  git: non_committed_changes: false
% 2.86/1.00  git: last_make_outside_of_git: false
% 2.86/1.00  
% 2.86/1.00  ------ 
% 2.86/1.00  
% 2.86/1.00  ------ Input Options
% 2.86/1.00  
% 2.86/1.00  --out_options                           all
% 2.86/1.00  --tptp_safe_out                         true
% 2.86/1.00  --problem_path                          ""
% 2.86/1.00  --include_path                          ""
% 2.86/1.00  --clausifier                            res/vclausify_rel
% 2.86/1.00  --clausifier_options                    --mode clausify
% 2.86/1.00  --stdin                                 false
% 2.86/1.00  --stats_out                             all
% 2.86/1.00  
% 2.86/1.00  ------ General Options
% 2.86/1.00  
% 2.86/1.00  --fof                                   false
% 2.86/1.00  --time_out_real                         305.
% 2.86/1.00  --time_out_virtual                      -1.
% 2.86/1.00  --symbol_type_check                     false
% 2.86/1.00  --clausify_out                          false
% 2.86/1.00  --sig_cnt_out                           false
% 2.86/1.00  --trig_cnt_out                          false
% 2.86/1.00  --trig_cnt_out_tolerance                1.
% 2.86/1.00  --trig_cnt_out_sk_spl                   false
% 2.86/1.00  --abstr_cl_out                          false
% 2.86/1.00  
% 2.86/1.00  ------ Global Options
% 2.86/1.00  
% 2.86/1.00  --schedule                              default
% 2.86/1.00  --add_important_lit                     false
% 2.86/1.00  --prop_solver_per_cl                    1000
% 2.86/1.00  --min_unsat_core                        false
% 2.86/1.00  --soft_assumptions                      false
% 2.86/1.00  --soft_lemma_size                       3
% 2.86/1.00  --prop_impl_unit_size                   0
% 2.86/1.00  --prop_impl_unit                        []
% 2.86/1.00  --share_sel_clauses                     true
% 2.86/1.00  --reset_solvers                         false
% 2.86/1.00  --bc_imp_inh                            [conj_cone]
% 2.86/1.00  --conj_cone_tolerance                   3.
% 2.86/1.00  --extra_neg_conj                        none
% 2.86/1.00  --large_theory_mode                     true
% 2.86/1.00  --prolific_symb_bound                   200
% 2.86/1.00  --lt_threshold                          2000
% 2.86/1.00  --clause_weak_htbl                      true
% 2.86/1.00  --gc_record_bc_elim                     false
% 2.86/1.00  
% 2.86/1.00  ------ Preprocessing Options
% 2.86/1.00  
% 2.86/1.00  --preprocessing_flag                    true
% 2.86/1.00  --time_out_prep_mult                    0.1
% 2.86/1.00  --splitting_mode                        input
% 2.86/1.00  --splitting_grd                         true
% 2.86/1.00  --splitting_cvd                         false
% 2.86/1.00  --splitting_cvd_svl                     false
% 2.86/1.00  --splitting_nvd                         32
% 2.86/1.00  --sub_typing                            true
% 2.86/1.00  --prep_gs_sim                           true
% 2.86/1.00  --prep_unflatten                        true
% 2.86/1.00  --prep_res_sim                          true
% 2.86/1.00  --prep_upred                            true
% 2.86/1.00  --prep_sem_filter                       exhaustive
% 2.86/1.00  --prep_sem_filter_out                   false
% 2.86/1.00  --pred_elim                             true
% 2.86/1.00  --res_sim_input                         true
% 2.86/1.00  --eq_ax_congr_red                       true
% 2.86/1.00  --pure_diseq_elim                       true
% 2.86/1.00  --brand_transform                       false
% 2.86/1.00  --non_eq_to_eq                          false
% 2.86/1.00  --prep_def_merge                        true
% 2.86/1.00  --prep_def_merge_prop_impl              false
% 2.86/1.00  --prep_def_merge_mbd                    true
% 2.86/1.00  --prep_def_merge_tr_red                 false
% 2.86/1.00  --prep_def_merge_tr_cl                  false
% 2.86/1.00  --smt_preprocessing                     true
% 2.86/1.00  --smt_ac_axioms                         fast
% 2.86/1.00  --preprocessed_out                      false
% 2.86/1.00  --preprocessed_stats                    false
% 2.86/1.00  
% 2.86/1.00  ------ Abstraction refinement Options
% 2.86/1.00  
% 2.86/1.00  --abstr_ref                             []
% 2.86/1.00  --abstr_ref_prep                        false
% 2.86/1.00  --abstr_ref_until_sat                   false
% 2.86/1.00  --abstr_ref_sig_restrict                funpre
% 2.86/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/1.00  --abstr_ref_under                       []
% 2.86/1.00  
% 2.86/1.00  ------ SAT Options
% 2.86/1.00  
% 2.86/1.00  --sat_mode                              false
% 2.86/1.00  --sat_fm_restart_options                ""
% 2.86/1.00  --sat_gr_def                            false
% 2.86/1.00  --sat_epr_types                         true
% 2.86/1.00  --sat_non_cyclic_types                  false
% 2.86/1.00  --sat_finite_models                     false
% 2.86/1.00  --sat_fm_lemmas                         false
% 2.86/1.00  --sat_fm_prep                           false
% 2.86/1.00  --sat_fm_uc_incr                        true
% 2.86/1.00  --sat_out_model                         small
% 2.86/1.00  --sat_out_clauses                       false
% 2.86/1.00  
% 2.86/1.00  ------ QBF Options
% 2.86/1.00  
% 2.86/1.00  --qbf_mode                              false
% 2.86/1.00  --qbf_elim_univ                         false
% 2.86/1.00  --qbf_dom_inst                          none
% 2.86/1.00  --qbf_dom_pre_inst                      false
% 2.86/1.00  --qbf_sk_in                             false
% 2.86/1.00  --qbf_pred_elim                         true
% 2.86/1.00  --qbf_split                             512
% 2.86/1.00  
% 2.86/1.00  ------ BMC1 Options
% 2.86/1.00  
% 2.86/1.00  --bmc1_incremental                      false
% 2.86/1.00  --bmc1_axioms                           reachable_all
% 2.86/1.00  --bmc1_min_bound                        0
% 2.86/1.00  --bmc1_max_bound                        -1
% 2.86/1.00  --bmc1_max_bound_default                -1
% 2.86/1.00  --bmc1_symbol_reachability              true
% 2.86/1.00  --bmc1_property_lemmas                  false
% 2.86/1.00  --bmc1_k_induction                      false
% 2.86/1.00  --bmc1_non_equiv_states                 false
% 2.86/1.00  --bmc1_deadlock                         false
% 2.86/1.00  --bmc1_ucm                              false
% 2.86/1.00  --bmc1_add_unsat_core                   none
% 2.86/1.00  --bmc1_unsat_core_children              false
% 2.86/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/1.00  --bmc1_out_stat                         full
% 2.86/1.00  --bmc1_ground_init                      false
% 2.86/1.00  --bmc1_pre_inst_next_state              false
% 2.86/1.00  --bmc1_pre_inst_state                   false
% 2.86/1.00  --bmc1_pre_inst_reach_state             false
% 2.86/1.00  --bmc1_out_unsat_core                   false
% 2.86/1.00  --bmc1_aig_witness_out                  false
% 2.86/1.00  --bmc1_verbose                          false
% 2.86/1.00  --bmc1_dump_clauses_tptp                false
% 2.86/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.86/1.00  --bmc1_dump_file                        -
% 2.86/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.86/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.86/1.00  --bmc1_ucm_extend_mode                  1
% 2.86/1.00  --bmc1_ucm_init_mode                    2
% 2.86/1.00  --bmc1_ucm_cone_mode                    none
% 2.86/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.86/1.00  --bmc1_ucm_relax_model                  4
% 2.86/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.86/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/1.00  --bmc1_ucm_layered_model                none
% 2.86/1.00  --bmc1_ucm_max_lemma_size               10
% 2.86/1.00  
% 2.86/1.00  ------ AIG Options
% 2.86/1.00  
% 2.86/1.00  --aig_mode                              false
% 2.86/1.00  
% 2.86/1.00  ------ Instantiation Options
% 2.86/1.00  
% 2.86/1.00  --instantiation_flag                    true
% 2.86/1.00  --inst_sos_flag                         false
% 2.86/1.00  --inst_sos_phase                        true
% 2.86/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/1.00  --inst_lit_sel_side                     num_symb
% 2.86/1.00  --inst_solver_per_active                1400
% 2.86/1.00  --inst_solver_calls_frac                1.
% 2.86/1.00  --inst_passive_queue_type               priority_queues
% 2.86/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/1.00  --inst_passive_queues_freq              [25;2]
% 2.86/1.00  --inst_dismatching                      true
% 2.86/1.00  --inst_eager_unprocessed_to_passive     true
% 2.86/1.00  --inst_prop_sim_given                   true
% 2.86/1.00  --inst_prop_sim_new                     false
% 2.86/1.00  --inst_subs_new                         false
% 2.86/1.00  --inst_eq_res_simp                      false
% 2.86/1.00  --inst_subs_given                       false
% 2.86/1.00  --inst_orphan_elimination               true
% 2.86/1.00  --inst_learning_loop_flag               true
% 2.86/1.00  --inst_learning_start                   3000
% 2.86/1.00  --inst_learning_factor                  2
% 2.86/1.00  --inst_start_prop_sim_after_learn       3
% 2.86/1.00  --inst_sel_renew                        solver
% 2.86/1.00  --inst_lit_activity_flag                true
% 2.86/1.00  --inst_restr_to_given                   false
% 2.86/1.00  --inst_activity_threshold               500
% 2.86/1.00  --inst_out_proof                        true
% 2.86/1.00  
% 2.86/1.00  ------ Resolution Options
% 2.86/1.00  
% 2.86/1.00  --resolution_flag                       true
% 2.86/1.00  --res_lit_sel                           adaptive
% 2.86/1.00  --res_lit_sel_side                      none
% 2.86/1.00  --res_ordering                          kbo
% 2.86/1.00  --res_to_prop_solver                    active
% 2.86/1.00  --res_prop_simpl_new                    false
% 2.86/1.00  --res_prop_simpl_given                  true
% 2.86/1.00  --res_passive_queue_type                priority_queues
% 2.86/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/1.00  --res_passive_queues_freq               [15;5]
% 2.86/1.00  --res_forward_subs                      full
% 2.86/1.00  --res_backward_subs                     full
% 2.86/1.00  --res_forward_subs_resolution           true
% 2.86/1.00  --res_backward_subs_resolution          true
% 2.86/1.00  --res_orphan_elimination                true
% 2.86/1.00  --res_time_limit                        2.
% 2.86/1.00  --res_out_proof                         true
% 2.86/1.00  
% 2.86/1.00  ------ Superposition Options
% 2.86/1.00  
% 2.86/1.00  --superposition_flag                    true
% 2.86/1.00  --sup_passive_queue_type                priority_queues
% 2.86/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.86/1.00  --demod_completeness_check              fast
% 2.86/1.00  --demod_use_ground                      true
% 2.86/1.00  --sup_to_prop_solver                    passive
% 2.86/1.00  --sup_prop_simpl_new                    true
% 2.86/1.00  --sup_prop_simpl_given                  true
% 2.86/1.00  --sup_fun_splitting                     false
% 2.86/1.00  --sup_smt_interval                      50000
% 2.86/1.00  
% 2.86/1.00  ------ Superposition Simplification Setup
% 2.86/1.00  
% 2.86/1.00  --sup_indices_passive                   []
% 2.86/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.86/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.00  --sup_full_bw                           [BwDemod]
% 2.86/1.00  --sup_immed_triv                        [TrivRules]
% 2.86/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.00  --sup_immed_bw_main                     []
% 2.86/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/1.00  
% 2.86/1.00  ------ Combination Options
% 2.86/1.00  
% 2.86/1.00  --comb_res_mult                         3
% 2.86/1.00  --comb_sup_mult                         2
% 2.86/1.00  --comb_inst_mult                        10
% 2.86/1.00  
% 2.86/1.00  ------ Debug Options
% 2.86/1.00  
% 2.86/1.00  --dbg_backtrace                         false
% 2.86/1.00  --dbg_dump_prop_clauses                 false
% 2.86/1.00  --dbg_dump_prop_clauses_file            -
% 2.86/1.00  --dbg_out_stat                          false
% 2.86/1.00  ------ Parsing...
% 2.86/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.86/1.00  
% 2.86/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.86/1.00  
% 2.86/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.86/1.00  
% 2.86/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.86/1.00  ------ Proving...
% 2.86/1.00  ------ Problem Properties 
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  clauses                                 24
% 2.86/1.00  conjectures                             8
% 2.86/1.00  EPR                                     4
% 2.86/1.00  Horn                                    24
% 2.86/1.00  unary                                   12
% 2.86/1.00  binary                                  3
% 2.86/1.00  lits                                    54
% 2.86/1.00  lits eq                                 21
% 2.86/1.00  fd_pure                                 0
% 2.86/1.00  fd_pseudo                               0
% 2.86/1.00  fd_cond                                 1
% 2.86/1.00  fd_pseudo_cond                          0
% 2.86/1.00  AC symbols                              0
% 2.86/1.00  
% 2.86/1.00  ------ Schedule dynamic 5 is on 
% 2.86/1.00  
% 2.86/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  ------ 
% 2.86/1.00  Current options:
% 2.86/1.00  ------ 
% 2.86/1.00  
% 2.86/1.00  ------ Input Options
% 2.86/1.00  
% 2.86/1.00  --out_options                           all
% 2.86/1.00  --tptp_safe_out                         true
% 2.86/1.00  --problem_path                          ""
% 2.86/1.00  --include_path                          ""
% 2.86/1.00  --clausifier                            res/vclausify_rel
% 2.86/1.00  --clausifier_options                    --mode clausify
% 2.86/1.00  --stdin                                 false
% 2.86/1.00  --stats_out                             all
% 2.86/1.00  
% 2.86/1.00  ------ General Options
% 2.86/1.00  
% 2.86/1.00  --fof                                   false
% 2.86/1.00  --time_out_real                         305.
% 2.86/1.00  --time_out_virtual                      -1.
% 2.86/1.00  --symbol_type_check                     false
% 2.86/1.00  --clausify_out                          false
% 2.86/1.00  --sig_cnt_out                           false
% 2.86/1.00  --trig_cnt_out                          false
% 2.86/1.00  --trig_cnt_out_tolerance                1.
% 2.86/1.00  --trig_cnt_out_sk_spl                   false
% 2.86/1.00  --abstr_cl_out                          false
% 2.86/1.00  
% 2.86/1.00  ------ Global Options
% 2.86/1.00  
% 2.86/1.00  --schedule                              default
% 2.86/1.00  --add_important_lit                     false
% 2.86/1.00  --prop_solver_per_cl                    1000
% 2.86/1.00  --min_unsat_core                        false
% 2.86/1.00  --soft_assumptions                      false
% 2.86/1.00  --soft_lemma_size                       3
% 2.86/1.00  --prop_impl_unit_size                   0
% 2.86/1.00  --prop_impl_unit                        []
% 2.86/1.00  --share_sel_clauses                     true
% 2.86/1.00  --reset_solvers                         false
% 2.86/1.00  --bc_imp_inh                            [conj_cone]
% 2.86/1.00  --conj_cone_tolerance                   3.
% 2.86/1.00  --extra_neg_conj                        none
% 2.86/1.00  --large_theory_mode                     true
% 2.86/1.00  --prolific_symb_bound                   200
% 2.86/1.00  --lt_threshold                          2000
% 2.86/1.00  --clause_weak_htbl                      true
% 2.86/1.00  --gc_record_bc_elim                     false
% 2.86/1.00  
% 2.86/1.00  ------ Preprocessing Options
% 2.86/1.00  
% 2.86/1.00  --preprocessing_flag                    true
% 2.86/1.00  --time_out_prep_mult                    0.1
% 2.86/1.00  --splitting_mode                        input
% 2.86/1.00  --splitting_grd                         true
% 2.86/1.00  --splitting_cvd                         false
% 2.86/1.00  --splitting_cvd_svl                     false
% 2.86/1.00  --splitting_nvd                         32
% 2.86/1.00  --sub_typing                            true
% 2.86/1.00  --prep_gs_sim                           true
% 2.86/1.00  --prep_unflatten                        true
% 2.86/1.00  --prep_res_sim                          true
% 2.86/1.00  --prep_upred                            true
% 2.86/1.00  --prep_sem_filter                       exhaustive
% 2.86/1.00  --prep_sem_filter_out                   false
% 2.86/1.00  --pred_elim                             true
% 2.86/1.00  --res_sim_input                         true
% 2.86/1.00  --eq_ax_congr_red                       true
% 2.86/1.00  --pure_diseq_elim                       true
% 2.86/1.00  --brand_transform                       false
% 2.86/1.00  --non_eq_to_eq                          false
% 2.86/1.00  --prep_def_merge                        true
% 2.86/1.00  --prep_def_merge_prop_impl              false
% 2.86/1.00  --prep_def_merge_mbd                    true
% 2.86/1.00  --prep_def_merge_tr_red                 false
% 2.86/1.00  --prep_def_merge_tr_cl                  false
% 2.86/1.00  --smt_preprocessing                     true
% 2.86/1.00  --smt_ac_axioms                         fast
% 2.86/1.00  --preprocessed_out                      false
% 2.86/1.00  --preprocessed_stats                    false
% 2.86/1.00  
% 2.86/1.00  ------ Abstraction refinement Options
% 2.86/1.00  
% 2.86/1.00  --abstr_ref                             []
% 2.86/1.00  --abstr_ref_prep                        false
% 2.86/1.00  --abstr_ref_until_sat                   false
% 2.86/1.00  --abstr_ref_sig_restrict                funpre
% 2.86/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/1.00  --abstr_ref_under                       []
% 2.86/1.00  
% 2.86/1.00  ------ SAT Options
% 2.86/1.00  
% 2.86/1.00  --sat_mode                              false
% 2.86/1.00  --sat_fm_restart_options                ""
% 2.86/1.00  --sat_gr_def                            false
% 2.86/1.00  --sat_epr_types                         true
% 2.86/1.00  --sat_non_cyclic_types                  false
% 2.86/1.00  --sat_finite_models                     false
% 2.86/1.00  --sat_fm_lemmas                         false
% 2.86/1.00  --sat_fm_prep                           false
% 2.86/1.00  --sat_fm_uc_incr                        true
% 2.86/1.00  --sat_out_model                         small
% 2.86/1.00  --sat_out_clauses                       false
% 2.86/1.00  
% 2.86/1.00  ------ QBF Options
% 2.86/1.00  
% 2.86/1.00  --qbf_mode                              false
% 2.86/1.00  --qbf_elim_univ                         false
% 2.86/1.00  --qbf_dom_inst                          none
% 2.86/1.00  --qbf_dom_pre_inst                      false
% 2.86/1.00  --qbf_sk_in                             false
% 2.86/1.00  --qbf_pred_elim                         true
% 2.86/1.00  --qbf_split                             512
% 2.86/1.00  
% 2.86/1.00  ------ BMC1 Options
% 2.86/1.00  
% 2.86/1.00  --bmc1_incremental                      false
% 2.86/1.00  --bmc1_axioms                           reachable_all
% 2.86/1.00  --bmc1_min_bound                        0
% 2.86/1.00  --bmc1_max_bound                        -1
% 2.86/1.00  --bmc1_max_bound_default                -1
% 2.86/1.00  --bmc1_symbol_reachability              true
% 2.86/1.00  --bmc1_property_lemmas                  false
% 2.86/1.00  --bmc1_k_induction                      false
% 2.86/1.00  --bmc1_non_equiv_states                 false
% 2.86/1.00  --bmc1_deadlock                         false
% 2.86/1.00  --bmc1_ucm                              false
% 2.86/1.00  --bmc1_add_unsat_core                   none
% 2.86/1.00  --bmc1_unsat_core_children              false
% 2.86/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/1.00  --bmc1_out_stat                         full
% 2.86/1.00  --bmc1_ground_init                      false
% 2.86/1.00  --bmc1_pre_inst_next_state              false
% 2.86/1.00  --bmc1_pre_inst_state                   false
% 2.86/1.00  --bmc1_pre_inst_reach_state             false
% 2.86/1.00  --bmc1_out_unsat_core                   false
% 2.86/1.00  --bmc1_aig_witness_out                  false
% 2.86/1.00  --bmc1_verbose                          false
% 2.86/1.00  --bmc1_dump_clauses_tptp                false
% 2.86/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.86/1.00  --bmc1_dump_file                        -
% 2.86/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.86/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.86/1.00  --bmc1_ucm_extend_mode                  1
% 2.86/1.00  --bmc1_ucm_init_mode                    2
% 2.86/1.00  --bmc1_ucm_cone_mode                    none
% 2.86/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.86/1.00  --bmc1_ucm_relax_model                  4
% 2.86/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.86/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/1.00  --bmc1_ucm_layered_model                none
% 2.86/1.00  --bmc1_ucm_max_lemma_size               10
% 2.86/1.00  
% 2.86/1.00  ------ AIG Options
% 2.86/1.00  
% 2.86/1.00  --aig_mode                              false
% 2.86/1.00  
% 2.86/1.00  ------ Instantiation Options
% 2.86/1.00  
% 2.86/1.00  --instantiation_flag                    true
% 2.86/1.00  --inst_sos_flag                         false
% 2.86/1.00  --inst_sos_phase                        true
% 2.86/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/1.00  --inst_lit_sel_side                     none
% 2.86/1.00  --inst_solver_per_active                1400
% 2.86/1.00  --inst_solver_calls_frac                1.
% 2.86/1.00  --inst_passive_queue_type               priority_queues
% 2.86/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/1.00  --inst_passive_queues_freq              [25;2]
% 2.86/1.00  --inst_dismatching                      true
% 2.86/1.00  --inst_eager_unprocessed_to_passive     true
% 2.86/1.00  --inst_prop_sim_given                   true
% 2.86/1.00  --inst_prop_sim_new                     false
% 2.86/1.00  --inst_subs_new                         false
% 2.86/1.00  --inst_eq_res_simp                      false
% 2.86/1.00  --inst_subs_given                       false
% 2.86/1.00  --inst_orphan_elimination               true
% 2.86/1.00  --inst_learning_loop_flag               true
% 2.86/1.00  --inst_learning_start                   3000
% 2.86/1.00  --inst_learning_factor                  2
% 2.86/1.00  --inst_start_prop_sim_after_learn       3
% 2.86/1.00  --inst_sel_renew                        solver
% 2.86/1.00  --inst_lit_activity_flag                true
% 2.86/1.00  --inst_restr_to_given                   false
% 2.86/1.00  --inst_activity_threshold               500
% 2.86/1.00  --inst_out_proof                        true
% 2.86/1.00  
% 2.86/1.00  ------ Resolution Options
% 2.86/1.00  
% 2.86/1.00  --resolution_flag                       false
% 2.86/1.00  --res_lit_sel                           adaptive
% 2.86/1.00  --res_lit_sel_side                      none
% 2.86/1.00  --res_ordering                          kbo
% 2.86/1.00  --res_to_prop_solver                    active
% 2.86/1.00  --res_prop_simpl_new                    false
% 2.86/1.00  --res_prop_simpl_given                  true
% 2.86/1.00  --res_passive_queue_type                priority_queues
% 2.86/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/1.00  --res_passive_queues_freq               [15;5]
% 2.86/1.00  --res_forward_subs                      full
% 2.86/1.00  --res_backward_subs                     full
% 2.86/1.00  --res_forward_subs_resolution           true
% 2.86/1.00  --res_backward_subs_resolution          true
% 2.86/1.00  --res_orphan_elimination                true
% 2.86/1.00  --res_time_limit                        2.
% 2.86/1.00  --res_out_proof                         true
% 2.86/1.00  
% 2.86/1.00  ------ Superposition Options
% 2.86/1.00  
% 2.86/1.00  --superposition_flag                    true
% 2.86/1.00  --sup_passive_queue_type                priority_queues
% 2.86/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.86/1.00  --demod_completeness_check              fast
% 2.86/1.00  --demod_use_ground                      true
% 2.86/1.00  --sup_to_prop_solver                    passive
% 2.86/1.00  --sup_prop_simpl_new                    true
% 2.86/1.00  --sup_prop_simpl_given                  true
% 2.86/1.00  --sup_fun_splitting                     false
% 2.86/1.00  --sup_smt_interval                      50000
% 2.86/1.00  
% 2.86/1.00  ------ Superposition Simplification Setup
% 2.86/1.00  
% 2.86/1.00  --sup_indices_passive                   []
% 2.86/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.86/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.00  --sup_full_bw                           [BwDemod]
% 2.86/1.00  --sup_immed_triv                        [TrivRules]
% 2.86/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.00  --sup_immed_bw_main                     []
% 2.86/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/1.00  
% 2.86/1.00  ------ Combination Options
% 2.86/1.00  
% 2.86/1.00  --comb_res_mult                         3
% 2.86/1.00  --comb_sup_mult                         2
% 2.86/1.00  --comb_inst_mult                        10
% 2.86/1.00  
% 2.86/1.00  ------ Debug Options
% 2.86/1.00  
% 2.86/1.00  --dbg_backtrace                         false
% 2.86/1.00  --dbg_dump_prop_clauses                 false
% 2.86/1.00  --dbg_dump_prop_clauses_file            -
% 2.86/1.00  --dbg_out_stat                          false
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  ------ Proving...
% 2.86/1.00  
% 2.86/1.00  
% 2.86/1.00  % SZS status Theorem for theBenchmark.p
% 2.86/1.00  
% 2.86/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.86/1.00  
% 2.86/1.00  fof(f12,conjecture,(
% 2.86/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.00  
% 2.86/1.00  fof(f13,negated_conjecture,(
% 2.86/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.86/1.00    inference(negated_conjecture,[],[f12])).
% 2.86/1.00  
% 2.86/1.00  fof(f28,plain,(
% 2.86/1.00    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.86/1.00    inference(ennf_transformation,[],[f13])).
% 2.86/1.00  
% 2.86/1.00  fof(f29,plain,(
% 2.86/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.86/1.00    inference(flattening,[],[f28])).
% 2.86/1.00  
% 2.86/1.00  fof(f33,plain,(
% 2.86/1.00    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.86/1.00    introduced(choice_axiom,[])).
% 2.86/1.00  
% 2.86/1.00  fof(f32,plain,(
% 2.86/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.86/1.00    introduced(choice_axiom,[])).
% 2.86/1.00  
% 2.86/1.00  fof(f34,plain,(
% 2.86/1.00    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.86/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f33,f32])).
% 2.86/1.00  
% 2.86/1.00  fof(f55,plain,(
% 2.86/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.86/1.00    inference(cnf_transformation,[],[f34])).
% 2.86/1.00  
% 2.86/1.00  fof(f58,plain,(
% 2.86/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.86/1.00    inference(cnf_transformation,[],[f34])).
% 2.86/1.00  
% 2.86/1.00  fof(f10,axiom,(
% 2.86/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f26,plain,(
% 2.86/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.86/1.01    inference(ennf_transformation,[],[f10])).
% 2.86/1.01  
% 2.86/1.01  fof(f27,plain,(
% 2.86/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.86/1.01    inference(flattening,[],[f26])).
% 2.86/1.01  
% 2.86/1.01  fof(f51,plain,(
% 2.86/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.86/1.01    inference(cnf_transformation,[],[f27])).
% 2.86/1.01  
% 2.86/1.01  fof(f56,plain,(
% 2.86/1.01    v1_funct_1(sK3)),
% 2.86/1.01    inference(cnf_transformation,[],[f34])).
% 2.86/1.01  
% 2.86/1.01  fof(f53,plain,(
% 2.86/1.01    v1_funct_1(sK2)),
% 2.86/1.01    inference(cnf_transformation,[],[f34])).
% 2.86/1.01  
% 2.86/1.01  fof(f6,axiom,(
% 2.86/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f20,plain,(
% 2.86/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.86/1.01    inference(ennf_transformation,[],[f6])).
% 2.86/1.01  
% 2.86/1.01  fof(f21,plain,(
% 2.86/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.01    inference(flattening,[],[f20])).
% 2.86/1.01  
% 2.86/1.01  fof(f30,plain,(
% 2.86/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.01    inference(nnf_transformation,[],[f21])).
% 2.86/1.01  
% 2.86/1.01  fof(f40,plain,(
% 2.86/1.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/1.01    inference(cnf_transformation,[],[f30])).
% 2.86/1.01  
% 2.86/1.01  fof(f60,plain,(
% 2.86/1.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.86/1.01    inference(cnf_transformation,[],[f34])).
% 2.86/1.01  
% 2.86/1.01  fof(f9,axiom,(
% 2.86/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f14,plain,(
% 2.86/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.86/1.01    inference(pure_predicate_removal,[],[f9])).
% 2.86/1.01  
% 2.86/1.01  fof(f50,plain,(
% 2.86/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.86/1.01    inference(cnf_transformation,[],[f14])).
% 2.86/1.01  
% 2.86/1.01  fof(f8,axiom,(
% 2.86/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f24,plain,(
% 2.86/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.86/1.01    inference(ennf_transformation,[],[f8])).
% 2.86/1.01  
% 2.86/1.01  fof(f25,plain,(
% 2.86/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.86/1.01    inference(flattening,[],[f24])).
% 2.86/1.01  
% 2.86/1.01  fof(f49,plain,(
% 2.86/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.86/1.01    inference(cnf_transformation,[],[f25])).
% 2.86/1.01  
% 2.86/1.01  fof(f5,axiom,(
% 2.86/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f19,plain,(
% 2.86/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.01    inference(ennf_transformation,[],[f5])).
% 2.86/1.01  
% 2.86/1.01  fof(f39,plain,(
% 2.86/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/1.01    inference(cnf_transformation,[],[f19])).
% 2.86/1.01  
% 2.86/1.01  fof(f59,plain,(
% 2.86/1.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.86/1.01    inference(cnf_transformation,[],[f34])).
% 2.86/1.01  
% 2.86/1.01  fof(f3,axiom,(
% 2.86/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f16,plain,(
% 2.86/1.01    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.86/1.01    inference(ennf_transformation,[],[f3])).
% 2.86/1.01  
% 2.86/1.01  fof(f17,plain,(
% 2.86/1.01    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.86/1.01    inference(flattening,[],[f16])).
% 2.86/1.01  
% 2.86/1.01  fof(f37,plain,(
% 2.86/1.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/1.01    inference(cnf_transformation,[],[f17])).
% 2.86/1.01  
% 2.86/1.01  fof(f11,axiom,(
% 2.86/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f52,plain,(
% 2.86/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.86/1.01    inference(cnf_transformation,[],[f11])).
% 2.86/1.01  
% 2.86/1.01  fof(f65,plain,(
% 2.86/1.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/1.01    inference(definition_unfolding,[],[f37,f52])).
% 2.86/1.01  
% 2.86/1.01  fof(f61,plain,(
% 2.86/1.01    v2_funct_1(sK2)),
% 2.86/1.01    inference(cnf_transformation,[],[f34])).
% 2.86/1.01  
% 2.86/1.01  fof(f1,axiom,(
% 2.86/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f15,plain,(
% 2.86/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.86/1.01    inference(ennf_transformation,[],[f1])).
% 2.86/1.01  
% 2.86/1.01  fof(f35,plain,(
% 2.86/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.86/1.01    inference(cnf_transformation,[],[f15])).
% 2.86/1.01  
% 2.86/1.01  fof(f2,axiom,(
% 2.86/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f36,plain,(
% 2.86/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.86/1.01    inference(cnf_transformation,[],[f2])).
% 2.86/1.01  
% 2.86/1.01  fof(f4,axiom,(
% 2.86/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f18,plain,(
% 2.86/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.01    inference(ennf_transformation,[],[f4])).
% 2.86/1.01  
% 2.86/1.01  fof(f38,plain,(
% 2.86/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/1.01    inference(cnf_transformation,[],[f18])).
% 2.86/1.01  
% 2.86/1.01  fof(f7,axiom,(
% 2.86/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f22,plain,(
% 2.86/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.01    inference(ennf_transformation,[],[f7])).
% 2.86/1.01  
% 2.86/1.01  fof(f23,plain,(
% 2.86/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.01    inference(flattening,[],[f22])).
% 2.86/1.01  
% 2.86/1.01  fof(f31,plain,(
% 2.86/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/1.01    inference(nnf_transformation,[],[f23])).
% 2.86/1.01  
% 2.86/1.01  fof(f42,plain,(
% 2.86/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/1.01    inference(cnf_transformation,[],[f31])).
% 2.86/1.01  
% 2.86/1.01  fof(f54,plain,(
% 2.86/1.01    v1_funct_2(sK2,sK0,sK1)),
% 2.86/1.01    inference(cnf_transformation,[],[f34])).
% 2.86/1.01  
% 2.86/1.01  fof(f63,plain,(
% 2.86/1.01    k1_xboole_0 != sK1),
% 2.86/1.01    inference(cnf_transformation,[],[f34])).
% 2.86/1.01  
% 2.86/1.01  fof(f57,plain,(
% 2.86/1.01    v1_funct_2(sK3,sK1,sK0)),
% 2.86/1.01    inference(cnf_transformation,[],[f34])).
% 2.86/1.01  
% 2.86/1.01  fof(f62,plain,(
% 2.86/1.01    k1_xboole_0 != sK0),
% 2.86/1.01    inference(cnf_transformation,[],[f34])).
% 2.86/1.01  
% 2.86/1.01  fof(f64,plain,(
% 2.86/1.01    k2_funct_1(sK2) != sK3),
% 2.86/1.01    inference(cnf_transformation,[],[f34])).
% 2.86/1.01  
% 2.86/1.01  cnf(c_26,negated_conjecture,
% 2.86/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.86/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_581,negated_conjecture,
% 2.86/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_26]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_944,plain,
% 2.86/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_581]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_23,negated_conjecture,
% 2.86/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.86/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_583,negated_conjecture,
% 2.86/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_23]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_942,plain,
% 2.86/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_16,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.86/1.01      | ~ v1_funct_1(X0)
% 2.86/1.01      | ~ v1_funct_1(X3)
% 2.86/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.86/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_588,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.86/1.01      | ~ m1_subset_1(X3_49,k1_zfmisc_1(k2_zfmisc_1(X4_49,X5_49)))
% 2.86/1.01      | ~ v1_funct_1(X0_49)
% 2.86/1.01      | ~ v1_funct_1(X3_49)
% 2.86/1.01      | k1_partfun1(X4_49,X5_49,X1_49,X2_49,X3_49,X0_49) = k5_relat_1(X3_49,X0_49) ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_941,plain,
% 2.86/1.01      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X4_49,X5_49) = k5_relat_1(X4_49,X5_49)
% 2.86/1.01      | m1_subset_1(X5_49,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 2.86/1.01      | m1_subset_1(X4_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 2.86/1.01      | v1_funct_1(X5_49) != iProver_top
% 2.86/1.01      | v1_funct_1(X4_49) != iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1967,plain,
% 2.86/1.01      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X2_49,sK3) = k5_relat_1(X2_49,sK3)
% 2.86/1.01      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 2.86/1.01      | v1_funct_1(X2_49) != iProver_top
% 2.86/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.86/1.01      inference(superposition,[status(thm)],[c_942,c_941]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_25,negated_conjecture,
% 2.86/1.01      ( v1_funct_1(sK3) ),
% 2.86/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_32,plain,
% 2.86/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_2189,plain,
% 2.86/1.01      ( v1_funct_1(X2_49) != iProver_top
% 2.86/1.01      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 2.86/1.01      | k1_partfun1(X0_49,X1_49,sK1,sK0,X2_49,sK3) = k5_relat_1(X2_49,sK3) ),
% 2.86/1.01      inference(global_propositional_subsumption,
% 2.86/1.01                [status(thm)],
% 2.86/1.01                [c_1967,c_32]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_2190,plain,
% 2.86/1.01      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X2_49,sK3) = k5_relat_1(X2_49,sK3)
% 2.86/1.01      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 2.86/1.01      | v1_funct_1(X2_49) != iProver_top ),
% 2.86/1.01      inference(renaming,[status(thm)],[c_2189]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_2199,plain,
% 2.86/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 2.86/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.86/1.01      inference(superposition,[status(thm)],[c_944,c_2190]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_28,negated_conjecture,
% 2.86/1.01      ( v1_funct_1(sK2) ),
% 2.86/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_29,plain,
% 2.86/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_2235,plain,
% 2.86/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 2.86/1.01      inference(global_propositional_subsumption,
% 2.86/1.01                [status(thm)],
% 2.86/1.01                [c_2199,c_29]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_6,plain,
% 2.86/1.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.86/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.86/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.86/1.01      | X3 = X2 ),
% 2.86/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_21,negated_conjecture,
% 2.86/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.86/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_319,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.01      | X3 = X0
% 2.86/1.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.86/1.01      | k6_partfun1(sK0) != X3
% 2.86/1.01      | sK0 != X2
% 2.86/1.01      | sK0 != X1 ),
% 2.86/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_320,plain,
% 2.86/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.86/1.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.86/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.86/1.01      inference(unflattening,[status(thm)],[c_319]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_15,plain,
% 2.86/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.86/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_328,plain,
% 2.86/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.86/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.86/1.01      inference(forward_subsumption_resolution,
% 2.86/1.01                [status(thm)],
% 2.86/1.01                [c_320,c_15]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_578,plain,
% 2.86/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.86/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_328]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_947,plain,
% 2.86/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.86/1.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_2238,plain,
% 2.86/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 2.86/1.01      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.86/1.01      inference(demodulation,[status(thm)],[c_2235,c_947]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_31,plain,
% 2.86/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_34,plain,
% 2.86/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_13,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.86/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.86/1.01      | ~ v1_funct_1(X0)
% 2.86/1.01      | ~ v1_funct_1(X3) ),
% 2.86/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_591,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.86/1.01      | ~ m1_subset_1(X3_49,k1_zfmisc_1(k2_zfmisc_1(X4_49,X5_49)))
% 2.86/1.01      | m1_subset_1(k1_partfun1(X4_49,X5_49,X1_49,X2_49,X3_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X4_49,X2_49)))
% 2.86/1.01      | ~ v1_funct_1(X0_49)
% 2.86/1.01      | ~ v1_funct_1(X3_49) ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_938,plain,
% 2.86/1.01      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
% 2.86/1.01      | m1_subset_1(X3_49,k1_zfmisc_1(k2_zfmisc_1(X4_49,X5_49))) != iProver_top
% 2.86/1.01      | m1_subset_1(k1_partfun1(X4_49,X5_49,X1_49,X2_49,X3_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X4_49,X2_49))) = iProver_top
% 2.86/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.86/1.01      | v1_funct_1(X3_49) != iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_2305,plain,
% 2.86/1.01      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 2.86/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.86/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.86/1.01      | v1_funct_1(sK3) != iProver_top
% 2.86/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.86/1.01      inference(superposition,[status(thm)],[c_2235,c_938]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_2578,plain,
% 2.86/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 2.86/1.01      inference(global_propositional_subsumption,
% 2.86/1.01                [status(thm)],
% 2.86/1.01                [c_2238,c_29,c_31,c_32,c_34,c_2305]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_4,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.86/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_592,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.86/1.01      | k2_relset_1(X1_49,X2_49,X0_49) = k2_relat_1(X0_49) ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_937,plain,
% 2.86/1.01      ( k2_relset_1(X0_49,X1_49,X2_49) = k2_relat_1(X2_49)
% 2.86/1.01      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1909,plain,
% 2.86/1.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.86/1.01      inference(superposition,[status(thm)],[c_944,c_937]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_22,negated_conjecture,
% 2.86/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.86/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_584,negated_conjecture,
% 2.86/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1914,plain,
% 2.86/1.01      ( k2_relat_1(sK2) = sK1 ),
% 2.86/1.01      inference(light_normalisation,[status(thm)],[c_1909,c_584]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_2,plain,
% 2.86/1.01      ( ~ v1_funct_1(X0)
% 2.86/1.01      | ~ v1_funct_1(X1)
% 2.86/1.01      | ~ v2_funct_1(X1)
% 2.86/1.01      | ~ v1_relat_1(X1)
% 2.86/1.01      | ~ v1_relat_1(X0)
% 2.86/1.01      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 2.86/1.01      | k2_relat_1(X1) != k1_relat_1(X0)
% 2.86/1.01      | k2_funct_1(X1) = X0 ),
% 2.86/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_20,negated_conjecture,
% 2.86/1.01      ( v2_funct_1(sK2) ),
% 2.86/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_280,plain,
% 2.86/1.01      ( ~ v1_funct_1(X0)
% 2.86/1.01      | ~ v1_funct_1(X1)
% 2.86/1.01      | ~ v1_relat_1(X1)
% 2.86/1.01      | ~ v1_relat_1(X0)
% 2.86/1.01      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 2.86/1.01      | k2_relat_1(X1) != k1_relat_1(X0)
% 2.86/1.01      | k2_funct_1(X1) = X0
% 2.86/1.01      | sK2 != X1 ),
% 2.86/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_20]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_281,plain,
% 2.86/1.01      ( ~ v1_funct_1(X0)
% 2.86/1.01      | ~ v1_funct_1(sK2)
% 2.86/1.01      | ~ v1_relat_1(X0)
% 2.86/1.01      | ~ v1_relat_1(sK2)
% 2.86/1.01      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.01      | k2_relat_1(sK2) != k1_relat_1(X0)
% 2.86/1.01      | k2_funct_1(sK2) = X0 ),
% 2.86/1.01      inference(unflattening,[status(thm)],[c_280]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_285,plain,
% 2.86/1.01      ( ~ v1_funct_1(X0)
% 2.86/1.01      | ~ v1_relat_1(X0)
% 2.86/1.01      | ~ v1_relat_1(sK2)
% 2.86/1.01      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.01      | k2_relat_1(sK2) != k1_relat_1(X0)
% 2.86/1.01      | k2_funct_1(sK2) = X0 ),
% 2.86/1.01      inference(global_propositional_subsumption,
% 2.86/1.01                [status(thm)],
% 2.86/1.01                [c_281,c_28]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_579,plain,
% 2.86/1.01      ( ~ v1_funct_1(X0_49)
% 2.86/1.01      | ~ v1_relat_1(X0_49)
% 2.86/1.01      | ~ v1_relat_1(sK2)
% 2.86/1.01      | k5_relat_1(sK2,X0_49) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.01      | k2_relat_1(sK2) != k1_relat_1(X0_49)
% 2.86/1.01      | k2_funct_1(sK2) = X0_49 ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_285]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_946,plain,
% 2.86/1.01      ( k5_relat_1(sK2,X0_49) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.01      | k2_relat_1(sK2) != k1_relat_1(X0_49)
% 2.86/1.01      | k2_funct_1(sK2) = X0_49
% 2.86/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.86/1.01      | v1_relat_1(X0_49) != iProver_top
% 2.86/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_647,plain,
% 2.86/1.01      ( k5_relat_1(sK2,X0_49) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.01      | k2_relat_1(sK2) != k1_relat_1(X0_49)
% 2.86/1.01      | k2_funct_1(sK2) = X0_49
% 2.86/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.86/1.01      | v1_relat_1(X0_49) != iProver_top
% 2.86/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_0,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.86/1.01      | ~ v1_relat_1(X1)
% 2.86/1.01      | v1_relat_1(X0) ),
% 2.86/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_595,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
% 2.86/1.01      | ~ v1_relat_1(X1_49)
% 2.86/1.01      | v1_relat_1(X0_49) ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1103,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.86/1.01      | v1_relat_1(X0_49)
% 2.86/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1_49,X2_49)) ),
% 2.86/1.01      inference(instantiation,[status(thm)],[c_595]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1264,plain,
% 2.86/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.86/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 2.86/1.01      | v1_relat_1(sK2) ),
% 2.86/1.01      inference(instantiation,[status(thm)],[c_1103]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1265,plain,
% 2.86/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.86/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.86/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_1264]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1,plain,
% 2.86/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.86/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_594,plain,
% 2.86/1.01      ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1290,plain,
% 2.86/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.86/1.01      inference(instantiation,[status(thm)],[c_594]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1291,plain,
% 2.86/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_1290]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1681,plain,
% 2.86/1.01      ( v1_relat_1(X0_49) != iProver_top
% 2.86/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.86/1.01      | k2_funct_1(sK2) = X0_49
% 2.86/1.01      | k2_relat_1(sK2) != k1_relat_1(X0_49)
% 2.86/1.01      | k5_relat_1(sK2,X0_49) != k6_partfun1(k1_relat_1(sK2)) ),
% 2.86/1.01      inference(global_propositional_subsumption,
% 2.86/1.01                [status(thm)],
% 2.86/1.01                [c_946,c_31,c_647,c_1265,c_1291]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1682,plain,
% 2.86/1.01      ( k5_relat_1(sK2,X0_49) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.01      | k2_relat_1(sK2) != k1_relat_1(X0_49)
% 2.86/1.01      | k2_funct_1(sK2) = X0_49
% 2.86/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.86/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 2.86/1.01      inference(renaming,[status(thm)],[c_1681]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1920,plain,
% 2.86/1.01      ( k5_relat_1(sK2,X0_49) != k6_partfun1(k1_relat_1(sK2))
% 2.86/1.01      | k1_relat_1(X0_49) != sK1
% 2.86/1.01      | k2_funct_1(sK2) = X0_49
% 2.86/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.86/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 2.86/1.01      inference(demodulation,[status(thm)],[c_1914,c_1682]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_3,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.86/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_593,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.86/1.01      | k1_relset_1(X1_49,X2_49,X0_49) = k1_relat_1(X0_49) ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_936,plain,
% 2.86/1.01      ( k1_relset_1(X0_49,X1_49,X2_49) = k1_relat_1(X2_49)
% 2.86/1.01      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1844,plain,
% 2.86/1.01      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.86/1.01      inference(superposition,[status(thm)],[c_944,c_936]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_12,plain,
% 2.86/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.86/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.86/1.01      | k1_xboole_0 = X2 ),
% 2.86/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_27,negated_conjecture,
% 2.86/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.86/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_419,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.86/1.01      | sK0 != X1
% 2.86/1.01      | sK1 != X2
% 2.86/1.01      | sK2 != X0
% 2.86/1.01      | k1_xboole_0 = X2 ),
% 2.86/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_420,plain,
% 2.86/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.86/1.01      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.86/1.01      | k1_xboole_0 = sK1 ),
% 2.86/1.01      inference(unflattening,[status(thm)],[c_419]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_18,negated_conjecture,
% 2.86/1.01      ( k1_xboole_0 != sK1 ),
% 2.86/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_422,plain,
% 2.86/1.01      ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
% 2.86/1.01      inference(global_propositional_subsumption,
% 2.86/1.01                [status(thm)],
% 2.86/1.01                [c_420,c_26,c_18]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_572,plain,
% 2.86/1.01      ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_422]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1849,plain,
% 2.86/1.01      ( k1_relat_1(sK2) = sK0 ),
% 2.86/1.01      inference(light_normalisation,[status(thm)],[c_1844,c_572]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_2114,plain,
% 2.86/1.01      ( k5_relat_1(sK2,X0_49) != k6_partfun1(sK0)
% 2.86/1.01      | k1_relat_1(X0_49) != sK1
% 2.86/1.01      | k2_funct_1(sK2) = X0_49
% 2.86/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.86/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 2.86/1.01      inference(light_normalisation,[status(thm)],[c_1920,c_1849]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_2582,plain,
% 2.86/1.01      ( k1_relat_1(sK3) != sK1
% 2.86/1.01      | k2_funct_1(sK2) = sK3
% 2.86/1.01      | v1_funct_1(sK3) != iProver_top
% 2.86/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.86/1.01      inference(superposition,[status(thm)],[c_2578,c_2114]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1843,plain,
% 2.86/1.01      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 2.86/1.01      inference(superposition,[status(thm)],[c_942,c_936]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_24,negated_conjecture,
% 2.86/1.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.86/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_411,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.86/1.01      | sK0 != X2
% 2.86/1.01      | sK1 != X1
% 2.86/1.01      | sK3 != X0
% 2.86/1.01      | k1_xboole_0 = X2 ),
% 2.86/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_412,plain,
% 2.86/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.86/1.01      | k1_relset_1(sK1,sK0,sK3) = sK1
% 2.86/1.01      | k1_xboole_0 = sK0 ),
% 2.86/1.01      inference(unflattening,[status(thm)],[c_411]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_19,negated_conjecture,
% 2.86/1.01      ( k1_xboole_0 != sK0 ),
% 2.86/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_414,plain,
% 2.86/1.01      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 2.86/1.01      inference(global_propositional_subsumption,
% 2.86/1.01                [status(thm)],
% 2.86/1.01                [c_412,c_23,c_19]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_573,plain,
% 2.86/1.01      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_414]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1852,plain,
% 2.86/1.01      ( k1_relat_1(sK3) = sK1 ),
% 2.86/1.01      inference(light_normalisation,[status(thm)],[c_1843,c_573]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_2583,plain,
% 2.86/1.01      ( k2_funct_1(sK2) = sK3
% 2.86/1.01      | sK1 != sK1
% 2.86/1.01      | v1_funct_1(sK3) != iProver_top
% 2.86/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.86/1.01      inference(light_normalisation,[status(thm)],[c_2582,c_1852]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_2584,plain,
% 2.86/1.01      ( k2_funct_1(sK2) = sK3
% 2.86/1.01      | v1_funct_1(sK3) != iProver_top
% 2.86/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.86/1.01      inference(equality_resolution_simp,[status(thm)],[c_2583]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1287,plain,
% 2.86/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.86/1.01      inference(instantiation,[status(thm)],[c_594]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1288,plain,
% 2.86/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_1287]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1261,plain,
% 2.86/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.86/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 2.86/1.01      | v1_relat_1(sK3) ),
% 2.86/1.01      inference(instantiation,[status(thm)],[c_1103]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1262,plain,
% 2.86/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.86/1.01      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.86/1.01      | v1_relat_1(sK3) = iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_1261]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_17,negated_conjecture,
% 2.86/1.01      ( k2_funct_1(sK2) != sK3 ),
% 2.86/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_587,negated_conjecture,
% 2.86/1.01      ( k2_funct_1(sK2) != sK3 ),
% 2.86/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(contradiction,plain,
% 2.86/1.01      ( $false ),
% 2.86/1.01      inference(minisat,
% 2.86/1.01                [status(thm)],
% 2.86/1.01                [c_2584,c_1288,c_1262,c_587,c_34,c_32]) ).
% 2.86/1.01  
% 2.86/1.01  
% 2.86/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.86/1.01  
% 2.86/1.01  ------                               Statistics
% 2.86/1.01  
% 2.86/1.01  ------ General
% 2.86/1.01  
% 2.86/1.01  abstr_ref_over_cycles:                  0
% 2.86/1.01  abstr_ref_under_cycles:                 0
% 2.86/1.01  gc_basic_clause_elim:                   0
% 2.86/1.01  forced_gc_time:                         0
% 2.86/1.01  parsing_time:                           0.014
% 2.86/1.01  unif_index_cands_time:                  0.
% 2.86/1.01  unif_index_add_time:                    0.
% 2.86/1.01  orderings_time:                         0.
% 2.86/1.01  out_proof_time:                         0.01
% 2.86/1.01  total_time:                             0.145
% 2.86/1.01  num_of_symbols:                         54
% 2.86/1.01  num_of_terms:                           3558
% 2.86/1.01  
% 2.86/1.01  ------ Preprocessing
% 2.86/1.01  
% 2.86/1.01  num_of_splits:                          0
% 2.86/1.01  num_of_split_atoms:                     0
% 2.86/1.01  num_of_reused_defs:                     0
% 2.86/1.01  num_eq_ax_congr_red:                    8
% 2.86/1.01  num_of_sem_filtered_clauses:            1
% 2.86/1.01  num_of_subtypes:                        2
% 2.86/1.01  monotx_restored_types:                  0
% 2.86/1.01  sat_num_of_epr_types:                   0
% 2.86/1.01  sat_num_of_non_cyclic_types:            0
% 2.86/1.01  sat_guarded_non_collapsed_types:        1
% 2.86/1.01  num_pure_diseq_elim:                    0
% 2.86/1.01  simp_replaced_by:                       0
% 2.86/1.01  res_preprocessed:                       134
% 2.86/1.01  prep_upred:                             0
% 2.86/1.01  prep_unflattend:                        43
% 2.86/1.01  smt_new_axioms:                         0
% 2.86/1.01  pred_elim_cands:                        3
% 2.86/1.01  pred_elim:                              3
% 2.86/1.01  pred_elim_cl:                           5
% 2.86/1.01  pred_elim_cycles:                       5
% 2.86/1.01  merged_defs:                            0
% 2.86/1.01  merged_defs_ncl:                        0
% 2.86/1.01  bin_hyper_res:                          0
% 2.86/1.01  prep_cycles:                            4
% 2.86/1.01  pred_elim_time:                         0.005
% 2.86/1.01  splitting_time:                         0.
% 2.86/1.01  sem_filter_time:                        0.
% 2.86/1.01  monotx_time:                            0.
% 2.86/1.01  subtype_inf_time:                       0.
% 2.86/1.01  
% 2.86/1.01  ------ Problem properties
% 2.86/1.01  
% 2.86/1.01  clauses:                                24
% 2.86/1.01  conjectures:                            8
% 2.86/1.01  epr:                                    4
% 2.86/1.01  horn:                                   24
% 2.86/1.01  ground:                                 15
% 2.86/1.01  unary:                                  12
% 2.86/1.01  binary:                                 3
% 2.86/1.01  lits:                                   54
% 2.86/1.01  lits_eq:                                21
% 2.86/1.01  fd_pure:                                0
% 2.86/1.01  fd_pseudo:                              0
% 2.86/1.01  fd_cond:                                1
% 2.86/1.01  fd_pseudo_cond:                         0
% 2.86/1.01  ac_symbols:                             0
% 2.86/1.01  
% 2.86/1.01  ------ Propositional Solver
% 2.86/1.01  
% 2.86/1.01  prop_solver_calls:                      25
% 2.86/1.01  prop_fast_solver_calls:                 809
% 2.86/1.01  smt_solver_calls:                       0
% 2.86/1.01  smt_fast_solver_calls:                  0
% 2.86/1.01  prop_num_of_clauses:                    1046
% 2.86/1.01  prop_preprocess_simplified:             3707
% 2.86/1.01  prop_fo_subsumed:                       25
% 2.86/1.01  prop_solver_time:                       0.
% 2.86/1.01  smt_solver_time:                        0.
% 2.86/1.01  smt_fast_solver_time:                   0.
% 2.86/1.01  prop_fast_solver_time:                  0.
% 2.86/1.01  prop_unsat_core_time:                   0.
% 2.86/1.01  
% 2.86/1.01  ------ QBF
% 2.86/1.01  
% 2.86/1.01  qbf_q_res:                              0
% 2.86/1.01  qbf_num_tautologies:                    0
% 2.86/1.01  qbf_prep_cycles:                        0
% 2.86/1.01  
% 2.86/1.01  ------ BMC1
% 2.86/1.01  
% 2.86/1.01  bmc1_current_bound:                     -1
% 2.86/1.01  bmc1_last_solved_bound:                 -1
% 2.86/1.01  bmc1_unsat_core_size:                   -1
% 2.86/1.01  bmc1_unsat_core_parents_size:           -1
% 2.86/1.01  bmc1_merge_next_fun:                    0
% 2.86/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.86/1.01  
% 2.86/1.01  ------ Instantiation
% 2.86/1.01  
% 2.86/1.01  inst_num_of_clauses:                    276
% 2.86/1.01  inst_num_in_passive:                    70
% 2.86/1.01  inst_num_in_active:                     189
% 2.86/1.01  inst_num_in_unprocessed:                17
% 2.86/1.01  inst_num_of_loops:                      200
% 2.86/1.01  inst_num_of_learning_restarts:          0
% 2.86/1.01  inst_num_moves_active_passive:          8
% 2.86/1.01  inst_lit_activity:                      0
% 2.86/1.01  inst_lit_activity_moves:                0
% 2.86/1.01  inst_num_tautologies:                   0
% 2.86/1.01  inst_num_prop_implied:                  0
% 2.86/1.01  inst_num_existing_simplified:           0
% 2.86/1.01  inst_num_eq_res_simplified:             0
% 2.86/1.01  inst_num_child_elim:                    0
% 2.86/1.01  inst_num_of_dismatching_blockings:      14
% 2.86/1.01  inst_num_of_non_proper_insts:           192
% 2.86/1.01  inst_num_of_duplicates:                 0
% 2.86/1.01  inst_inst_num_from_inst_to_res:         0
% 2.86/1.01  inst_dismatching_checking_time:         0.
% 2.86/1.01  
% 2.86/1.01  ------ Resolution
% 2.86/1.01  
% 2.86/1.01  res_num_of_clauses:                     0
% 2.86/1.01  res_num_in_passive:                     0
% 2.86/1.01  res_num_in_active:                      0
% 2.86/1.01  res_num_of_loops:                       138
% 2.86/1.01  res_forward_subset_subsumed:            28
% 2.86/1.01  res_backward_subset_subsumed:           0
% 2.86/1.01  res_forward_subsumed:                   0
% 2.86/1.01  res_backward_subsumed:                  0
% 2.86/1.01  res_forward_subsumption_resolution:     1
% 2.86/1.01  res_backward_subsumption_resolution:    0
% 2.86/1.01  res_clause_to_clause_subsumption:       100
% 2.86/1.01  res_orphan_elimination:                 0
% 2.86/1.01  res_tautology_del:                      21
% 2.86/1.01  res_num_eq_res_simplified:              0
% 2.86/1.01  res_num_sel_changes:                    0
% 2.86/1.01  res_moves_from_active_to_pass:          0
% 2.86/1.01  
% 2.86/1.01  ------ Superposition
% 2.86/1.01  
% 2.86/1.01  sup_time_total:                         0.
% 2.86/1.01  sup_time_generating:                    0.
% 2.86/1.01  sup_time_sim_full:                      0.
% 2.86/1.01  sup_time_sim_immed:                     0.
% 2.86/1.01  
% 2.86/1.01  sup_num_of_clauses:                     55
% 2.86/1.01  sup_num_in_active:                      36
% 2.86/1.01  sup_num_in_passive:                     19
% 2.86/1.01  sup_num_of_loops:                       38
% 2.86/1.01  sup_fw_superposition:                   17
% 2.86/1.01  sup_bw_superposition:                   16
% 2.86/1.01  sup_immediate_simplified:               4
% 2.86/1.01  sup_given_eliminated:                   0
% 2.86/1.01  comparisons_done:                       0
% 2.86/1.01  comparisons_avoided:                    0
% 2.86/1.01  
% 2.86/1.01  ------ Simplifications
% 2.86/1.01  
% 2.86/1.01  
% 2.86/1.01  sim_fw_subset_subsumed:                 0
% 2.86/1.01  sim_bw_subset_subsumed:                 0
% 2.86/1.01  sim_fw_subsumed:                        0
% 2.86/1.01  sim_bw_subsumed:                        0
% 2.86/1.01  sim_fw_subsumption_res:                 1
% 2.86/1.01  sim_bw_subsumption_res:                 0
% 2.86/1.01  sim_tautology_del:                      0
% 2.86/1.01  sim_eq_tautology_del:                   0
% 2.86/1.01  sim_eq_res_simp:                        1
% 2.86/1.01  sim_fw_demodulated:                     0
% 2.86/1.01  sim_bw_demodulated:                     3
% 2.86/1.01  sim_light_normalised:                   5
% 2.86/1.01  sim_joinable_taut:                      0
% 2.86/1.01  sim_joinable_simp:                      0
% 2.86/1.01  sim_ac_normalised:                      0
% 2.86/1.01  sim_smt_subsumption:                    0
% 2.86/1.01  
%------------------------------------------------------------------------------
