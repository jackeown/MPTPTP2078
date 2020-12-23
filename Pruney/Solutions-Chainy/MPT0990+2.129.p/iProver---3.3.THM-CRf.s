%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:24 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  221 (1180 expanded)
%              Number of clauses        :  129 ( 376 expanded)
%              Number of leaves         :   24 ( 265 expanded)
%              Depth                    :   21
%              Number of atoms          :  645 (7731 expanded)
%              Number of equality atoms :  294 (2973 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f24,plain,(
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
    inference(pure_predicate_removal,[],[f23])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f57,plain,(
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

fof(f56,plain,
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

fof(f58,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f57,f56])).

fof(f90,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f77,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f101,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f77,f86])).

fof(f93,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f82,f86])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f98,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f67,f86])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f69,f86])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f70,f86])).

fof(f96,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1324,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1343,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3221,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_1343])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1452,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1517,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1452])).

cnf(c_1518,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1517])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1597,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1598,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1597])).

cnf(c_3229,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3221,c_40,c_1518,c_1598])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1322,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3222,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1322,c_1343])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1398,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1434,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_1486,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_1487,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_1594,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1595,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1594])).

cnf(c_3445,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3222,c_38,c_1487,c_1595])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1321,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1332,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1336,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5178,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1332,c_1336])).

cnf(c_20598,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_5178])).

cnf(c_20983,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20598,c_38,c_1487,c_1595])).

cnf(c_20984,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_20983])).

cnf(c_20991,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3445,c_20984])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1329,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2249,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1322,c_1329])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2250,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2249,c_32])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_393,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_30])).

cnf(c_394,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_396,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_36])).

cnf(c_1318,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_1953,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1318,c_36,c_35,c_394,c_1486,c_1594])).

cnf(c_2320,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2250,c_1953])).

cnf(c_21002,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20991,c_2320])).

cnf(c_21076,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_3229,c_21002])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1325,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2194,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_1325])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2825,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2194,c_39])).

cnf(c_2826,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2825])).

cnf(c_2833,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1322,c_2826])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_363,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_23,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_53,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_365,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_53])).

cnf(c_1320,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1385,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2046,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1320,c_36,c_35,c_34,c_33,c_53,c_363,c_1385])).

cnf(c_2834,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2833,c_2046])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4402,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2834,c_37])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1330,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2239,plain,
    ( v4_relat_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_1330])).

cnf(c_2,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1341,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1331,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4655,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2250,c_1331])).

cnf(c_5194,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4655,c_37,c_38,c_1487,c_1595])).

cnf(c_5200,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
    | v4_relat_1(X0,sK1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1341,c_5194])).

cnf(c_6368,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2239,c_5200])).

cnf(c_2240,plain,
    ( v4_relat_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1322,c_1330])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1337,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3162,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_1337])).

cnf(c_2094,plain,
    ( ~ v4_relat_1(sK2,X0)
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2095,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | v4_relat_1(sK2,X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2094])).

cnf(c_2097,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v4_relat_1(sK2,sK0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2095])).

cnf(c_4003,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3162,c_38,c_1487,c_1595,c_2097,c_2240])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1339,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3449,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_3445,c_1339])).

cnf(c_4005,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4003,c_3449])).

cnf(c_4006,plain,
    ( k9_relat_1(sK2,sK0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4005,c_2250])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1338,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4944,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3445,c_1338])).

cnf(c_5342,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3229,c_4944])).

cnf(c_5343,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_5342,c_4402])).

cnf(c_9,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_5344,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = sK0 ),
    inference(demodulation,[status(thm)],[c_5343,c_9])).

cnf(c_6373,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6368,c_4006,c_5344])).

cnf(c_6623,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6373,c_40,c_1518,c_1598])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1335,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3234,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_3229,c_1335])).

cnf(c_6627,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_6623,c_3234])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_421,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_30])).

cnf(c_422,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_424,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_36])).

cnf(c_1316,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_1632,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1316,c_36,c_35,c_422,c_1486,c_1594])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1334,plain,
    ( k5_relat_1(X0,k6_partfun1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3956,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1632,c_1334])).

cnf(c_1500,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1501,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1500])).

cnf(c_6637,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3956,c_37,c_38,c_1487,c_1501,c_1595])).

cnf(c_6638,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6637])).

cnf(c_6643,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | v4_relat_1(sK2,X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1341,c_6638])).

cnf(c_18644,plain,
    ( v4_relat_1(sK2,X0) != iProver_top
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6643,c_38,c_1487,c_1595])).

cnf(c_18645,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | v4_relat_1(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_18644])).

cnf(c_18650,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_2240,c_18645])).

cnf(c_21086,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_21076,c_4402,c_6627,c_18650])).

cnf(c_27,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f96])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21086,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:18:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 7.65/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/1.52  
% 7.65/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.52  
% 7.65/1.52  ------  iProver source info
% 7.65/1.52  
% 7.65/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.52  git: non_committed_changes: false
% 7.65/1.52  git: last_make_outside_of_git: false
% 7.65/1.52  
% 7.65/1.52  ------ 
% 7.65/1.52  
% 7.65/1.52  ------ Input Options
% 7.65/1.52  
% 7.65/1.52  --out_options                           all
% 7.65/1.52  --tptp_safe_out                         true
% 7.65/1.52  --problem_path                          ""
% 7.65/1.52  --include_path                          ""
% 7.65/1.52  --clausifier                            res/vclausify_rel
% 7.65/1.52  --clausifier_options                    ""
% 7.65/1.52  --stdin                                 false
% 7.65/1.52  --stats_out                             all
% 7.65/1.52  
% 7.65/1.52  ------ General Options
% 7.65/1.52  
% 7.65/1.52  --fof                                   false
% 7.65/1.52  --time_out_real                         305.
% 7.65/1.52  --time_out_virtual                      -1.
% 7.65/1.52  --symbol_type_check                     false
% 7.65/1.52  --clausify_out                          false
% 7.65/1.52  --sig_cnt_out                           false
% 7.65/1.52  --trig_cnt_out                          false
% 7.65/1.52  --trig_cnt_out_tolerance                1.
% 7.65/1.52  --trig_cnt_out_sk_spl                   false
% 7.65/1.52  --abstr_cl_out                          false
% 7.65/1.52  
% 7.65/1.52  ------ Global Options
% 7.65/1.52  
% 7.65/1.52  --schedule                              default
% 7.65/1.52  --add_important_lit                     false
% 7.65/1.52  --prop_solver_per_cl                    1000
% 7.65/1.52  --min_unsat_core                        false
% 7.65/1.52  --soft_assumptions                      false
% 7.65/1.52  --soft_lemma_size                       3
% 7.65/1.52  --prop_impl_unit_size                   0
% 7.65/1.52  --prop_impl_unit                        []
% 7.65/1.52  --share_sel_clauses                     true
% 7.65/1.52  --reset_solvers                         false
% 7.65/1.52  --bc_imp_inh                            [conj_cone]
% 7.65/1.52  --conj_cone_tolerance                   3.
% 7.65/1.52  --extra_neg_conj                        none
% 7.65/1.52  --large_theory_mode                     true
% 7.65/1.52  --prolific_symb_bound                   200
% 7.65/1.52  --lt_threshold                          2000
% 7.65/1.52  --clause_weak_htbl                      true
% 7.65/1.52  --gc_record_bc_elim                     false
% 7.65/1.52  
% 7.65/1.52  ------ Preprocessing Options
% 7.65/1.52  
% 7.65/1.52  --preprocessing_flag                    true
% 7.65/1.52  --time_out_prep_mult                    0.1
% 7.65/1.52  --splitting_mode                        input
% 7.65/1.52  --splitting_grd                         true
% 7.65/1.52  --splitting_cvd                         false
% 7.65/1.52  --splitting_cvd_svl                     false
% 7.65/1.52  --splitting_nvd                         32
% 7.65/1.52  --sub_typing                            true
% 7.65/1.52  --prep_gs_sim                           true
% 7.65/1.52  --prep_unflatten                        true
% 7.65/1.52  --prep_res_sim                          true
% 7.65/1.52  --prep_upred                            true
% 7.65/1.52  --prep_sem_filter                       exhaustive
% 7.65/1.52  --prep_sem_filter_out                   false
% 7.65/1.52  --pred_elim                             true
% 7.65/1.52  --res_sim_input                         true
% 7.65/1.52  --eq_ax_congr_red                       true
% 7.65/1.52  --pure_diseq_elim                       true
% 7.65/1.52  --brand_transform                       false
% 7.65/1.52  --non_eq_to_eq                          false
% 7.65/1.52  --prep_def_merge                        true
% 7.65/1.52  --prep_def_merge_prop_impl              false
% 7.65/1.52  --prep_def_merge_mbd                    true
% 7.65/1.52  --prep_def_merge_tr_red                 false
% 7.65/1.52  --prep_def_merge_tr_cl                  false
% 7.65/1.52  --smt_preprocessing                     true
% 7.65/1.52  --smt_ac_axioms                         fast
% 7.65/1.52  --preprocessed_out                      false
% 7.65/1.52  --preprocessed_stats                    false
% 7.65/1.52  
% 7.65/1.52  ------ Abstraction refinement Options
% 7.65/1.52  
% 7.65/1.52  --abstr_ref                             []
% 7.65/1.52  --abstr_ref_prep                        false
% 7.65/1.52  --abstr_ref_until_sat                   false
% 7.65/1.52  --abstr_ref_sig_restrict                funpre
% 7.65/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.52  --abstr_ref_under                       []
% 7.65/1.52  
% 7.65/1.52  ------ SAT Options
% 7.65/1.52  
% 7.65/1.52  --sat_mode                              false
% 7.65/1.52  --sat_fm_restart_options                ""
% 7.65/1.52  --sat_gr_def                            false
% 7.65/1.52  --sat_epr_types                         true
% 7.65/1.52  --sat_non_cyclic_types                  false
% 7.65/1.52  --sat_finite_models                     false
% 7.65/1.52  --sat_fm_lemmas                         false
% 7.65/1.52  --sat_fm_prep                           false
% 7.65/1.52  --sat_fm_uc_incr                        true
% 7.65/1.52  --sat_out_model                         small
% 7.65/1.52  --sat_out_clauses                       false
% 7.65/1.52  
% 7.65/1.52  ------ QBF Options
% 7.65/1.52  
% 7.65/1.52  --qbf_mode                              false
% 7.65/1.52  --qbf_elim_univ                         false
% 7.65/1.52  --qbf_dom_inst                          none
% 7.65/1.52  --qbf_dom_pre_inst                      false
% 7.65/1.52  --qbf_sk_in                             false
% 7.65/1.52  --qbf_pred_elim                         true
% 7.65/1.52  --qbf_split                             512
% 7.65/1.52  
% 7.65/1.52  ------ BMC1 Options
% 7.65/1.52  
% 7.65/1.52  --bmc1_incremental                      false
% 7.65/1.52  --bmc1_axioms                           reachable_all
% 7.65/1.52  --bmc1_min_bound                        0
% 7.65/1.52  --bmc1_max_bound                        -1
% 7.65/1.52  --bmc1_max_bound_default                -1
% 7.65/1.52  --bmc1_symbol_reachability              true
% 7.65/1.52  --bmc1_property_lemmas                  false
% 7.65/1.52  --bmc1_k_induction                      false
% 7.65/1.52  --bmc1_non_equiv_states                 false
% 7.65/1.52  --bmc1_deadlock                         false
% 7.65/1.52  --bmc1_ucm                              false
% 7.65/1.52  --bmc1_add_unsat_core                   none
% 7.65/1.52  --bmc1_unsat_core_children              false
% 7.65/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.52  --bmc1_out_stat                         full
% 7.65/1.52  --bmc1_ground_init                      false
% 7.65/1.52  --bmc1_pre_inst_next_state              false
% 7.65/1.52  --bmc1_pre_inst_state                   false
% 7.65/1.52  --bmc1_pre_inst_reach_state             false
% 7.65/1.52  --bmc1_out_unsat_core                   false
% 7.65/1.52  --bmc1_aig_witness_out                  false
% 7.65/1.52  --bmc1_verbose                          false
% 7.65/1.52  --bmc1_dump_clauses_tptp                false
% 7.65/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.52  --bmc1_dump_file                        -
% 7.65/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.52  --bmc1_ucm_extend_mode                  1
% 7.65/1.52  --bmc1_ucm_init_mode                    2
% 7.65/1.52  --bmc1_ucm_cone_mode                    none
% 7.65/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.52  --bmc1_ucm_relax_model                  4
% 7.65/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.52  --bmc1_ucm_layered_model                none
% 7.65/1.52  --bmc1_ucm_max_lemma_size               10
% 7.65/1.52  
% 7.65/1.52  ------ AIG Options
% 7.65/1.52  
% 7.65/1.52  --aig_mode                              false
% 7.65/1.52  
% 7.65/1.52  ------ Instantiation Options
% 7.65/1.52  
% 7.65/1.52  --instantiation_flag                    true
% 7.65/1.52  --inst_sos_flag                         true
% 7.65/1.52  --inst_sos_phase                        true
% 7.65/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.52  --inst_lit_sel_side                     num_symb
% 7.65/1.52  --inst_solver_per_active                1400
% 7.65/1.52  --inst_solver_calls_frac                1.
% 7.65/1.52  --inst_passive_queue_type               priority_queues
% 7.65/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.52  --inst_passive_queues_freq              [25;2]
% 7.65/1.52  --inst_dismatching                      true
% 7.65/1.52  --inst_eager_unprocessed_to_passive     true
% 7.65/1.52  --inst_prop_sim_given                   true
% 7.65/1.52  --inst_prop_sim_new                     false
% 7.65/1.52  --inst_subs_new                         false
% 7.65/1.52  --inst_eq_res_simp                      false
% 7.65/1.52  --inst_subs_given                       false
% 7.65/1.52  --inst_orphan_elimination               true
% 7.65/1.52  --inst_learning_loop_flag               true
% 7.65/1.52  --inst_learning_start                   3000
% 7.65/1.52  --inst_learning_factor                  2
% 7.65/1.52  --inst_start_prop_sim_after_learn       3
% 7.65/1.52  --inst_sel_renew                        solver
% 7.65/1.52  --inst_lit_activity_flag                true
% 7.65/1.52  --inst_restr_to_given                   false
% 7.65/1.52  --inst_activity_threshold               500
% 7.65/1.52  --inst_out_proof                        true
% 7.65/1.52  
% 7.65/1.52  ------ Resolution Options
% 7.65/1.52  
% 7.65/1.52  --resolution_flag                       true
% 7.65/1.52  --res_lit_sel                           adaptive
% 7.65/1.52  --res_lit_sel_side                      none
% 7.65/1.52  --res_ordering                          kbo
% 7.65/1.52  --res_to_prop_solver                    active
% 7.65/1.52  --res_prop_simpl_new                    false
% 7.65/1.52  --res_prop_simpl_given                  true
% 7.65/1.52  --res_passive_queue_type                priority_queues
% 7.65/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.52  --res_passive_queues_freq               [15;5]
% 7.65/1.52  --res_forward_subs                      full
% 7.65/1.52  --res_backward_subs                     full
% 7.65/1.52  --res_forward_subs_resolution           true
% 7.65/1.52  --res_backward_subs_resolution          true
% 7.65/1.52  --res_orphan_elimination                true
% 7.65/1.52  --res_time_limit                        2.
% 7.65/1.52  --res_out_proof                         true
% 7.65/1.52  
% 7.65/1.52  ------ Superposition Options
% 7.65/1.52  
% 7.65/1.52  --superposition_flag                    true
% 7.65/1.52  --sup_passive_queue_type                priority_queues
% 7.65/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.52  --demod_completeness_check              fast
% 7.65/1.52  --demod_use_ground                      true
% 7.65/1.52  --sup_to_prop_solver                    passive
% 7.65/1.52  --sup_prop_simpl_new                    true
% 7.65/1.52  --sup_prop_simpl_given                  true
% 7.65/1.52  --sup_fun_splitting                     true
% 7.65/1.52  --sup_smt_interval                      50000
% 7.65/1.52  
% 7.65/1.52  ------ Superposition Simplification Setup
% 7.65/1.52  
% 7.65/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.65/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.65/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.65/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.65/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.65/1.52  --sup_immed_triv                        [TrivRules]
% 7.65/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.52  --sup_immed_bw_main                     []
% 7.65/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.65/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.52  --sup_input_bw                          []
% 7.65/1.52  
% 7.65/1.52  ------ Combination Options
% 7.65/1.52  
% 7.65/1.52  --comb_res_mult                         3
% 7.65/1.52  --comb_sup_mult                         2
% 7.65/1.52  --comb_inst_mult                        10
% 7.65/1.52  
% 7.65/1.52  ------ Debug Options
% 7.65/1.52  
% 7.65/1.52  --dbg_backtrace                         false
% 7.65/1.52  --dbg_dump_prop_clauses                 false
% 7.65/1.52  --dbg_dump_prop_clauses_file            -
% 7.65/1.52  --dbg_out_stat                          false
% 7.65/1.52  ------ Parsing...
% 7.65/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.52  
% 7.65/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.65/1.52  
% 7.65/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.52  
% 7.65/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.52  ------ Proving...
% 7.65/1.52  ------ Problem Properties 
% 7.65/1.52  
% 7.65/1.52  
% 7.65/1.52  clauses                                 34
% 7.65/1.52  conjectures                             8
% 7.65/1.52  EPR                                     4
% 7.65/1.52  Horn                                    34
% 7.65/1.52  unary                                   12
% 7.65/1.52  binary                                  9
% 7.65/1.52  lits                                    77
% 7.65/1.52  lits eq                                 20
% 7.65/1.52  fd_pure                                 0
% 7.65/1.52  fd_pseudo                               0
% 7.65/1.52  fd_cond                                 0
% 7.65/1.52  fd_pseudo_cond                          0
% 7.65/1.52  AC symbols                              0
% 7.65/1.52  
% 7.65/1.52  ------ Schedule dynamic 5 is on 
% 7.65/1.52  
% 7.65/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.65/1.52  
% 7.65/1.52  
% 7.65/1.52  ------ 
% 7.65/1.52  Current options:
% 7.65/1.52  ------ 
% 7.65/1.52  
% 7.65/1.52  ------ Input Options
% 7.65/1.52  
% 7.65/1.52  --out_options                           all
% 7.65/1.52  --tptp_safe_out                         true
% 7.65/1.52  --problem_path                          ""
% 7.65/1.52  --include_path                          ""
% 7.65/1.52  --clausifier                            res/vclausify_rel
% 7.65/1.52  --clausifier_options                    ""
% 7.65/1.52  --stdin                                 false
% 7.65/1.52  --stats_out                             all
% 7.65/1.52  
% 7.65/1.52  ------ General Options
% 7.65/1.52  
% 7.65/1.52  --fof                                   false
% 7.65/1.52  --time_out_real                         305.
% 7.65/1.52  --time_out_virtual                      -1.
% 7.65/1.52  --symbol_type_check                     false
% 7.65/1.52  --clausify_out                          false
% 7.65/1.52  --sig_cnt_out                           false
% 7.65/1.52  --trig_cnt_out                          false
% 7.65/1.52  --trig_cnt_out_tolerance                1.
% 7.65/1.52  --trig_cnt_out_sk_spl                   false
% 7.65/1.52  --abstr_cl_out                          false
% 7.65/1.52  
% 7.65/1.52  ------ Global Options
% 7.65/1.52  
% 7.65/1.52  --schedule                              default
% 7.65/1.52  --add_important_lit                     false
% 7.65/1.52  --prop_solver_per_cl                    1000
% 7.65/1.52  --min_unsat_core                        false
% 7.65/1.52  --soft_assumptions                      false
% 7.65/1.52  --soft_lemma_size                       3
% 7.65/1.52  --prop_impl_unit_size                   0
% 7.65/1.52  --prop_impl_unit                        []
% 7.65/1.52  --share_sel_clauses                     true
% 7.65/1.52  --reset_solvers                         false
% 7.65/1.52  --bc_imp_inh                            [conj_cone]
% 7.65/1.52  --conj_cone_tolerance                   3.
% 7.65/1.52  --extra_neg_conj                        none
% 7.65/1.52  --large_theory_mode                     true
% 7.65/1.52  --prolific_symb_bound                   200
% 7.65/1.52  --lt_threshold                          2000
% 7.65/1.52  --clause_weak_htbl                      true
% 7.65/1.52  --gc_record_bc_elim                     false
% 7.65/1.52  
% 7.65/1.52  ------ Preprocessing Options
% 7.65/1.52  
% 7.65/1.52  --preprocessing_flag                    true
% 7.65/1.52  --time_out_prep_mult                    0.1
% 7.65/1.52  --splitting_mode                        input
% 7.65/1.52  --splitting_grd                         true
% 7.65/1.52  --splitting_cvd                         false
% 7.65/1.52  --splitting_cvd_svl                     false
% 7.65/1.52  --splitting_nvd                         32
% 7.65/1.52  --sub_typing                            true
% 7.65/1.52  --prep_gs_sim                           true
% 7.65/1.52  --prep_unflatten                        true
% 7.65/1.52  --prep_res_sim                          true
% 7.65/1.52  --prep_upred                            true
% 7.65/1.52  --prep_sem_filter                       exhaustive
% 7.65/1.52  --prep_sem_filter_out                   false
% 7.65/1.52  --pred_elim                             true
% 7.65/1.52  --res_sim_input                         true
% 7.65/1.52  --eq_ax_congr_red                       true
% 7.65/1.52  --pure_diseq_elim                       true
% 7.65/1.52  --brand_transform                       false
% 7.65/1.52  --non_eq_to_eq                          false
% 7.65/1.52  --prep_def_merge                        true
% 7.65/1.52  --prep_def_merge_prop_impl              false
% 7.65/1.52  --prep_def_merge_mbd                    true
% 7.65/1.52  --prep_def_merge_tr_red                 false
% 7.65/1.52  --prep_def_merge_tr_cl                  false
% 7.65/1.52  --smt_preprocessing                     true
% 7.65/1.52  --smt_ac_axioms                         fast
% 7.65/1.52  --preprocessed_out                      false
% 7.65/1.52  --preprocessed_stats                    false
% 7.65/1.52  
% 7.65/1.52  ------ Abstraction refinement Options
% 7.65/1.52  
% 7.65/1.52  --abstr_ref                             []
% 7.65/1.52  --abstr_ref_prep                        false
% 7.65/1.52  --abstr_ref_until_sat                   false
% 7.65/1.52  --abstr_ref_sig_restrict                funpre
% 7.65/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.52  --abstr_ref_under                       []
% 7.65/1.52  
% 7.65/1.52  ------ SAT Options
% 7.65/1.52  
% 7.65/1.52  --sat_mode                              false
% 7.65/1.52  --sat_fm_restart_options                ""
% 7.65/1.52  --sat_gr_def                            false
% 7.65/1.52  --sat_epr_types                         true
% 7.65/1.52  --sat_non_cyclic_types                  false
% 7.65/1.52  --sat_finite_models                     false
% 7.65/1.52  --sat_fm_lemmas                         false
% 7.65/1.52  --sat_fm_prep                           false
% 7.65/1.52  --sat_fm_uc_incr                        true
% 7.65/1.52  --sat_out_model                         small
% 7.65/1.52  --sat_out_clauses                       false
% 7.65/1.52  
% 7.65/1.52  ------ QBF Options
% 7.65/1.52  
% 7.65/1.52  --qbf_mode                              false
% 7.65/1.52  --qbf_elim_univ                         false
% 7.65/1.52  --qbf_dom_inst                          none
% 7.65/1.52  --qbf_dom_pre_inst                      false
% 7.65/1.52  --qbf_sk_in                             false
% 7.65/1.52  --qbf_pred_elim                         true
% 7.65/1.52  --qbf_split                             512
% 7.65/1.52  
% 7.65/1.52  ------ BMC1 Options
% 7.65/1.52  
% 7.65/1.52  --bmc1_incremental                      false
% 7.65/1.52  --bmc1_axioms                           reachable_all
% 7.65/1.52  --bmc1_min_bound                        0
% 7.65/1.52  --bmc1_max_bound                        -1
% 7.65/1.52  --bmc1_max_bound_default                -1
% 7.65/1.52  --bmc1_symbol_reachability              true
% 7.65/1.52  --bmc1_property_lemmas                  false
% 7.65/1.52  --bmc1_k_induction                      false
% 7.65/1.52  --bmc1_non_equiv_states                 false
% 7.65/1.52  --bmc1_deadlock                         false
% 7.65/1.52  --bmc1_ucm                              false
% 7.65/1.52  --bmc1_add_unsat_core                   none
% 7.65/1.52  --bmc1_unsat_core_children              false
% 7.65/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.52  --bmc1_out_stat                         full
% 7.65/1.52  --bmc1_ground_init                      false
% 7.65/1.52  --bmc1_pre_inst_next_state              false
% 7.65/1.52  --bmc1_pre_inst_state                   false
% 7.65/1.52  --bmc1_pre_inst_reach_state             false
% 7.65/1.52  --bmc1_out_unsat_core                   false
% 7.65/1.52  --bmc1_aig_witness_out                  false
% 7.65/1.52  --bmc1_verbose                          false
% 7.65/1.52  --bmc1_dump_clauses_tptp                false
% 7.65/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.52  --bmc1_dump_file                        -
% 7.65/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.52  --bmc1_ucm_extend_mode                  1
% 7.65/1.52  --bmc1_ucm_init_mode                    2
% 7.65/1.52  --bmc1_ucm_cone_mode                    none
% 7.65/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.52  --bmc1_ucm_relax_model                  4
% 7.65/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.52  --bmc1_ucm_layered_model                none
% 7.65/1.52  --bmc1_ucm_max_lemma_size               10
% 7.65/1.52  
% 7.65/1.52  ------ AIG Options
% 7.65/1.52  
% 7.65/1.52  --aig_mode                              false
% 7.65/1.52  
% 7.65/1.52  ------ Instantiation Options
% 7.65/1.52  
% 7.65/1.52  --instantiation_flag                    true
% 7.65/1.52  --inst_sos_flag                         true
% 7.65/1.52  --inst_sos_phase                        true
% 7.65/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.52  --inst_lit_sel_side                     none
% 7.65/1.52  --inst_solver_per_active                1400
% 7.65/1.52  --inst_solver_calls_frac                1.
% 7.65/1.52  --inst_passive_queue_type               priority_queues
% 7.65/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.52  --inst_passive_queues_freq              [25;2]
% 7.65/1.52  --inst_dismatching                      true
% 7.65/1.52  --inst_eager_unprocessed_to_passive     true
% 7.65/1.52  --inst_prop_sim_given                   true
% 7.65/1.52  --inst_prop_sim_new                     false
% 7.65/1.52  --inst_subs_new                         false
% 7.65/1.52  --inst_eq_res_simp                      false
% 7.65/1.52  --inst_subs_given                       false
% 7.65/1.52  --inst_orphan_elimination               true
% 7.65/1.52  --inst_learning_loop_flag               true
% 7.65/1.52  --inst_learning_start                   3000
% 7.65/1.52  --inst_learning_factor                  2
% 7.65/1.52  --inst_start_prop_sim_after_learn       3
% 7.65/1.52  --inst_sel_renew                        solver
% 7.65/1.52  --inst_lit_activity_flag                true
% 7.65/1.52  --inst_restr_to_given                   false
% 7.65/1.52  --inst_activity_threshold               500
% 7.65/1.52  --inst_out_proof                        true
% 7.65/1.52  
% 7.65/1.52  ------ Resolution Options
% 7.65/1.52  
% 7.65/1.52  --resolution_flag                       false
% 7.65/1.52  --res_lit_sel                           adaptive
% 7.65/1.52  --res_lit_sel_side                      none
% 7.65/1.52  --res_ordering                          kbo
% 7.65/1.52  --res_to_prop_solver                    active
% 7.65/1.52  --res_prop_simpl_new                    false
% 7.65/1.52  --res_prop_simpl_given                  true
% 7.65/1.52  --res_passive_queue_type                priority_queues
% 7.65/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.52  --res_passive_queues_freq               [15;5]
% 7.65/1.52  --res_forward_subs                      full
% 7.65/1.52  --res_backward_subs                     full
% 7.65/1.52  --res_forward_subs_resolution           true
% 7.65/1.52  --res_backward_subs_resolution          true
% 7.65/1.52  --res_orphan_elimination                true
% 7.65/1.52  --res_time_limit                        2.
% 7.65/1.52  --res_out_proof                         true
% 7.65/1.52  
% 7.65/1.52  ------ Superposition Options
% 7.65/1.52  
% 7.65/1.52  --superposition_flag                    true
% 7.65/1.52  --sup_passive_queue_type                priority_queues
% 7.65/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.52  --demod_completeness_check              fast
% 7.65/1.52  --demod_use_ground                      true
% 7.65/1.52  --sup_to_prop_solver                    passive
% 7.65/1.52  --sup_prop_simpl_new                    true
% 7.65/1.52  --sup_prop_simpl_given                  true
% 7.65/1.52  --sup_fun_splitting                     true
% 7.65/1.52  --sup_smt_interval                      50000
% 7.65/1.52  
% 7.65/1.52  ------ Superposition Simplification Setup
% 7.65/1.52  
% 7.65/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.65/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.65/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.65/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.65/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.65/1.52  --sup_immed_triv                        [TrivRules]
% 7.65/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.52  --sup_immed_bw_main                     []
% 7.65/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.65/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.52  --sup_input_bw                          []
% 7.65/1.52  
% 7.65/1.52  ------ Combination Options
% 7.65/1.52  
% 7.65/1.52  --comb_res_mult                         3
% 7.65/1.52  --comb_sup_mult                         2
% 7.65/1.52  --comb_inst_mult                        10
% 7.65/1.52  
% 7.65/1.52  ------ Debug Options
% 7.65/1.52  
% 7.65/1.52  --dbg_backtrace                         false
% 7.65/1.52  --dbg_dump_prop_clauses                 false
% 7.65/1.52  --dbg_dump_prop_clauses_file            -
% 7.65/1.52  --dbg_out_stat                          false
% 7.65/1.52  
% 7.65/1.52  
% 7.65/1.52  
% 7.65/1.52  
% 7.65/1.52  ------ Proving...
% 7.65/1.52  
% 7.65/1.52  
% 7.65/1.52  % SZS status Theorem for theBenchmark.p
% 7.65/1.52  
% 7.65/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.52  
% 7.65/1.52  fof(f22,conjecture,(
% 7.65/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f23,negated_conjecture,(
% 7.65/1.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.65/1.52    inference(negated_conjecture,[],[f22])).
% 7.65/1.52  
% 7.65/1.52  fof(f24,plain,(
% 7.65/1.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.65/1.52    inference(pure_predicate_removal,[],[f23])).
% 7.65/1.52  
% 7.65/1.52  fof(f52,plain,(
% 7.65/1.52    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 7.65/1.52    inference(ennf_transformation,[],[f24])).
% 7.65/1.52  
% 7.65/1.52  fof(f53,plain,(
% 7.65/1.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 7.65/1.52    inference(flattening,[],[f52])).
% 7.65/1.52  
% 7.65/1.52  fof(f57,plain,(
% 7.65/1.52    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 7.65/1.52    introduced(choice_axiom,[])).
% 7.65/1.52  
% 7.65/1.52  fof(f56,plain,(
% 7.65/1.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 7.65/1.52    introduced(choice_axiom,[])).
% 7.65/1.52  
% 7.65/1.52  fof(f58,plain,(
% 7.65/1.52    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 7.65/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f57,f56])).
% 7.65/1.52  
% 7.65/1.52  fof(f90,plain,(
% 7.65/1.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.65/1.52    inference(cnf_transformation,[],[f58])).
% 7.65/1.52  
% 7.65/1.52  fof(f1,axiom,(
% 7.65/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f26,plain,(
% 7.65/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.65/1.52    inference(ennf_transformation,[],[f1])).
% 7.65/1.52  
% 7.65/1.52  fof(f59,plain,(
% 7.65/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f26])).
% 7.65/1.52  
% 7.65/1.52  fof(f3,axiom,(
% 7.65/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f62,plain,(
% 7.65/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.65/1.52    inference(cnf_transformation,[],[f3])).
% 7.65/1.52  
% 7.65/1.52  fof(f88,plain,(
% 7.65/1.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.65/1.52    inference(cnf_transformation,[],[f58])).
% 7.65/1.52  
% 7.65/1.52  fof(f87,plain,(
% 7.65/1.52    v1_funct_1(sK2)),
% 7.65/1.52    inference(cnf_transformation,[],[f58])).
% 7.65/1.52  
% 7.65/1.52  fof(f11,axiom,(
% 7.65/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f36,plain,(
% 7.65/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.52    inference(ennf_transformation,[],[f11])).
% 7.65/1.52  
% 7.65/1.52  fof(f37,plain,(
% 7.65/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.52    inference(flattening,[],[f36])).
% 7.65/1.52  
% 7.65/1.52  fof(f71,plain,(
% 7.65/1.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f37])).
% 7.65/1.52  
% 7.65/1.52  fof(f7,axiom,(
% 7.65/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f32,plain,(
% 7.65/1.52    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.65/1.52    inference(ennf_transformation,[],[f7])).
% 7.65/1.52  
% 7.65/1.52  fof(f66,plain,(
% 7.65/1.52    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f32])).
% 7.65/1.52  
% 7.65/1.52  fof(f16,axiom,(
% 7.65/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f45,plain,(
% 7.65/1.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.52    inference(ennf_transformation,[],[f16])).
% 7.65/1.52  
% 7.65/1.52  fof(f79,plain,(
% 7.65/1.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.52    inference(cnf_transformation,[],[f45])).
% 7.65/1.52  
% 7.65/1.52  fof(f91,plain,(
% 7.65/1.52    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.65/1.52    inference(cnf_transformation,[],[f58])).
% 7.65/1.52  
% 7.65/1.52  fof(f14,axiom,(
% 7.65/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f42,plain,(
% 7.65/1.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.52    inference(ennf_transformation,[],[f14])).
% 7.65/1.52  
% 7.65/1.52  fof(f43,plain,(
% 7.65/1.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.52    inference(flattening,[],[f42])).
% 7.65/1.52  
% 7.65/1.52  fof(f77,plain,(
% 7.65/1.52    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f43])).
% 7.65/1.52  
% 7.65/1.52  fof(f21,axiom,(
% 7.65/1.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f86,plain,(
% 7.65/1.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f21])).
% 7.65/1.52  
% 7.65/1.52  fof(f101,plain,(
% 7.65/1.52    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.52    inference(definition_unfolding,[],[f77,f86])).
% 7.65/1.52  
% 7.65/1.52  fof(f93,plain,(
% 7.65/1.52    v2_funct_1(sK2)),
% 7.65/1.52    inference(cnf_transformation,[],[f58])).
% 7.65/1.52  
% 7.65/1.52  fof(f20,axiom,(
% 7.65/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f50,plain,(
% 7.65/1.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.65/1.52    inference(ennf_transformation,[],[f20])).
% 7.65/1.52  
% 7.65/1.52  fof(f51,plain,(
% 7.65/1.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.65/1.52    inference(flattening,[],[f50])).
% 7.65/1.52  
% 7.65/1.52  fof(f85,plain,(
% 7.65/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f51])).
% 7.65/1.52  
% 7.65/1.52  fof(f89,plain,(
% 7.65/1.52    v1_funct_1(sK3)),
% 7.65/1.52    inference(cnf_transformation,[],[f58])).
% 7.65/1.52  
% 7.65/1.52  fof(f17,axiom,(
% 7.65/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f46,plain,(
% 7.65/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.65/1.52    inference(ennf_transformation,[],[f17])).
% 7.65/1.52  
% 7.65/1.52  fof(f47,plain,(
% 7.65/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.52    inference(flattening,[],[f46])).
% 7.65/1.52  
% 7.65/1.52  fof(f55,plain,(
% 7.65/1.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.52    inference(nnf_transformation,[],[f47])).
% 7.65/1.52  
% 7.65/1.52  fof(f80,plain,(
% 7.65/1.52    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.52    inference(cnf_transformation,[],[f55])).
% 7.65/1.52  
% 7.65/1.52  fof(f92,plain,(
% 7.65/1.52    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.65/1.52    inference(cnf_transformation,[],[f58])).
% 7.65/1.52  
% 7.65/1.52  fof(f18,axiom,(
% 7.65/1.52    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f82,plain,(
% 7.65/1.52    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.65/1.52    inference(cnf_transformation,[],[f18])).
% 7.65/1.52  
% 7.65/1.52  fof(f103,plain,(
% 7.65/1.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.65/1.52    inference(definition_unfolding,[],[f82,f86])).
% 7.65/1.52  
% 7.65/1.52  fof(f19,axiom,(
% 7.65/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f48,plain,(
% 7.65/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.65/1.52    inference(ennf_transformation,[],[f19])).
% 7.65/1.52  
% 7.65/1.52  fof(f49,plain,(
% 7.65/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.65/1.52    inference(flattening,[],[f48])).
% 7.65/1.52  
% 7.65/1.52  fof(f84,plain,(
% 7.65/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f49])).
% 7.65/1.52  
% 7.65/1.52  fof(f15,axiom,(
% 7.65/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f25,plain,(
% 7.65/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.65/1.52    inference(pure_predicate_removal,[],[f15])).
% 7.65/1.52  
% 7.65/1.52  fof(f44,plain,(
% 7.65/1.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.52    inference(ennf_transformation,[],[f25])).
% 7.65/1.52  
% 7.65/1.52  fof(f78,plain,(
% 7.65/1.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.52    inference(cnf_transformation,[],[f44])).
% 7.65/1.52  
% 7.65/1.52  fof(f2,axiom,(
% 7.65/1.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f27,plain,(
% 7.65/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.65/1.52    inference(ennf_transformation,[],[f2])).
% 7.65/1.52  
% 7.65/1.52  fof(f54,plain,(
% 7.65/1.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.65/1.52    inference(nnf_transformation,[],[f27])).
% 7.65/1.52  
% 7.65/1.52  fof(f60,plain,(
% 7.65/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f54])).
% 7.65/1.52  
% 7.65/1.52  fof(f12,axiom,(
% 7.65/1.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f38,plain,(
% 7.65/1.52    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.65/1.52    inference(ennf_transformation,[],[f12])).
% 7.65/1.52  
% 7.65/1.52  fof(f39,plain,(
% 7.65/1.52    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.65/1.52    inference(flattening,[],[f38])).
% 7.65/1.52  
% 7.65/1.52  fof(f73,plain,(
% 7.65/1.52    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f39])).
% 7.65/1.52  
% 7.65/1.52  fof(f6,axiom,(
% 7.65/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f30,plain,(
% 7.65/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.65/1.52    inference(ennf_transformation,[],[f6])).
% 7.65/1.52  
% 7.65/1.52  fof(f31,plain,(
% 7.65/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.65/1.52    inference(flattening,[],[f30])).
% 7.65/1.52  
% 7.65/1.52  fof(f65,plain,(
% 7.65/1.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f31])).
% 7.65/1.52  
% 7.65/1.52  fof(f4,axiom,(
% 7.65/1.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f28,plain,(
% 7.65/1.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.65/1.52    inference(ennf_transformation,[],[f4])).
% 7.65/1.52  
% 7.65/1.52  fof(f63,plain,(
% 7.65/1.52    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f28])).
% 7.65/1.52  
% 7.65/1.52  fof(f5,axiom,(
% 7.65/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f29,plain,(
% 7.65/1.52    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.65/1.52    inference(ennf_transformation,[],[f5])).
% 7.65/1.52  
% 7.65/1.52  fof(f64,plain,(
% 7.65/1.52    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f29])).
% 7.65/1.52  
% 7.65/1.52  fof(f8,axiom,(
% 7.65/1.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f67,plain,(
% 7.65/1.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.65/1.52    inference(cnf_transformation,[],[f8])).
% 7.65/1.52  
% 7.65/1.52  fof(f98,plain,(
% 7.65/1.52    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 7.65/1.52    inference(definition_unfolding,[],[f67,f86])).
% 7.65/1.52  
% 7.65/1.52  fof(f9,axiom,(
% 7.65/1.52    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f33,plain,(
% 7.65/1.52    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 7.65/1.52    inference(ennf_transformation,[],[f9])).
% 7.65/1.52  
% 7.65/1.52  fof(f69,plain,(
% 7.65/1.52    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f33])).
% 7.65/1.52  
% 7.65/1.52  fof(f99,plain,(
% 7.65/1.52    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.65/1.52    inference(definition_unfolding,[],[f69,f86])).
% 7.65/1.52  
% 7.65/1.52  fof(f13,axiom,(
% 7.65/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f40,plain,(
% 7.65/1.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.52    inference(ennf_transformation,[],[f13])).
% 7.65/1.52  
% 7.65/1.52  fof(f41,plain,(
% 7.65/1.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.52    inference(flattening,[],[f40])).
% 7.65/1.52  
% 7.65/1.52  fof(f75,plain,(
% 7.65/1.52    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f41])).
% 7.65/1.52  
% 7.65/1.52  fof(f10,axiom,(
% 7.65/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.65/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.52  
% 7.65/1.52  fof(f34,plain,(
% 7.65/1.52    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.65/1.52    inference(ennf_transformation,[],[f10])).
% 7.65/1.52  
% 7.65/1.52  fof(f35,plain,(
% 7.65/1.52    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.65/1.52    inference(flattening,[],[f34])).
% 7.65/1.52  
% 7.65/1.52  fof(f70,plain,(
% 7.65/1.52    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.65/1.52    inference(cnf_transformation,[],[f35])).
% 7.65/1.52  
% 7.65/1.52  fof(f100,plain,(
% 7.65/1.52    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.65/1.52    inference(definition_unfolding,[],[f70,f86])).
% 7.65/1.52  
% 7.65/1.52  fof(f96,plain,(
% 7.65/1.52    k2_funct_1(sK2) != sK3),
% 7.65/1.52    inference(cnf_transformation,[],[f58])).
% 7.65/1.52  
% 7.65/1.52  cnf(c_33,negated_conjecture,
% 7.65/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.65/1.52      inference(cnf_transformation,[],[f90]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1324,plain,
% 7.65/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_0,plain,
% 7.65/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.65/1.52      | ~ v1_relat_1(X1)
% 7.65/1.52      | v1_relat_1(X0) ),
% 7.65/1.52      inference(cnf_transformation,[],[f59]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1343,plain,
% 7.65/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.65/1.52      | v1_relat_1(X1) != iProver_top
% 7.65/1.52      | v1_relat_1(X0) = iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_3221,plain,
% 7.65/1.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.65/1.52      | v1_relat_1(sK3) = iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_1324,c_1343]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_40,plain,
% 7.65/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1452,plain,
% 7.65/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.52      | v1_relat_1(X0)
% 7.65/1.52      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.65/1.52      inference(instantiation,[status(thm)],[c_0]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1517,plain,
% 7.65/1.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.65/1.52      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 7.65/1.52      | v1_relat_1(sK3) ),
% 7.65/1.52      inference(instantiation,[status(thm)],[c_1452]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1518,plain,
% 7.65/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.65/1.52      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.65/1.52      | v1_relat_1(sK3) = iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_1517]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_3,plain,
% 7.65/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.65/1.52      inference(cnf_transformation,[],[f62]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1597,plain,
% 7.65/1.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 7.65/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1598,plain,
% 7.65/1.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_1597]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_3229,plain,
% 7.65/1.52      ( v1_relat_1(sK3) = iProver_top ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_3221,c_40,c_1518,c_1598]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_35,negated_conjecture,
% 7.65/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.65/1.52      inference(cnf_transformation,[],[f88]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1322,plain,
% 7.65/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_3222,plain,
% 7.65/1.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.65/1.52      | v1_relat_1(sK2) = iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_1322,c_1343]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_38,plain,
% 7.65/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1398,plain,
% 7.65/1.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 7.65/1.52      | ~ v1_relat_1(X0)
% 7.65/1.52      | v1_relat_1(sK2) ),
% 7.65/1.52      inference(instantiation,[status(thm)],[c_0]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1434,plain,
% 7.65/1.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.52      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 7.65/1.52      | v1_relat_1(sK2) ),
% 7.65/1.52      inference(instantiation,[status(thm)],[c_1398]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1486,plain,
% 7.65/1.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.65/1.52      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.65/1.52      | v1_relat_1(sK2) ),
% 7.65/1.52      inference(instantiation,[status(thm)],[c_1434]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1487,plain,
% 7.65/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.65/1.52      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.65/1.52      | v1_relat_1(sK2) = iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1594,plain,
% 7.65/1.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.65/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1595,plain,
% 7.65/1.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_1594]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_3445,plain,
% 7.65/1.52      ( v1_relat_1(sK2) = iProver_top ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_3222,c_38,c_1487,c_1595]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_36,negated_conjecture,
% 7.65/1.52      ( v1_funct_1(sK2) ),
% 7.65/1.52      inference(cnf_transformation,[],[f87]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1321,plain,
% 7.65/1.52      ( v1_funct_1(sK2) = iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_13,plain,
% 7.65/1.52      ( ~ v1_funct_1(X0)
% 7.65/1.52      | ~ v1_relat_1(X0)
% 7.65/1.52      | v1_relat_1(k2_funct_1(X0)) ),
% 7.65/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1332,plain,
% 7.65/1.52      ( v1_funct_1(X0) != iProver_top
% 7.65/1.52      | v1_relat_1(X0) != iProver_top
% 7.65/1.52      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_7,plain,
% 7.65/1.52      ( ~ v1_relat_1(X0)
% 7.65/1.52      | ~ v1_relat_1(X1)
% 7.65/1.52      | ~ v1_relat_1(X2)
% 7.65/1.52      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 7.65/1.52      inference(cnf_transformation,[],[f66]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1336,plain,
% 7.65/1.52      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.65/1.52      | v1_relat_1(X0) != iProver_top
% 7.65/1.52      | v1_relat_1(X1) != iProver_top
% 7.65/1.52      | v1_relat_1(X2) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_5178,plain,
% 7.65/1.52      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 7.65/1.52      | v1_funct_1(X0) != iProver_top
% 7.65/1.52      | v1_relat_1(X0) != iProver_top
% 7.65/1.52      | v1_relat_1(X1) != iProver_top
% 7.65/1.52      | v1_relat_1(X2) != iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_1332,c_1336]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_20598,plain,
% 7.65/1.52      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.65/1.52      | v1_relat_1(X0) != iProver_top
% 7.65/1.52      | v1_relat_1(X1) != iProver_top
% 7.65/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_1321,c_5178]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_20983,plain,
% 7.65/1.52      ( v1_relat_1(X1) != iProver_top
% 7.65/1.52      | v1_relat_1(X0) != iProver_top
% 7.65/1.52      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_20598,c_38,c_1487,c_1595]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_20984,plain,
% 7.65/1.52      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.65/1.52      | v1_relat_1(X0) != iProver_top
% 7.65/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.65/1.52      inference(renaming,[status(thm)],[c_20983]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_20991,plain,
% 7.65/1.52      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 7.65/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_3445,c_20984]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_20,plain,
% 7.65/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.65/1.52      inference(cnf_transformation,[],[f79]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1329,plain,
% 7.65/1.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.65/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2249,plain,
% 7.65/1.52      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_1322,c_1329]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_32,negated_conjecture,
% 7.65/1.52      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.65/1.52      inference(cnf_transformation,[],[f91]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2250,plain,
% 7.65/1.52      ( k2_relat_1(sK2) = sK1 ),
% 7.65/1.52      inference(light_normalisation,[status(thm)],[c_2249,c_32]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_17,plain,
% 7.65/1.52      ( ~ v2_funct_1(X0)
% 7.65/1.52      | ~ v1_funct_1(X0)
% 7.65/1.52      | ~ v1_relat_1(X0)
% 7.65/1.52      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 7.65/1.52      inference(cnf_transformation,[],[f101]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_30,negated_conjecture,
% 7.65/1.52      ( v2_funct_1(sK2) ),
% 7.65/1.52      inference(cnf_transformation,[],[f93]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_393,plain,
% 7.65/1.52      ( ~ v1_funct_1(X0)
% 7.65/1.52      | ~ v1_relat_1(X0)
% 7.65/1.52      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 7.65/1.52      | sK2 != X0 ),
% 7.65/1.52      inference(resolution_lifted,[status(thm)],[c_17,c_30]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_394,plain,
% 7.65/1.52      ( ~ v1_funct_1(sK2)
% 7.65/1.52      | ~ v1_relat_1(sK2)
% 7.65/1.52      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.65/1.52      inference(unflattening,[status(thm)],[c_393]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_396,plain,
% 7.65/1.52      ( ~ v1_relat_1(sK2)
% 7.65/1.52      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_394,c_36]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1318,plain,
% 7.65/1.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 7.65/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1953,plain,
% 7.65/1.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_1318,c_36,c_35,c_394,c_1486,c_1594]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2320,plain,
% 7.65/1.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.65/1.52      inference(demodulation,[status(thm)],[c_2250,c_1953]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_21002,plain,
% 7.65/1.52      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.65/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.52      inference(light_normalisation,[status(thm)],[c_20991,c_2320]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_21076,plain,
% 7.65/1.52      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_3229,c_21002]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_26,plain,
% 7.65/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.65/1.52      | ~ v1_funct_1(X0)
% 7.65/1.52      | ~ v1_funct_1(X3)
% 7.65/1.52      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.65/1.52      inference(cnf_transformation,[],[f85]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1325,plain,
% 7.65/1.52      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.65/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.65/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.52      | v1_funct_1(X5) != iProver_top
% 7.65/1.52      | v1_funct_1(X4) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2194,plain,
% 7.65/1.52      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.65/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.52      | v1_funct_1(X2) != iProver_top
% 7.65/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_1324,c_1325]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_34,negated_conjecture,
% 7.65/1.52      ( v1_funct_1(sK3) ),
% 7.65/1.52      inference(cnf_transformation,[],[f89]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_39,plain,
% 7.65/1.52      ( v1_funct_1(sK3) = iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2825,plain,
% 7.65/1.52      ( v1_funct_1(X2) != iProver_top
% 7.65/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.52      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_2194,c_39]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2826,plain,
% 7.65/1.52      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.65/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.65/1.52      inference(renaming,[status(thm)],[c_2825]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2833,plain,
% 7.65/1.52      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.65/1.52      | v1_funct_1(sK2) != iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_1322,c_2826]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_22,plain,
% 7.65/1.52      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.65/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.52      | X3 = X2 ),
% 7.65/1.52      inference(cnf_transformation,[],[f80]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_31,negated_conjecture,
% 7.65/1.52      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.65/1.52      inference(cnf_transformation,[],[f92]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_362,plain,
% 7.65/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.52      | X3 = X0
% 7.65/1.52      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.65/1.52      | k6_partfun1(sK0) != X3
% 7.65/1.52      | sK0 != X2
% 7.65/1.52      | sK0 != X1 ),
% 7.65/1.52      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_363,plain,
% 7.65/1.52      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.65/1.52      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.65/1.52      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.65/1.52      inference(unflattening,[status(thm)],[c_362]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_23,plain,
% 7.65/1.52      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.65/1.52      inference(cnf_transformation,[],[f103]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_53,plain,
% 7.65/1.52      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.65/1.52      inference(instantiation,[status(thm)],[c_23]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_365,plain,
% 7.65/1.52      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.65/1.52      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_363,c_53]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1320,plain,
% 7.65/1.52      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.65/1.52      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_24,plain,
% 7.65/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.65/1.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.65/1.52      | ~ v1_funct_1(X0)
% 7.65/1.52      | ~ v1_funct_1(X3) ),
% 7.65/1.52      inference(cnf_transformation,[],[f84]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1385,plain,
% 7.65/1.52      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.65/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.65/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.65/1.52      | ~ v1_funct_1(sK3)
% 7.65/1.52      | ~ v1_funct_1(sK2) ),
% 7.65/1.52      inference(instantiation,[status(thm)],[c_24]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2046,plain,
% 7.65/1.52      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_1320,c_36,c_35,c_34,c_33,c_53,c_363,c_1385]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2834,plain,
% 7.65/1.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.65/1.52      | v1_funct_1(sK2) != iProver_top ),
% 7.65/1.52      inference(light_normalisation,[status(thm)],[c_2833,c_2046]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_37,plain,
% 7.65/1.52      ( v1_funct_1(sK2) = iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_4402,plain,
% 7.65/1.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_2834,c_37]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_19,plain,
% 7.65/1.52      ( v4_relat_1(X0,X1)
% 7.65/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.65/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1330,plain,
% 7.65/1.52      ( v4_relat_1(X0,X1) = iProver_top
% 7.65/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2239,plain,
% 7.65/1.52      ( v4_relat_1(sK3,sK1) = iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_1324,c_1330]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2,plain,
% 7.65/1.52      ( r1_tarski(k1_relat_1(X0),X1)
% 7.65/1.52      | ~ v4_relat_1(X0,X1)
% 7.65/1.52      | ~ v1_relat_1(X0) ),
% 7.65/1.52      inference(cnf_transformation,[],[f60]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1341,plain,
% 7.65/1.52      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.65/1.52      | v4_relat_1(X0,X1) != iProver_top
% 7.65/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_14,plain,
% 7.65/1.52      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 7.65/1.52      | ~ v1_funct_1(X1)
% 7.65/1.52      | ~ v1_relat_1(X1)
% 7.65/1.52      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 7.65/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1331,plain,
% 7.65/1.52      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 7.65/1.52      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 7.65/1.52      | v1_funct_1(X0) != iProver_top
% 7.65/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_4655,plain,
% 7.65/1.52      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 7.65/1.52      | r1_tarski(X0,sK1) != iProver_top
% 7.65/1.52      | v1_funct_1(sK2) != iProver_top
% 7.65/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_2250,c_1331]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_5194,plain,
% 7.65/1.52      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 7.65/1.52      | r1_tarski(X0,sK1) != iProver_top ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_4655,c_37,c_38,c_1487,c_1595]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_5200,plain,
% 7.65/1.52      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
% 7.65/1.52      | v4_relat_1(X0,sK1) != iProver_top
% 7.65/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_1341,c_5194]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_6368,plain,
% 7.65/1.52      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3)
% 7.65/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_2239,c_5200]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2240,plain,
% 7.65/1.52      ( v4_relat_1(sK2,sK0) = iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_1322,c_1330]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_6,plain,
% 7.65/1.52      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.65/1.52      inference(cnf_transformation,[],[f65]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1337,plain,
% 7.65/1.52      ( k7_relat_1(X0,X1) = X0
% 7.65/1.52      | v4_relat_1(X0,X1) != iProver_top
% 7.65/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_3162,plain,
% 7.65/1.52      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_2240,c_1337]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2094,plain,
% 7.65/1.52      ( ~ v4_relat_1(sK2,X0)
% 7.65/1.52      | ~ v1_relat_1(sK2)
% 7.65/1.52      | k7_relat_1(sK2,X0) = sK2 ),
% 7.65/1.52      inference(instantiation,[status(thm)],[c_6]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2095,plain,
% 7.65/1.52      ( k7_relat_1(sK2,X0) = sK2
% 7.65/1.52      | v4_relat_1(sK2,X0) != iProver_top
% 7.65/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_2094]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_2097,plain,
% 7.65/1.52      ( k7_relat_1(sK2,sK0) = sK2
% 7.65/1.52      | v4_relat_1(sK2,sK0) != iProver_top
% 7.65/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.52      inference(instantiation,[status(thm)],[c_2095]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_4003,plain,
% 7.65/1.52      ( k7_relat_1(sK2,sK0) = sK2 ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_3162,c_38,c_1487,c_1595,c_2097,c_2240]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_4,plain,
% 7.65/1.52      ( ~ v1_relat_1(X0)
% 7.65/1.52      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.65/1.52      inference(cnf_transformation,[],[f63]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1339,plain,
% 7.65/1.52      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.65/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_3449,plain,
% 7.65/1.52      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_3445,c_1339]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_4005,plain,
% 7.65/1.52      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_4003,c_3449]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_4006,plain,
% 7.65/1.52      ( k9_relat_1(sK2,sK0) = sK1 ),
% 7.65/1.52      inference(light_normalisation,[status(thm)],[c_4005,c_2250]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_5,plain,
% 7.65/1.52      ( ~ v1_relat_1(X0)
% 7.65/1.52      | ~ v1_relat_1(X1)
% 7.65/1.52      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 7.65/1.52      inference(cnf_transformation,[],[f64]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1338,plain,
% 7.65/1.52      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 7.65/1.52      | v1_relat_1(X0) != iProver_top
% 7.65/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_4944,plain,
% 7.65/1.52      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 7.65/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_3445,c_1338]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_5342,plain,
% 7.65/1.52      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_3229,c_4944]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_5343,plain,
% 7.65/1.52      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
% 7.65/1.52      inference(light_normalisation,[status(thm)],[c_5342,c_4402]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_9,plain,
% 7.65/1.52      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.65/1.52      inference(cnf_transformation,[],[f98]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_5344,plain,
% 7.65/1.52      ( k10_relat_1(sK2,k1_relat_1(sK3)) = sK0 ),
% 7.65/1.52      inference(demodulation,[status(thm)],[c_5343,c_9]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_6373,plain,
% 7.65/1.52      ( k1_relat_1(sK3) = sK1 | v1_relat_1(sK3) != iProver_top ),
% 7.65/1.52      inference(light_normalisation,[status(thm)],[c_6368,c_4006,c_5344]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_6623,plain,
% 7.65/1.52      ( k1_relat_1(sK3) = sK1 ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_6373,c_40,c_1518,c_1598]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_10,plain,
% 7.65/1.52      ( ~ v1_relat_1(X0)
% 7.65/1.52      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 7.65/1.52      inference(cnf_transformation,[],[f99]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1335,plain,
% 7.65/1.52      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 7.65/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_3234,plain,
% 7.65/1.52      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_3229,c_1335]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_6627,plain,
% 7.65/1.52      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 7.65/1.52      inference(demodulation,[status(thm)],[c_6623,c_3234]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_15,plain,
% 7.65/1.52      ( ~ v2_funct_1(X0)
% 7.65/1.52      | ~ v1_funct_1(X0)
% 7.65/1.52      | ~ v1_relat_1(X0)
% 7.65/1.52      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.65/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_421,plain,
% 7.65/1.52      ( ~ v1_funct_1(X0)
% 7.65/1.52      | ~ v1_relat_1(X0)
% 7.65/1.52      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.65/1.52      | sK2 != X0 ),
% 7.65/1.52      inference(resolution_lifted,[status(thm)],[c_15,c_30]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_422,plain,
% 7.65/1.52      ( ~ v1_funct_1(sK2)
% 7.65/1.52      | ~ v1_relat_1(sK2)
% 7.65/1.52      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.65/1.52      inference(unflattening,[status(thm)],[c_421]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_424,plain,
% 7.65/1.52      ( ~ v1_relat_1(sK2)
% 7.65/1.52      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_422,c_36]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1316,plain,
% 7.65/1.52      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.65/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1632,plain,
% 7.65/1.52      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_1316,c_36,c_35,c_422,c_1486,c_1594]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_11,plain,
% 7.65/1.52      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.65/1.52      | ~ v1_relat_1(X0)
% 7.65/1.52      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 7.65/1.52      inference(cnf_transformation,[],[f100]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1334,plain,
% 7.65/1.52      ( k5_relat_1(X0,k6_partfun1(X1)) = X0
% 7.65/1.52      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.65/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_3956,plain,
% 7.65/1.52      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 7.65/1.52      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 7.65/1.52      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_1632,c_1334]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1500,plain,
% 7.65/1.52      ( ~ v1_funct_1(sK2)
% 7.65/1.52      | v1_relat_1(k2_funct_1(sK2))
% 7.65/1.52      | ~ v1_relat_1(sK2) ),
% 7.65/1.52      inference(instantiation,[status(thm)],[c_13]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_1501,plain,
% 7.65/1.52      ( v1_funct_1(sK2) != iProver_top
% 7.65/1.52      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 7.65/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.52      inference(predicate_to_equality,[status(thm)],[c_1500]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_6637,plain,
% 7.65/1.52      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 7.65/1.52      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_3956,c_37,c_38,c_1487,c_1501,c_1595]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_6638,plain,
% 7.65/1.52      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 7.65/1.52      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 7.65/1.52      inference(renaming,[status(thm)],[c_6637]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_6643,plain,
% 7.65/1.52      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 7.65/1.52      | v4_relat_1(sK2,X0) != iProver_top
% 7.65/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_1341,c_6638]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_18644,plain,
% 7.65/1.52      ( v4_relat_1(sK2,X0) != iProver_top
% 7.65/1.52      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
% 7.65/1.52      inference(global_propositional_subsumption,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_6643,c_38,c_1487,c_1595]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_18645,plain,
% 7.65/1.52      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 7.65/1.52      | v4_relat_1(sK2,X0) != iProver_top ),
% 7.65/1.52      inference(renaming,[status(thm)],[c_18644]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_18650,plain,
% 7.65/1.52      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 7.65/1.52      inference(superposition,[status(thm)],[c_2240,c_18645]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_21086,plain,
% 7.65/1.52      ( k2_funct_1(sK2) = sK3 ),
% 7.65/1.52      inference(light_normalisation,
% 7.65/1.52                [status(thm)],
% 7.65/1.52                [c_21076,c_4402,c_6627,c_18650]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(c_27,negated_conjecture,
% 7.65/1.52      ( k2_funct_1(sK2) != sK3 ),
% 7.65/1.52      inference(cnf_transformation,[],[f96]) ).
% 7.65/1.52  
% 7.65/1.52  cnf(contradiction,plain,
% 7.65/1.52      ( $false ),
% 7.65/1.52      inference(minisat,[status(thm)],[c_21086,c_27]) ).
% 7.65/1.52  
% 7.65/1.52  
% 7.65/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.52  
% 7.65/1.52  ------                               Statistics
% 7.65/1.52  
% 7.65/1.52  ------ General
% 7.65/1.52  
% 7.65/1.52  abstr_ref_over_cycles:                  0
% 7.65/1.52  abstr_ref_under_cycles:                 0
% 7.65/1.52  gc_basic_clause_elim:                   0
% 7.65/1.52  forced_gc_time:                         0
% 7.65/1.52  parsing_time:                           0.008
% 7.65/1.52  unif_index_cands_time:                  0.
% 7.65/1.52  unif_index_add_time:                    0.
% 7.65/1.52  orderings_time:                         0.
% 7.65/1.52  out_proof_time:                         0.018
% 7.65/1.52  total_time:                             0.668
% 7.65/1.52  num_of_symbols:                         55
% 7.65/1.52  num_of_terms:                           31807
% 7.65/1.52  
% 7.65/1.52  ------ Preprocessing
% 7.65/1.52  
% 7.65/1.52  num_of_splits:                          0
% 7.65/1.52  num_of_split_atoms:                     0
% 7.65/1.52  num_of_reused_defs:                     0
% 7.65/1.52  num_eq_ax_congr_red:                    18
% 7.65/1.52  num_of_sem_filtered_clauses:            1
% 7.65/1.52  num_of_subtypes:                        0
% 7.65/1.52  monotx_restored_types:                  0
% 7.65/1.52  sat_num_of_epr_types:                   0
% 7.65/1.52  sat_num_of_non_cyclic_types:            0
% 7.65/1.52  sat_guarded_non_collapsed_types:        0
% 7.65/1.52  num_pure_diseq_elim:                    0
% 7.65/1.52  simp_replaced_by:                       0
% 7.65/1.52  res_preprocessed:                       174
% 7.65/1.52  prep_upred:                             0
% 7.65/1.52  prep_unflattend:                        18
% 7.65/1.52  smt_new_axioms:                         0
% 7.65/1.52  pred_elim_cands:                        5
% 7.65/1.52  pred_elim:                              2
% 7.65/1.52  pred_elim_cl:                           3
% 7.65/1.52  pred_elim_cycles:                       6
% 7.65/1.52  merged_defs:                            0
% 7.65/1.52  merged_defs_ncl:                        0
% 7.65/1.52  bin_hyper_res:                          0
% 7.65/1.52  prep_cycles:                            4
% 7.65/1.52  pred_elim_time:                         0.003
% 7.65/1.52  splitting_time:                         0.
% 7.65/1.52  sem_filter_time:                        0.
% 7.65/1.52  monotx_time:                            0.
% 7.65/1.52  subtype_inf_time:                       0.
% 7.65/1.52  
% 7.65/1.52  ------ Problem properties
% 7.65/1.52  
% 7.65/1.52  clauses:                                34
% 7.65/1.52  conjectures:                            8
% 7.65/1.52  epr:                                    4
% 7.65/1.52  horn:                                   34
% 7.65/1.52  ground:                                 13
% 7.65/1.52  unary:                                  12
% 7.65/1.52  binary:                                 9
% 7.65/1.52  lits:                                   77
% 7.65/1.52  lits_eq:                                20
% 7.65/1.52  fd_pure:                                0
% 7.65/1.52  fd_pseudo:                              0
% 7.65/1.52  fd_cond:                                0
% 7.65/1.52  fd_pseudo_cond:                         0
% 7.65/1.52  ac_symbols:                             0
% 7.65/1.52  
% 7.65/1.52  ------ Propositional Solver
% 7.65/1.52  
% 7.65/1.52  prop_solver_calls:                      33
% 7.65/1.52  prop_fast_solver_calls:                 1867
% 7.65/1.52  smt_solver_calls:                       0
% 7.65/1.52  smt_fast_solver_calls:                  0
% 7.65/1.52  prop_num_of_clauses:                    12589
% 7.65/1.52  prop_preprocess_simplified:             22522
% 7.65/1.52  prop_fo_subsumed:                       232
% 7.65/1.52  prop_solver_time:                       0.
% 7.65/1.52  smt_solver_time:                        0.
% 7.65/1.52  smt_fast_solver_time:                   0.
% 7.65/1.52  prop_fast_solver_time:                  0.
% 7.65/1.52  prop_unsat_core_time:                   0.001
% 7.65/1.52  
% 7.65/1.52  ------ QBF
% 7.65/1.52  
% 7.65/1.52  qbf_q_res:                              0
% 7.65/1.52  qbf_num_tautologies:                    0
% 7.65/1.52  qbf_prep_cycles:                        0
% 7.65/1.52  
% 7.65/1.52  ------ BMC1
% 7.65/1.52  
% 7.65/1.52  bmc1_current_bound:                     -1
% 7.65/1.52  bmc1_last_solved_bound:                 -1
% 7.65/1.52  bmc1_unsat_core_size:                   -1
% 7.65/1.52  bmc1_unsat_core_parents_size:           -1
% 7.65/1.52  bmc1_merge_next_fun:                    0
% 7.65/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.65/1.52  
% 7.65/1.52  ------ Instantiation
% 7.65/1.52  
% 7.65/1.52  inst_num_of_clauses:                    3043
% 7.65/1.52  inst_num_in_passive:                    782
% 7.65/1.52  inst_num_in_active:                     1502
% 7.65/1.52  inst_num_in_unprocessed:                759
% 7.65/1.52  inst_num_of_loops:                      1620
% 7.65/1.52  inst_num_of_learning_restarts:          0
% 7.65/1.52  inst_num_moves_active_passive:          115
% 7.65/1.52  inst_lit_activity:                      0
% 7.65/1.52  inst_lit_activity_moves:                1
% 7.65/1.52  inst_num_tautologies:                   0
% 7.65/1.52  inst_num_prop_implied:                  0
% 7.65/1.52  inst_num_existing_simplified:           0
% 7.65/1.52  inst_num_eq_res_simplified:             0
% 7.65/1.52  inst_num_child_elim:                    0
% 7.65/1.52  inst_num_of_dismatching_blockings:      526
% 7.65/1.52  inst_num_of_non_proper_insts:           2828
% 7.65/1.52  inst_num_of_duplicates:                 0
% 7.65/1.52  inst_inst_num_from_inst_to_res:         0
% 7.65/1.52  inst_dismatching_checking_time:         0.
% 7.65/1.52  
% 7.65/1.52  ------ Resolution
% 7.65/1.52  
% 7.65/1.52  res_num_of_clauses:                     0
% 7.65/1.52  res_num_in_passive:                     0
% 7.65/1.52  res_num_in_active:                      0
% 7.65/1.52  res_num_of_loops:                       178
% 7.65/1.52  res_forward_subset_subsumed:            195
% 7.65/1.52  res_backward_subset_subsumed:           0
% 7.65/1.52  res_forward_subsumed:                   0
% 7.65/1.52  res_backward_subsumed:                  0
% 7.65/1.52  res_forward_subsumption_resolution:     0
% 7.65/1.52  res_backward_subsumption_resolution:    0
% 7.65/1.52  res_clause_to_clause_subsumption:       1877
% 7.65/1.52  res_orphan_elimination:                 0
% 7.65/1.52  res_tautology_del:                      241
% 7.65/1.52  res_num_eq_res_simplified:              0
% 7.65/1.52  res_num_sel_changes:                    0
% 7.65/1.52  res_moves_from_active_to_pass:          0
% 7.65/1.52  
% 7.65/1.52  ------ Superposition
% 7.65/1.52  
% 7.65/1.52  sup_time_total:                         0.
% 7.65/1.52  sup_time_generating:                    0.
% 7.65/1.52  sup_time_sim_full:                      0.
% 7.65/1.52  sup_time_sim_immed:                     0.
% 7.65/1.52  
% 7.65/1.52  sup_num_of_clauses:                     896
% 7.65/1.52  sup_num_in_active:                      306
% 7.65/1.52  sup_num_in_passive:                     590
% 7.65/1.52  sup_num_of_loops:                       323
% 7.65/1.52  sup_fw_superposition:                   617
% 7.65/1.52  sup_bw_superposition:                   375
% 7.65/1.52  sup_immediate_simplified:               280
% 7.65/1.52  sup_given_eliminated:                   1
% 7.65/1.52  comparisons_done:                       0
% 7.65/1.52  comparisons_avoided:                    0
% 7.65/1.52  
% 7.65/1.52  ------ Simplifications
% 7.65/1.52  
% 7.65/1.52  
% 7.65/1.52  sim_fw_subset_subsumed:                 6
% 7.65/1.52  sim_bw_subset_subsumed:                 43
% 7.65/1.52  sim_fw_subsumed:                        14
% 7.65/1.52  sim_bw_subsumed:                        1
% 7.65/1.52  sim_fw_subsumption_res:                 0
% 7.65/1.52  sim_bw_subsumption_res:                 0
% 7.65/1.52  sim_tautology_del:                      3
% 7.65/1.52  sim_eq_tautology_del:                   31
% 7.65/1.52  sim_eq_res_simp:                        0
% 7.65/1.52  sim_fw_demodulated:                     20
% 7.65/1.52  sim_bw_demodulated:                     18
% 7.65/1.52  sim_light_normalised:                   261
% 7.65/1.52  sim_joinable_taut:                      0
% 7.65/1.52  sim_joinable_simp:                      0
% 7.65/1.52  sim_ac_normalised:                      0
% 7.65/1.52  sim_smt_subsumption:                    0
% 7.65/1.52  
%------------------------------------------------------------------------------
