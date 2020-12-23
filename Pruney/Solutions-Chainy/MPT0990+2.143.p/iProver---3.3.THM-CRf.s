%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:27 EST 2020

% Result     : Theorem 1.24s
% Output     : CNFRefutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :  207 (1140 expanded)
%              Number of clauses        :  121 ( 343 expanded)
%              Number of leaves         :   24 ( 290 expanded)
%              Depth                    :   20
%              Number of atoms          :  767 (9254 expanded)
%              Number of equality atoms :  379 (3349 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,conjecture,(
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

fof(f30,negated_conjecture,(
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
    inference(negated_conjecture,[],[f29])).

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f68,plain,(
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

fof(f67,plain,
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

fof(f69,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f62,f68,f67])).

fof(f113,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f69])).

fof(f116,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f69])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f55])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f114,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f48])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f118,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f69])).

fof(f24,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f111,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f53])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f26,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f88,f105])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f117,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f69])).

fof(f27,axiom,(
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

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f112,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f115,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f69])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f85,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f126,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f87,f105])).

fof(f28,axiom,(
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

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f109,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f120,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f69])).

fof(f22,axiom,(
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

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f52])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f78,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f122,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_49,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1699,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1702,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1708,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_9287,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1702,c_1708])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_55,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_9302,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9287,c_55])).

cnf(c_9303,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9302])).

cnf(c_9311,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1699,c_9303])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_44,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_44])).

cnf(c_568,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_33,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_576,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_568,c_33])).

cnf(c_1695,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_51,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2165,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2859,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1695,c_51,c_49,c_48,c_46,c_576,c_2165])).

cnf(c_9312,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9311,c_2859])).

cnf(c_52,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_10003,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9312,c_52])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1722,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10049,plain,
    ( k2_funct_1(sK4) = sK3
    | k6_partfun1(k2_relat_1(sK4)) != k6_partfun1(sK1)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10003,c_1722])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1721,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4137,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1699,c_1721])).

cnf(c_45,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_4138,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4137,c_45])).

cnf(c_4136,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1702,c_1721])).

cnf(c_35,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_580,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_44])).

cnf(c_581,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_681,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_581])).

cnf(c_1694,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_2232,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1694])).

cnf(c_50,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_53,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_54,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_56,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_57,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_2866,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2232,c_52,c_53,c_54,c_55,c_56,c_57])).

cnf(c_4139,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4136,c_2866])).

cnf(c_10054,plain,
    ( k2_funct_1(sK4) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | k1_relat_1(sK4) != sK2
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10049,c_4138,c_4139])).

cnf(c_10055,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10054])).

cnf(c_1700,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1725,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7401,plain,
    ( k2_funct_1(sK4) = k4_relat_1(sK4)
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1700,c_1725])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1890,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2194,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1890])).

cnf(c_3088,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2194])).

cnf(c_3089,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3088])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3388,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3389,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3388])).

cnf(c_16,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1724,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_37,plain,
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
    inference(cnf_transformation,[],[f109])).

cnf(c_1706,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1739,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1738,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3054,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1739,c_1738])).

cnf(c_4738,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | o_0_0_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1706,c_3054])).

cnf(c_4740,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_45,c_4738])).

cnf(c_5227,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | o_0_0_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4740,c_52,c_53,c_54])).

cnf(c_5228,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5227])).

cnf(c_5233,plain,
    ( sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2859,c_5228])).

cnf(c_42,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1836,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_951,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1916,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_951])).

cnf(c_2225,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | sK1 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1916])).

cnf(c_5271,plain,
    ( v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5233,c_55,c_56,c_57,c_42,c_0,c_1836,c_2225])).

cnf(c_5275,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1724,c_5271])).

cnf(c_7717,plain,
    ( k2_funct_1(sK4) = k4_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7401,c_57,c_3089,c_3389,c_5275])).

cnf(c_10056,plain,
    ( k1_relat_1(sK4) != sK2
    | k4_relat_1(sK4) = sK3
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10055,c_7717])).

cnf(c_1733,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1735,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4190,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1699,c_1735])).

cnf(c_4320,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1733,c_4190])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1712,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_9032,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | o_0_0_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1712,c_3054])).

cnf(c_9036,plain,
    ( k1_relset_1(sK2,sK1,sK4) = sK2
    | sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1702,c_9032])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1719,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5907,plain,
    ( k8_relset_1(sK2,sK1,sK4,sK1) = k1_relset_1(sK2,sK1,sK4) ),
    inference(superposition,[status(thm)],[c_1702,c_1719])).

cnf(c_4189,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1702,c_1735])).

cnf(c_4194,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4189,c_57,c_3089,c_3389])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1731,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4199,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_4194,c_1731])).

cnf(c_4207,plain,
    ( k10_relat_1(sK4,sK1) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_4199,c_4139])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1720,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4926,plain,
    ( k8_relset_1(sK2,sK1,sK4,X0) = k10_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1702,c_1720])).

cnf(c_5910,plain,
    ( k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_5907,c_4207,c_4926])).

cnf(c_9039,plain,
    ( k1_relat_1(sK4) = sK2
    | sK1 = o_0_0_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9036,c_5910])).

cnf(c_11349,plain,
    ( k4_relat_1(sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10056,c_52,c_55,c_56,c_57,c_42,c_0,c_1836,c_2225,c_3089,c_3389,c_4320,c_5275,c_9039])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1732,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4204,plain,
    ( k4_relat_1(k4_relat_1(sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_4194,c_1732])).

cnf(c_11359,plain,
    ( k4_relat_1(sK3) = sK4 ),
    inference(demodulation,[status(thm)],[c_11349,c_4204])).

cnf(c_1697,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_7402,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1697,c_1725])).

cnf(c_43,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_59,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_7720,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7402,c_59,c_4320])).

cnf(c_40,negated_conjecture,
    ( k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_7722,plain,
    ( k4_relat_1(sK3) != sK4 ),
    inference(demodulation,[status(thm)],[c_7720,c_40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11359,c_7722])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:11:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.24/1.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.24/1.06  
% 1.24/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.24/1.06  
% 1.24/1.06  ------  iProver source info
% 1.24/1.06  
% 1.24/1.06  git: date: 2020-06-30 10:37:57 +0100
% 1.24/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.24/1.06  git: non_committed_changes: false
% 1.24/1.06  git: last_make_outside_of_git: false
% 1.24/1.06  
% 1.24/1.06  ------ 
% 1.24/1.06  
% 1.24/1.06  ------ Input Options
% 1.24/1.06  
% 1.24/1.06  --out_options                           all
% 1.24/1.06  --tptp_safe_out                         true
% 1.24/1.06  --problem_path                          ""
% 1.24/1.06  --include_path                          ""
% 1.24/1.06  --clausifier                            res/vclausify_rel
% 1.24/1.06  --clausifier_options                    ""
% 1.24/1.06  --stdin                                 false
% 1.24/1.06  --stats_out                             all
% 1.24/1.06  
% 1.24/1.06  ------ General Options
% 1.24/1.06  
% 1.24/1.06  --fof                                   false
% 1.24/1.06  --time_out_real                         305.
% 1.24/1.06  --time_out_virtual                      -1.
% 1.24/1.06  --symbol_type_check                     false
% 1.24/1.06  --clausify_out                          false
% 1.24/1.06  --sig_cnt_out                           false
% 1.24/1.06  --trig_cnt_out                          false
% 1.24/1.06  --trig_cnt_out_tolerance                1.
% 1.24/1.06  --trig_cnt_out_sk_spl                   false
% 1.24/1.06  --abstr_cl_out                          false
% 1.24/1.06  
% 1.24/1.06  ------ Global Options
% 1.24/1.06  
% 1.24/1.06  --schedule                              default
% 1.24/1.06  --add_important_lit                     false
% 1.24/1.06  --prop_solver_per_cl                    1000
% 1.24/1.06  --min_unsat_core                        false
% 1.24/1.06  --soft_assumptions                      false
% 1.24/1.06  --soft_lemma_size                       3
% 1.24/1.06  --prop_impl_unit_size                   0
% 1.24/1.06  --prop_impl_unit                        []
% 1.24/1.06  --share_sel_clauses                     true
% 1.24/1.06  --reset_solvers                         false
% 1.24/1.06  --bc_imp_inh                            [conj_cone]
% 1.24/1.06  --conj_cone_tolerance                   3.
% 1.24/1.06  --extra_neg_conj                        none
% 1.24/1.06  --large_theory_mode                     true
% 1.24/1.06  --prolific_symb_bound                   200
% 1.24/1.06  --lt_threshold                          2000
% 1.24/1.06  --clause_weak_htbl                      true
% 1.24/1.06  --gc_record_bc_elim                     false
% 1.24/1.06  
% 1.24/1.06  ------ Preprocessing Options
% 1.24/1.06  
% 1.24/1.06  --preprocessing_flag                    true
% 1.24/1.06  --time_out_prep_mult                    0.1
% 1.24/1.06  --splitting_mode                        input
% 1.24/1.06  --splitting_grd                         true
% 1.24/1.06  --splitting_cvd                         false
% 1.24/1.06  --splitting_cvd_svl                     false
% 1.24/1.06  --splitting_nvd                         32
% 1.24/1.06  --sub_typing                            true
% 1.24/1.06  --prep_gs_sim                           true
% 1.24/1.06  --prep_unflatten                        true
% 1.24/1.06  --prep_res_sim                          true
% 1.24/1.06  --prep_upred                            true
% 1.24/1.06  --prep_sem_filter                       exhaustive
% 1.24/1.06  --prep_sem_filter_out                   false
% 1.24/1.06  --pred_elim                             true
% 1.24/1.06  --res_sim_input                         true
% 1.24/1.06  --eq_ax_congr_red                       true
% 1.24/1.06  --pure_diseq_elim                       true
% 1.24/1.06  --brand_transform                       false
% 1.24/1.06  --non_eq_to_eq                          false
% 1.24/1.06  --prep_def_merge                        true
% 1.24/1.06  --prep_def_merge_prop_impl              false
% 1.24/1.06  --prep_def_merge_mbd                    true
% 1.24/1.06  --prep_def_merge_tr_red                 false
% 1.24/1.06  --prep_def_merge_tr_cl                  false
% 1.24/1.06  --smt_preprocessing                     true
% 1.24/1.06  --smt_ac_axioms                         fast
% 1.24/1.06  --preprocessed_out                      false
% 1.24/1.06  --preprocessed_stats                    false
% 1.24/1.06  
% 1.24/1.06  ------ Abstraction refinement Options
% 1.24/1.06  
% 1.24/1.06  --abstr_ref                             []
% 1.24/1.06  --abstr_ref_prep                        false
% 1.24/1.06  --abstr_ref_until_sat                   false
% 1.24/1.06  --abstr_ref_sig_restrict                funpre
% 1.24/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.24/1.06  --abstr_ref_under                       []
% 1.24/1.06  
% 1.24/1.06  ------ SAT Options
% 1.24/1.06  
% 1.24/1.06  --sat_mode                              false
% 1.24/1.06  --sat_fm_restart_options                ""
% 1.24/1.06  --sat_gr_def                            false
% 1.24/1.06  --sat_epr_types                         true
% 1.24/1.06  --sat_non_cyclic_types                  false
% 1.24/1.06  --sat_finite_models                     false
% 1.24/1.06  --sat_fm_lemmas                         false
% 1.24/1.06  --sat_fm_prep                           false
% 1.24/1.06  --sat_fm_uc_incr                        true
% 1.24/1.06  --sat_out_model                         small
% 1.24/1.06  --sat_out_clauses                       false
% 1.24/1.06  
% 1.24/1.06  ------ QBF Options
% 1.24/1.06  
% 1.24/1.06  --qbf_mode                              false
% 1.24/1.06  --qbf_elim_univ                         false
% 1.24/1.06  --qbf_dom_inst                          none
% 1.24/1.06  --qbf_dom_pre_inst                      false
% 1.24/1.06  --qbf_sk_in                             false
% 1.24/1.06  --qbf_pred_elim                         true
% 1.24/1.06  --qbf_split                             512
% 1.24/1.06  
% 1.24/1.06  ------ BMC1 Options
% 1.24/1.06  
% 1.24/1.06  --bmc1_incremental                      false
% 1.24/1.06  --bmc1_axioms                           reachable_all
% 1.24/1.06  --bmc1_min_bound                        0
% 1.24/1.06  --bmc1_max_bound                        -1
% 1.24/1.06  --bmc1_max_bound_default                -1
% 1.24/1.06  --bmc1_symbol_reachability              true
% 1.24/1.06  --bmc1_property_lemmas                  false
% 1.24/1.06  --bmc1_k_induction                      false
% 1.24/1.06  --bmc1_non_equiv_states                 false
% 1.24/1.06  --bmc1_deadlock                         false
% 1.24/1.06  --bmc1_ucm                              false
% 1.24/1.06  --bmc1_add_unsat_core                   none
% 1.24/1.06  --bmc1_unsat_core_children              false
% 1.24/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.24/1.06  --bmc1_out_stat                         full
% 1.24/1.06  --bmc1_ground_init                      false
% 1.24/1.06  --bmc1_pre_inst_next_state              false
% 1.24/1.06  --bmc1_pre_inst_state                   false
% 1.24/1.06  --bmc1_pre_inst_reach_state             false
% 1.24/1.06  --bmc1_out_unsat_core                   false
% 1.24/1.06  --bmc1_aig_witness_out                  false
% 1.24/1.06  --bmc1_verbose                          false
% 1.24/1.06  --bmc1_dump_clauses_tptp                false
% 1.24/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.24/1.06  --bmc1_dump_file                        -
% 1.24/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.24/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.24/1.06  --bmc1_ucm_extend_mode                  1
% 1.24/1.06  --bmc1_ucm_init_mode                    2
% 1.24/1.06  --bmc1_ucm_cone_mode                    none
% 1.24/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.24/1.06  --bmc1_ucm_relax_model                  4
% 1.24/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.24/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.24/1.06  --bmc1_ucm_layered_model                none
% 1.24/1.06  --bmc1_ucm_max_lemma_size               10
% 1.24/1.06  
% 1.24/1.06  ------ AIG Options
% 1.24/1.06  
% 1.24/1.06  --aig_mode                              false
% 1.24/1.06  
% 1.24/1.06  ------ Instantiation Options
% 1.24/1.06  
% 1.24/1.06  --instantiation_flag                    true
% 1.24/1.06  --inst_sos_flag                         true
% 1.24/1.06  --inst_sos_phase                        true
% 1.24/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.24/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.24/1.06  --inst_lit_sel_side                     num_symb
% 1.24/1.06  --inst_solver_per_active                1400
% 1.24/1.06  --inst_solver_calls_frac                1.
% 1.24/1.06  --inst_passive_queue_type               priority_queues
% 1.24/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.24/1.06  --inst_passive_queues_freq              [25;2]
% 1.24/1.06  --inst_dismatching                      true
% 1.24/1.06  --inst_eager_unprocessed_to_passive     true
% 1.24/1.06  --inst_prop_sim_given                   true
% 1.24/1.06  --inst_prop_sim_new                     false
% 1.24/1.06  --inst_subs_new                         false
% 1.24/1.06  --inst_eq_res_simp                      false
% 1.24/1.06  --inst_subs_given                       false
% 1.24/1.06  --inst_orphan_elimination               true
% 1.24/1.06  --inst_learning_loop_flag               true
% 1.24/1.06  --inst_learning_start                   3000
% 1.24/1.06  --inst_learning_factor                  2
% 1.24/1.06  --inst_start_prop_sim_after_learn       3
% 1.24/1.06  --inst_sel_renew                        solver
% 1.24/1.06  --inst_lit_activity_flag                true
% 1.24/1.06  --inst_restr_to_given                   false
% 1.24/1.06  --inst_activity_threshold               500
% 1.24/1.06  --inst_out_proof                        true
% 1.24/1.06  
% 1.24/1.06  ------ Resolution Options
% 1.24/1.06  
% 1.24/1.06  --resolution_flag                       true
% 1.24/1.06  --res_lit_sel                           adaptive
% 1.24/1.06  --res_lit_sel_side                      none
% 1.24/1.06  --res_ordering                          kbo
% 1.24/1.06  --res_to_prop_solver                    active
% 1.24/1.06  --res_prop_simpl_new                    false
% 1.24/1.06  --res_prop_simpl_given                  true
% 1.24/1.06  --res_passive_queue_type                priority_queues
% 1.24/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.24/1.06  --res_passive_queues_freq               [15;5]
% 1.24/1.06  --res_forward_subs                      full
% 1.24/1.06  --res_backward_subs                     full
% 1.24/1.06  --res_forward_subs_resolution           true
% 1.24/1.06  --res_backward_subs_resolution          true
% 1.24/1.06  --res_orphan_elimination                true
% 1.24/1.06  --res_time_limit                        2.
% 1.24/1.06  --res_out_proof                         true
% 1.24/1.06  
% 1.24/1.06  ------ Superposition Options
% 1.24/1.06  
% 1.24/1.06  --superposition_flag                    true
% 1.24/1.06  --sup_passive_queue_type                priority_queues
% 1.24/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.24/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.24/1.06  --demod_completeness_check              fast
% 1.24/1.06  --demod_use_ground                      true
% 1.24/1.06  --sup_to_prop_solver                    passive
% 1.24/1.06  --sup_prop_simpl_new                    true
% 1.24/1.06  --sup_prop_simpl_given                  true
% 1.24/1.06  --sup_fun_splitting                     true
% 1.24/1.06  --sup_smt_interval                      50000
% 1.24/1.06  
% 1.24/1.06  ------ Superposition Simplification Setup
% 1.24/1.06  
% 1.24/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 1.24/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 1.24/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 1.24/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 1.24/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 1.24/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 1.24/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 1.24/1.06  --sup_immed_triv                        [TrivRules]
% 1.24/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.24/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 1.24/1.06  --sup_immed_bw_main                     []
% 1.24/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 1.24/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 1.24/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 1.24/1.06  --sup_input_bw                          []
% 1.24/1.06  
% 1.24/1.06  ------ Combination Options
% 1.24/1.06  
% 1.24/1.06  --comb_res_mult                         3
% 1.24/1.06  --comb_sup_mult                         2
% 1.24/1.06  --comb_inst_mult                        10
% 1.24/1.06  
% 1.24/1.06  ------ Debug Options
% 1.24/1.06  
% 1.24/1.06  --dbg_backtrace                         false
% 1.24/1.06  --dbg_dump_prop_clauses                 false
% 1.24/1.06  --dbg_dump_prop_clauses_file            -
% 1.24/1.06  --dbg_out_stat                          false
% 1.24/1.06  ------ Parsing...
% 1.24/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.24/1.06  
% 1.24/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.24/1.06  
% 1.24/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.24/1.06  
% 1.24/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.24/1.06  ------ Proving...
% 1.24/1.06  ------ Problem Properties 
% 1.24/1.06  
% 1.24/1.06  
% 1.24/1.06  clauses                                 51
% 1.24/1.06  conjectures                             11
% 1.24/1.06  EPR                                     11
% 1.24/1.06  Horn                                    45
% 1.24/1.06  unary                                   18
% 1.24/1.06  binary                                  13
% 1.24/1.06  lits                                    155
% 1.24/1.06  lits eq                                 43
% 1.24/1.06  fd_pure                                 0
% 1.24/1.06  fd_pseudo                               0
% 1.24/1.06  fd_cond                                 6
% 1.24/1.06  fd_pseudo_cond                          2
% 1.24/1.06  AC symbols                              0
% 1.24/1.06  
% 1.24/1.06  ------ Schedule dynamic 5 is on 
% 1.24/1.06  
% 1.24/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.24/1.06  
% 1.24/1.06  
% 1.24/1.06  ------ 
% 1.24/1.06  Current options:
% 1.24/1.06  ------ 
% 1.24/1.06  
% 1.24/1.06  ------ Input Options
% 1.24/1.06  
% 1.24/1.06  --out_options                           all
% 1.24/1.06  --tptp_safe_out                         true
% 1.24/1.06  --problem_path                          ""
% 1.24/1.06  --include_path                          ""
% 1.24/1.06  --clausifier                            res/vclausify_rel
% 1.24/1.06  --clausifier_options                    ""
% 1.24/1.06  --stdin                                 false
% 1.24/1.06  --stats_out                             all
% 1.24/1.06  
% 1.24/1.06  ------ General Options
% 1.24/1.06  
% 1.24/1.06  --fof                                   false
% 1.24/1.06  --time_out_real                         305.
% 1.24/1.06  --time_out_virtual                      -1.
% 1.24/1.06  --symbol_type_check                     false
% 1.24/1.06  --clausify_out                          false
% 1.24/1.06  --sig_cnt_out                           false
% 1.24/1.06  --trig_cnt_out                          false
% 1.24/1.06  --trig_cnt_out_tolerance                1.
% 1.24/1.06  --trig_cnt_out_sk_spl                   false
% 1.24/1.06  --abstr_cl_out                          false
% 1.24/1.06  
% 1.24/1.06  ------ Global Options
% 1.24/1.06  
% 1.24/1.06  --schedule                              default
% 1.24/1.06  --add_important_lit                     false
% 1.24/1.06  --prop_solver_per_cl                    1000
% 1.24/1.06  --min_unsat_core                        false
% 1.24/1.06  --soft_assumptions                      false
% 1.24/1.06  --soft_lemma_size                       3
% 1.24/1.06  --prop_impl_unit_size                   0
% 1.24/1.06  --prop_impl_unit                        []
% 1.24/1.06  --share_sel_clauses                     true
% 1.24/1.06  --reset_solvers                         false
% 1.24/1.06  --bc_imp_inh                            [conj_cone]
% 1.24/1.06  --conj_cone_tolerance                   3.
% 1.24/1.06  --extra_neg_conj                        none
% 1.24/1.06  --large_theory_mode                     true
% 1.24/1.06  --prolific_symb_bound                   200
% 1.24/1.06  --lt_threshold                          2000
% 1.24/1.06  --clause_weak_htbl                      true
% 1.24/1.06  --gc_record_bc_elim                     false
% 1.24/1.06  
% 1.24/1.06  ------ Preprocessing Options
% 1.24/1.06  
% 1.24/1.06  --preprocessing_flag                    true
% 1.24/1.06  --time_out_prep_mult                    0.1
% 1.24/1.06  --splitting_mode                        input
% 1.24/1.06  --splitting_grd                         true
% 1.24/1.06  --splitting_cvd                         false
% 1.24/1.06  --splitting_cvd_svl                     false
% 1.24/1.06  --splitting_nvd                         32
% 1.24/1.06  --sub_typing                            true
% 1.24/1.06  --prep_gs_sim                           true
% 1.24/1.06  --prep_unflatten                        true
% 1.24/1.06  --prep_res_sim                          true
% 1.24/1.06  --prep_upred                            true
% 1.24/1.06  --prep_sem_filter                       exhaustive
% 1.24/1.06  --prep_sem_filter_out                   false
% 1.24/1.06  --pred_elim                             true
% 1.24/1.06  --res_sim_input                         true
% 1.24/1.06  --eq_ax_congr_red                       true
% 1.24/1.06  --pure_diseq_elim                       true
% 1.24/1.06  --brand_transform                       false
% 1.24/1.06  --non_eq_to_eq                          false
% 1.24/1.06  --prep_def_merge                        true
% 1.24/1.06  --prep_def_merge_prop_impl              false
% 1.24/1.06  --prep_def_merge_mbd                    true
% 1.24/1.06  --prep_def_merge_tr_red                 false
% 1.24/1.06  --prep_def_merge_tr_cl                  false
% 1.24/1.06  --smt_preprocessing                     true
% 1.24/1.06  --smt_ac_axioms                         fast
% 1.24/1.06  --preprocessed_out                      false
% 1.24/1.06  --preprocessed_stats                    false
% 1.24/1.06  
% 1.24/1.06  ------ Abstraction refinement Options
% 1.24/1.06  
% 1.24/1.06  --abstr_ref                             []
% 1.24/1.06  --abstr_ref_prep                        false
% 1.24/1.06  --abstr_ref_until_sat                   false
% 1.24/1.06  --abstr_ref_sig_restrict                funpre
% 1.24/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.24/1.06  --abstr_ref_under                       []
% 1.24/1.06  
% 1.24/1.06  ------ SAT Options
% 1.24/1.06  
% 1.24/1.06  --sat_mode                              false
% 1.24/1.06  --sat_fm_restart_options                ""
% 1.24/1.06  --sat_gr_def                            false
% 1.24/1.06  --sat_epr_types                         true
% 1.24/1.06  --sat_non_cyclic_types                  false
% 1.24/1.06  --sat_finite_models                     false
% 1.24/1.06  --sat_fm_lemmas                         false
% 1.24/1.06  --sat_fm_prep                           false
% 1.24/1.06  --sat_fm_uc_incr                        true
% 1.24/1.06  --sat_out_model                         small
% 1.24/1.06  --sat_out_clauses                       false
% 1.24/1.06  
% 1.24/1.06  ------ QBF Options
% 1.24/1.06  
% 1.24/1.06  --qbf_mode                              false
% 1.24/1.06  --qbf_elim_univ                         false
% 1.24/1.06  --qbf_dom_inst                          none
% 1.24/1.06  --qbf_dom_pre_inst                      false
% 1.24/1.06  --qbf_sk_in                             false
% 1.24/1.06  --qbf_pred_elim                         true
% 1.24/1.06  --qbf_split                             512
% 1.24/1.06  
% 1.24/1.06  ------ BMC1 Options
% 1.24/1.06  
% 1.24/1.06  --bmc1_incremental                      false
% 1.24/1.06  --bmc1_axioms                           reachable_all
% 1.24/1.06  --bmc1_min_bound                        0
% 1.24/1.06  --bmc1_max_bound                        -1
% 1.24/1.06  --bmc1_max_bound_default                -1
% 1.24/1.06  --bmc1_symbol_reachability              true
% 1.24/1.06  --bmc1_property_lemmas                  false
% 1.24/1.06  --bmc1_k_induction                      false
% 1.24/1.06  --bmc1_non_equiv_states                 false
% 1.24/1.06  --bmc1_deadlock                         false
% 1.24/1.06  --bmc1_ucm                              false
% 1.24/1.06  --bmc1_add_unsat_core                   none
% 1.24/1.06  --bmc1_unsat_core_children              false
% 1.24/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.24/1.06  --bmc1_out_stat                         full
% 1.24/1.06  --bmc1_ground_init                      false
% 1.24/1.06  --bmc1_pre_inst_next_state              false
% 1.24/1.06  --bmc1_pre_inst_state                   false
% 1.24/1.06  --bmc1_pre_inst_reach_state             false
% 1.24/1.06  --bmc1_out_unsat_core                   false
% 1.24/1.06  --bmc1_aig_witness_out                  false
% 1.24/1.06  --bmc1_verbose                          false
% 1.24/1.06  --bmc1_dump_clauses_tptp                false
% 1.24/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.24/1.06  --bmc1_dump_file                        -
% 1.24/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.24/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.24/1.06  --bmc1_ucm_extend_mode                  1
% 1.24/1.06  --bmc1_ucm_init_mode                    2
% 1.24/1.06  --bmc1_ucm_cone_mode                    none
% 1.24/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.24/1.06  --bmc1_ucm_relax_model                  4
% 1.24/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.24/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.24/1.06  --bmc1_ucm_layered_model                none
% 1.24/1.06  --bmc1_ucm_max_lemma_size               10
% 1.24/1.06  
% 1.24/1.06  ------ AIG Options
% 1.24/1.06  
% 1.24/1.06  --aig_mode                              false
% 1.24/1.06  
% 1.24/1.06  ------ Instantiation Options
% 1.24/1.06  
% 1.24/1.06  --instantiation_flag                    true
% 1.24/1.06  --inst_sos_flag                         true
% 1.24/1.06  --inst_sos_phase                        true
% 1.24/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.24/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.24/1.06  --inst_lit_sel_side                     none
% 1.24/1.06  --inst_solver_per_active                1400
% 1.24/1.06  --inst_solver_calls_frac                1.
% 1.24/1.06  --inst_passive_queue_type               priority_queues
% 1.24/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.24/1.06  --inst_passive_queues_freq              [25;2]
% 1.24/1.06  --inst_dismatching                      true
% 1.24/1.06  --inst_eager_unprocessed_to_passive     true
% 1.24/1.06  --inst_prop_sim_given                   true
% 1.24/1.06  --inst_prop_sim_new                     false
% 1.24/1.06  --inst_subs_new                         false
% 1.24/1.06  --inst_eq_res_simp                      false
% 1.24/1.06  --inst_subs_given                       false
% 1.24/1.06  --inst_orphan_elimination               true
% 1.24/1.06  --inst_learning_loop_flag               true
% 1.24/1.06  --inst_learning_start                   3000
% 1.24/1.06  --inst_learning_factor                  2
% 1.24/1.06  --inst_start_prop_sim_after_learn       3
% 1.24/1.06  --inst_sel_renew                        solver
% 1.24/1.06  --inst_lit_activity_flag                true
% 1.24/1.06  --inst_restr_to_given                   false
% 1.24/1.06  --inst_activity_threshold               500
% 1.24/1.06  --inst_out_proof                        true
% 1.24/1.06  
% 1.24/1.06  ------ Resolution Options
% 1.24/1.06  
% 1.24/1.06  --resolution_flag                       false
% 1.24/1.06  --res_lit_sel                           adaptive
% 1.24/1.06  --res_lit_sel_side                      none
% 1.24/1.06  --res_ordering                          kbo
% 1.24/1.06  --res_to_prop_solver                    active
% 1.24/1.06  --res_prop_simpl_new                    false
% 1.24/1.06  --res_prop_simpl_given                  true
% 1.24/1.06  --res_passive_queue_type                priority_queues
% 1.24/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.24/1.06  --res_passive_queues_freq               [15;5]
% 1.24/1.06  --res_forward_subs                      full
% 1.24/1.06  --res_backward_subs                     full
% 1.24/1.06  --res_forward_subs_resolution           true
% 1.24/1.06  --res_backward_subs_resolution          true
% 1.24/1.06  --res_orphan_elimination                true
% 1.24/1.06  --res_time_limit                        2.
% 1.24/1.06  --res_out_proof                         true
% 1.24/1.06  
% 1.24/1.06  ------ Superposition Options
% 1.24/1.06  
% 1.24/1.06  --superposition_flag                    true
% 1.24/1.06  --sup_passive_queue_type                priority_queues
% 1.24/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.24/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.24/1.06  --demod_completeness_check              fast
% 1.24/1.06  --demod_use_ground                      true
% 1.24/1.06  --sup_to_prop_solver                    passive
% 1.24/1.06  --sup_prop_simpl_new                    true
% 1.24/1.06  --sup_prop_simpl_given                  true
% 1.24/1.06  --sup_fun_splitting                     true
% 1.24/1.06  --sup_smt_interval                      50000
% 1.24/1.06  
% 1.24/1.06  ------ Superposition Simplification Setup
% 1.24/1.06  
% 1.24/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 1.24/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 1.24/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 1.24/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 1.24/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 1.24/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 1.24/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 1.24/1.06  --sup_immed_triv                        [TrivRules]
% 1.24/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.24/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 1.24/1.06  --sup_immed_bw_main                     []
% 1.24/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 1.24/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 1.24/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 1.24/1.06  --sup_input_bw                          []
% 1.24/1.06  
% 1.24/1.06  ------ Combination Options
% 1.24/1.06  
% 1.24/1.06  --comb_res_mult                         3
% 1.24/1.06  --comb_sup_mult                         2
% 1.24/1.06  --comb_inst_mult                        10
% 1.24/1.06  
% 1.24/1.06  ------ Debug Options
% 1.24/1.06  
% 1.24/1.06  --dbg_backtrace                         false
% 1.24/1.06  --dbg_dump_prop_clauses                 false
% 1.24/1.06  --dbg_dump_prop_clauses_file            -
% 1.24/1.06  --dbg_out_stat                          false
% 1.24/1.06  
% 1.24/1.06  
% 1.24/1.06  
% 1.24/1.06  
% 1.24/1.06  ------ Proving...
% 1.24/1.06  
% 1.24/1.06  
% 1.24/1.06  % SZS status Theorem for theBenchmark.p
% 1.24/1.06  
% 1.24/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 1.24/1.06  
% 1.24/1.06  fof(f29,conjecture,(
% 1.24/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f30,negated_conjecture,(
% 1.24/1.06    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.24/1.06    inference(negated_conjecture,[],[f29])).
% 1.24/1.06  
% 1.24/1.06  fof(f61,plain,(
% 1.24/1.06    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.24/1.06    inference(ennf_transformation,[],[f30])).
% 1.24/1.06  
% 1.24/1.06  fof(f62,plain,(
% 1.24/1.06    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.24/1.06    inference(flattening,[],[f61])).
% 1.24/1.06  
% 1.24/1.06  fof(f68,plain,(
% 1.24/1.06    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK4 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 1.24/1.06    introduced(choice_axiom,[])).
% 1.24/1.06  
% 1.24/1.06  fof(f67,plain,(
% 1.24/1.06    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.24/1.06    introduced(choice_axiom,[])).
% 1.24/1.06  
% 1.24/1.06  fof(f69,plain,(
% 1.24/1.06    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.24/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f62,f68,f67])).
% 1.24/1.06  
% 1.24/1.06  fof(f113,plain,(
% 1.24/1.06    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.24/1.06    inference(cnf_transformation,[],[f69])).
% 1.24/1.06  
% 1.24/1.06  fof(f116,plain,(
% 1.24/1.06    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.24/1.06    inference(cnf_transformation,[],[f69])).
% 1.24/1.06  
% 1.24/1.06  fof(f25,axiom,(
% 1.24/1.06    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f55,plain,(
% 1.24/1.06    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.24/1.06    inference(ennf_transformation,[],[f25])).
% 1.24/1.06  
% 1.24/1.06  fof(f56,plain,(
% 1.24/1.06    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.24/1.06    inference(flattening,[],[f55])).
% 1.24/1.06  
% 1.24/1.06  fof(f104,plain,(
% 1.24/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.24/1.06    inference(cnf_transformation,[],[f56])).
% 1.24/1.06  
% 1.24/1.06  fof(f114,plain,(
% 1.24/1.06    v1_funct_1(sK4)),
% 1.24/1.06    inference(cnf_transformation,[],[f69])).
% 1.24/1.06  
% 1.24/1.06  fof(f20,axiom,(
% 1.24/1.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f48,plain,(
% 1.24/1.06    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.24/1.06    inference(ennf_transformation,[],[f20])).
% 1.24/1.06  
% 1.24/1.06  fof(f49,plain,(
% 1.24/1.06    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/1.06    inference(flattening,[],[f48])).
% 1.24/1.06  
% 1.24/1.06  fof(f65,plain,(
% 1.24/1.06    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/1.06    inference(nnf_transformation,[],[f49])).
% 1.24/1.06  
% 1.24/1.06  fof(f91,plain,(
% 1.24/1.06    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.24/1.06    inference(cnf_transformation,[],[f65])).
% 1.24/1.06  
% 1.24/1.06  fof(f118,plain,(
% 1.24/1.06    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 1.24/1.06    inference(cnf_transformation,[],[f69])).
% 1.24/1.06  
% 1.24/1.06  fof(f24,axiom,(
% 1.24/1.06    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f31,plain,(
% 1.24/1.06    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.24/1.06    inference(pure_predicate_removal,[],[f24])).
% 1.24/1.06  
% 1.24/1.06  fof(f103,plain,(
% 1.24/1.06    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.24/1.06    inference(cnf_transformation,[],[f31])).
% 1.24/1.06  
% 1.24/1.06  fof(f111,plain,(
% 1.24/1.06    v1_funct_1(sK3)),
% 1.24/1.06    inference(cnf_transformation,[],[f69])).
% 1.24/1.06  
% 1.24/1.06  fof(f23,axiom,(
% 1.24/1.06    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f53,plain,(
% 1.24/1.06    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.24/1.06    inference(ennf_transformation,[],[f23])).
% 1.24/1.06  
% 1.24/1.06  fof(f54,plain,(
% 1.24/1.06    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.24/1.06    inference(flattening,[],[f53])).
% 1.24/1.06  
% 1.24/1.06  fof(f102,plain,(
% 1.24/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.24/1.06    inference(cnf_transformation,[],[f54])).
% 1.24/1.06  
% 1.24/1.06  fof(f17,axiom,(
% 1.24/1.06    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f44,plain,(
% 1.24/1.06    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.24/1.06    inference(ennf_transformation,[],[f17])).
% 1.24/1.06  
% 1.24/1.06  fof(f45,plain,(
% 1.24/1.06    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.24/1.06    inference(flattening,[],[f44])).
% 1.24/1.06  
% 1.24/1.06  fof(f88,plain,(
% 1.24/1.06    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.24/1.06    inference(cnf_transformation,[],[f45])).
% 1.24/1.06  
% 1.24/1.06  fof(f26,axiom,(
% 1.24/1.06    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f105,plain,(
% 1.24/1.06    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.24/1.06    inference(cnf_transformation,[],[f26])).
% 1.24/1.06  
% 1.24/1.06  fof(f128,plain,(
% 1.24/1.06    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.24/1.06    inference(definition_unfolding,[],[f88,f105])).
% 1.24/1.06  
% 1.24/1.06  fof(f18,axiom,(
% 1.24/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f46,plain,(
% 1.24/1.06    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/1.06    inference(ennf_transformation,[],[f18])).
% 1.24/1.06  
% 1.24/1.06  fof(f89,plain,(
% 1.24/1.06    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.24/1.06    inference(cnf_transformation,[],[f46])).
% 1.24/1.06  
% 1.24/1.06  fof(f117,plain,(
% 1.24/1.06    k2_relset_1(sK1,sK2,sK3) = sK2),
% 1.24/1.06    inference(cnf_transformation,[],[f69])).
% 1.24/1.06  
% 1.24/1.06  fof(f27,axiom,(
% 1.24/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f57,plain,(
% 1.24/1.06    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.24/1.06    inference(ennf_transformation,[],[f27])).
% 1.24/1.06  
% 1.24/1.06  fof(f58,plain,(
% 1.24/1.06    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.24/1.06    inference(flattening,[],[f57])).
% 1.24/1.06  
% 1.24/1.06  fof(f106,plain,(
% 1.24/1.06    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.24/1.06    inference(cnf_transformation,[],[f58])).
% 1.24/1.06  
% 1.24/1.06  fof(f112,plain,(
% 1.24/1.06    v1_funct_2(sK3,sK1,sK2)),
% 1.24/1.06    inference(cnf_transformation,[],[f69])).
% 1.24/1.06  
% 1.24/1.06  fof(f115,plain,(
% 1.24/1.06    v1_funct_2(sK4,sK2,sK1)),
% 1.24/1.06    inference(cnf_transformation,[],[f69])).
% 1.24/1.06  
% 1.24/1.06  fof(f15,axiom,(
% 1.24/1.06    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f42,plain,(
% 1.24/1.06    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.24/1.06    inference(ennf_transformation,[],[f15])).
% 1.24/1.06  
% 1.24/1.06  fof(f43,plain,(
% 1.24/1.06    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.24/1.06    inference(flattening,[],[f42])).
% 1.24/1.06  
% 1.24/1.06  fof(f85,plain,(
% 1.24/1.06    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.24/1.06    inference(cnf_transformation,[],[f43])).
% 1.24/1.06  
% 1.24/1.06  fof(f5,axiom,(
% 1.24/1.06    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f34,plain,(
% 1.24/1.06    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.24/1.06    inference(ennf_transformation,[],[f5])).
% 1.24/1.06  
% 1.24/1.06  fof(f74,plain,(
% 1.24/1.06    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.24/1.06    inference(cnf_transformation,[],[f34])).
% 1.24/1.06  
% 1.24/1.06  fof(f7,axiom,(
% 1.24/1.06    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f76,plain,(
% 1.24/1.06    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.24/1.06    inference(cnf_transformation,[],[f7])).
% 1.24/1.06  
% 1.24/1.06  fof(f16,axiom,(
% 1.24/1.06    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f87,plain,(
% 1.24/1.06    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.24/1.06    inference(cnf_transformation,[],[f16])).
% 1.24/1.06  
% 1.24/1.06  fof(f126,plain,(
% 1.24/1.06    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.24/1.06    inference(definition_unfolding,[],[f87,f105])).
% 1.24/1.06  
% 1.24/1.06  fof(f28,axiom,(
% 1.24/1.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f59,plain,(
% 1.24/1.06    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.24/1.06    inference(ennf_transformation,[],[f28])).
% 1.24/1.06  
% 1.24/1.06  fof(f60,plain,(
% 1.24/1.06    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.24/1.06    inference(flattening,[],[f59])).
% 1.24/1.06  
% 1.24/1.06  fof(f109,plain,(
% 1.24/1.06    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.24/1.06    inference(cnf_transformation,[],[f60])).
% 1.24/1.06  
% 1.24/1.06  fof(f1,axiom,(
% 1.24/1.06    v1_xboole_0(o_0_0_xboole_0)),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f70,plain,(
% 1.24/1.06    v1_xboole_0(o_0_0_xboole_0)),
% 1.24/1.06    inference(cnf_transformation,[],[f1])).
% 1.24/1.06  
% 1.24/1.06  fof(f2,axiom,(
% 1.24/1.06    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f32,plain,(
% 1.24/1.06    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.24/1.06    inference(ennf_transformation,[],[f2])).
% 1.24/1.06  
% 1.24/1.06  fof(f71,plain,(
% 1.24/1.06    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.24/1.06    inference(cnf_transformation,[],[f32])).
% 1.24/1.06  
% 1.24/1.06  fof(f120,plain,(
% 1.24/1.06    k1_xboole_0 != sK1),
% 1.24/1.06    inference(cnf_transformation,[],[f69])).
% 1.24/1.06  
% 1.24/1.06  fof(f22,axiom,(
% 1.24/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f51,plain,(
% 1.24/1.06    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/1.06    inference(ennf_transformation,[],[f22])).
% 1.24/1.06  
% 1.24/1.06  fof(f52,plain,(
% 1.24/1.06    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/1.06    inference(flattening,[],[f51])).
% 1.24/1.06  
% 1.24/1.06  fof(f66,plain,(
% 1.24/1.06    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/1.06    inference(nnf_transformation,[],[f52])).
% 1.24/1.06  
% 1.24/1.06  fof(f95,plain,(
% 1.24/1.06    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.24/1.06    inference(cnf_transformation,[],[f66])).
% 1.24/1.06  
% 1.24/1.06  fof(f21,axiom,(
% 1.24/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f50,plain,(
% 1.24/1.06    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/1.06    inference(ennf_transformation,[],[f21])).
% 1.24/1.06  
% 1.24/1.06  fof(f94,plain,(
% 1.24/1.06    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.24/1.06    inference(cnf_transformation,[],[f50])).
% 1.24/1.06  
% 1.24/1.06  fof(f9,axiom,(
% 1.24/1.06    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f37,plain,(
% 1.24/1.06    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.24/1.06    inference(ennf_transformation,[],[f9])).
% 1.24/1.06  
% 1.24/1.06  fof(f78,plain,(
% 1.24/1.06    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.24/1.06    inference(cnf_transformation,[],[f37])).
% 1.24/1.06  
% 1.24/1.06  fof(f19,axiom,(
% 1.24/1.06    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f47,plain,(
% 1.24/1.06    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/1.06    inference(ennf_transformation,[],[f19])).
% 1.24/1.06  
% 1.24/1.06  fof(f90,plain,(
% 1.24/1.06    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.24/1.06    inference(cnf_transformation,[],[f47])).
% 1.24/1.06  
% 1.24/1.06  fof(f8,axiom,(
% 1.24/1.06    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.24/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/1.06  
% 1.24/1.06  fof(f36,plain,(
% 1.24/1.06    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.24/1.06    inference(ennf_transformation,[],[f8])).
% 1.24/1.06  
% 1.24/1.06  fof(f77,plain,(
% 1.24/1.06    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.24/1.06    inference(cnf_transformation,[],[f36])).
% 1.24/1.06  
% 1.24/1.06  fof(f119,plain,(
% 1.24/1.06    v2_funct_1(sK3)),
% 1.24/1.06    inference(cnf_transformation,[],[f69])).
% 1.24/1.06  
% 1.24/1.06  fof(f122,plain,(
% 1.24/1.06    k2_funct_1(sK3) != sK4),
% 1.24/1.06    inference(cnf_transformation,[],[f69])).
% 1.24/1.06  
% 1.24/1.06  cnf(c_49,negated_conjecture,
% 1.24/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.24/1.06      inference(cnf_transformation,[],[f113]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1699,plain,
% 1.24/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_46,negated_conjecture,
% 1.24/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 1.24/1.06      inference(cnf_transformation,[],[f116]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1702,plain,
% 1.24/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_34,plain,
% 1.24/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.24/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.24/1.06      | ~ v1_funct_1(X0)
% 1.24/1.06      | ~ v1_funct_1(X3)
% 1.24/1.06      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 1.24/1.06      inference(cnf_transformation,[],[f104]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1708,plain,
% 1.24/1.06      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 1.24/1.06      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 1.24/1.06      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.24/1.06      | v1_funct_1(X5) != iProver_top
% 1.24/1.06      | v1_funct_1(X4) != iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_9287,plain,
% 1.24/1.06      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 1.24/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.24/1.06      | v1_funct_1(X2) != iProver_top
% 1.24/1.06      | v1_funct_1(sK4) != iProver_top ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1702,c_1708]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_48,negated_conjecture,
% 1.24/1.06      ( v1_funct_1(sK4) ),
% 1.24/1.06      inference(cnf_transformation,[],[f114]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_55,plain,
% 1.24/1.06      ( v1_funct_1(sK4) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_9302,plain,
% 1.24/1.06      ( v1_funct_1(X2) != iProver_top
% 1.24/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.24/1.06      | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
% 1.24/1.06      inference(global_propositional_subsumption,
% 1.24/1.06                [status(thm)],
% 1.24/1.06                [c_9287,c_55]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_9303,plain,
% 1.24/1.06      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 1.24/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.24/1.06      | v1_funct_1(X2) != iProver_top ),
% 1.24/1.06      inference(renaming,[status(thm)],[c_9302]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_9311,plain,
% 1.24/1.06      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
% 1.24/1.06      | v1_funct_1(sK3) != iProver_top ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1699,c_9303]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_22,plain,
% 1.24/1.06      ( ~ r2_relset_1(X0,X1,X2,X3)
% 1.24/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.24/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.24/1.06      | X3 = X2 ),
% 1.24/1.06      inference(cnf_transformation,[],[f91]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_44,negated_conjecture,
% 1.24/1.06      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 1.24/1.06      inference(cnf_transformation,[],[f118]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_567,plain,
% 1.24/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.24/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.24/1.06      | X3 = X0
% 1.24/1.06      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 1.24/1.06      | k6_partfun1(sK1) != X3
% 1.24/1.06      | sK1 != X2
% 1.24/1.06      | sK1 != X1 ),
% 1.24/1.06      inference(resolution_lifted,[status(thm)],[c_22,c_44]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_568,plain,
% 1.24/1.06      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.24/1.06      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.24/1.06      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 1.24/1.06      inference(unflattening,[status(thm)],[c_567]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_33,plain,
% 1.24/1.06      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 1.24/1.06      inference(cnf_transformation,[],[f103]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_576,plain,
% 1.24/1.06      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.24/1.06      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 1.24/1.06      inference(forward_subsumption_resolution,
% 1.24/1.06                [status(thm)],
% 1.24/1.06                [c_568,c_33]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1695,plain,
% 1.24/1.06      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 1.24/1.06      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_51,negated_conjecture,
% 1.24/1.06      ( v1_funct_1(sK3) ),
% 1.24/1.06      inference(cnf_transformation,[],[f111]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_31,plain,
% 1.24/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.24/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.24/1.06      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 1.24/1.06      | ~ v1_funct_1(X0)
% 1.24/1.06      | ~ v1_funct_1(X3) ),
% 1.24/1.06      inference(cnf_transformation,[],[f102]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_2165,plain,
% 1.24/1.06      ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.24/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.24/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.24/1.06      | ~ v1_funct_1(sK4)
% 1.24/1.06      | ~ v1_funct_1(sK3) ),
% 1.24/1.06      inference(instantiation,[status(thm)],[c_31]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_2859,plain,
% 1.24/1.06      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 1.24/1.06      inference(global_propositional_subsumption,
% 1.24/1.06                [status(thm)],
% 1.24/1.06                [c_1695,c_51,c_49,c_48,c_46,c_576,c_2165]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_9312,plain,
% 1.24/1.06      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
% 1.24/1.06      | v1_funct_1(sK3) != iProver_top ),
% 1.24/1.06      inference(light_normalisation,[status(thm)],[c_9311,c_2859]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_52,plain,
% 1.24/1.06      ( v1_funct_1(sK3) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_10003,plain,
% 1.24/1.06      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
% 1.24/1.06      inference(global_propositional_subsumption,
% 1.24/1.06                [status(thm)],
% 1.24/1.06                [c_9312,c_52]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_18,plain,
% 1.24/1.06      ( ~ v1_funct_1(X0)
% 1.24/1.06      | ~ v1_funct_1(X1)
% 1.24/1.06      | ~ v2_funct_1(X0)
% 1.24/1.06      | ~ v1_relat_1(X0)
% 1.24/1.06      | ~ v1_relat_1(X1)
% 1.24/1.06      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 1.24/1.06      | k2_funct_1(X0) = X1
% 1.24/1.06      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 1.24/1.06      inference(cnf_transformation,[],[f128]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1722,plain,
% 1.24/1.06      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 1.24/1.06      | k2_funct_1(X1) = X0
% 1.24/1.06      | k1_relat_1(X1) != k2_relat_1(X0)
% 1.24/1.06      | v1_funct_1(X1) != iProver_top
% 1.24/1.06      | v1_funct_1(X0) != iProver_top
% 1.24/1.06      | v2_funct_1(X1) != iProver_top
% 1.24/1.06      | v1_relat_1(X1) != iProver_top
% 1.24/1.06      | v1_relat_1(X0) != iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_10049,plain,
% 1.24/1.06      ( k2_funct_1(sK4) = sK3
% 1.24/1.06      | k6_partfun1(k2_relat_1(sK4)) != k6_partfun1(sK1)
% 1.24/1.06      | k1_relat_1(sK4) != k2_relat_1(sK3)
% 1.24/1.06      | v1_funct_1(sK4) != iProver_top
% 1.24/1.06      | v1_funct_1(sK3) != iProver_top
% 1.24/1.06      | v2_funct_1(sK4) != iProver_top
% 1.24/1.06      | v1_relat_1(sK4) != iProver_top
% 1.24/1.06      | v1_relat_1(sK3) != iProver_top ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_10003,c_1722]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_19,plain,
% 1.24/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.24/1.06      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.24/1.06      inference(cnf_transformation,[],[f89]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1721,plain,
% 1.24/1.06      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.24/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4137,plain,
% 1.24/1.06      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1699,c_1721]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_45,negated_conjecture,
% 1.24/1.06      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 1.24/1.06      inference(cnf_transformation,[],[f117]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4138,plain,
% 1.24/1.06      ( k2_relat_1(sK3) = sK2 ),
% 1.24/1.06      inference(light_normalisation,[status(thm)],[c_4137,c_45]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4136,plain,
% 1.24/1.06      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1702,c_1721]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_35,plain,
% 1.24/1.06      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 1.24/1.06      | ~ v1_funct_2(X3,X1,X0)
% 1.24/1.06      | ~ v1_funct_2(X2,X0,X1)
% 1.24/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 1.24/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.24/1.06      | ~ v1_funct_1(X2)
% 1.24/1.06      | ~ v1_funct_1(X3)
% 1.24/1.06      | k2_relset_1(X1,X0,X3) = X0 ),
% 1.24/1.06      inference(cnf_transformation,[],[f106]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_580,plain,
% 1.24/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 1.24/1.06      | ~ v1_funct_2(X3,X2,X1)
% 1.24/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.24/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.24/1.06      | ~ v1_funct_1(X3)
% 1.24/1.06      | ~ v1_funct_1(X0)
% 1.24/1.06      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 1.24/1.06      | k2_relset_1(X2,X1,X3) = X1
% 1.24/1.06      | k6_partfun1(X1) != k6_partfun1(sK1)
% 1.24/1.06      | sK1 != X1 ),
% 1.24/1.06      inference(resolution_lifted,[status(thm)],[c_35,c_44]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_581,plain,
% 1.24/1.06      ( ~ v1_funct_2(X0,X1,sK1)
% 1.24/1.06      | ~ v1_funct_2(X2,sK1,X1)
% 1.24/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 1.24/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 1.24/1.06      | ~ v1_funct_1(X2)
% 1.24/1.06      | ~ v1_funct_1(X0)
% 1.24/1.06      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 1.24/1.06      | k2_relset_1(X1,sK1,X0) = sK1
% 1.24/1.06      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 1.24/1.06      inference(unflattening,[status(thm)],[c_580]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_681,plain,
% 1.24/1.06      ( ~ v1_funct_2(X0,X1,sK1)
% 1.24/1.06      | ~ v1_funct_2(X2,sK1,X1)
% 1.24/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 1.24/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 1.24/1.06      | ~ v1_funct_1(X0)
% 1.24/1.06      | ~ v1_funct_1(X2)
% 1.24/1.06      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 1.24/1.06      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 1.24/1.06      inference(equality_resolution_simp,[status(thm)],[c_581]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1694,plain,
% 1.24/1.06      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 1.24/1.06      | k2_relset_1(X0,sK1,X2) = sK1
% 1.24/1.06      | v1_funct_2(X2,X0,sK1) != iProver_top
% 1.24/1.06      | v1_funct_2(X1,sK1,X0) != iProver_top
% 1.24/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 1.24/1.06      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 1.24/1.06      | v1_funct_1(X2) != iProver_top
% 1.24/1.06      | v1_funct_1(X1) != iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_2232,plain,
% 1.24/1.06      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 1.24/1.06      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 1.24/1.06      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 1.24/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.24/1.06      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 1.24/1.06      | v1_funct_1(sK4) != iProver_top
% 1.24/1.06      | v1_funct_1(sK3) != iProver_top ),
% 1.24/1.06      inference(equality_resolution,[status(thm)],[c_1694]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_50,negated_conjecture,
% 1.24/1.06      ( v1_funct_2(sK3,sK1,sK2) ),
% 1.24/1.06      inference(cnf_transformation,[],[f112]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_53,plain,
% 1.24/1.06      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_54,plain,
% 1.24/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_47,negated_conjecture,
% 1.24/1.06      ( v1_funct_2(sK4,sK2,sK1) ),
% 1.24/1.06      inference(cnf_transformation,[],[f115]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_56,plain,
% 1.24/1.06      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_57,plain,
% 1.24/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_2866,plain,
% 1.24/1.06      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 1.24/1.06      inference(global_propositional_subsumption,
% 1.24/1.06                [status(thm)],
% 1.24/1.06                [c_2232,c_52,c_53,c_54,c_55,c_56,c_57]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4139,plain,
% 1.24/1.06      ( k2_relat_1(sK4) = sK1 ),
% 1.24/1.06      inference(light_normalisation,[status(thm)],[c_4136,c_2866]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_10054,plain,
% 1.24/1.06      ( k2_funct_1(sK4) = sK3
% 1.24/1.06      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 1.24/1.06      | k1_relat_1(sK4) != sK2
% 1.24/1.06      | v1_funct_1(sK4) != iProver_top
% 1.24/1.06      | v1_funct_1(sK3) != iProver_top
% 1.24/1.06      | v2_funct_1(sK4) != iProver_top
% 1.24/1.06      | v1_relat_1(sK4) != iProver_top
% 1.24/1.06      | v1_relat_1(sK3) != iProver_top ),
% 1.24/1.06      inference(light_normalisation,
% 1.24/1.06                [status(thm)],
% 1.24/1.06                [c_10049,c_4138,c_4139]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_10055,plain,
% 1.24/1.06      ( k2_funct_1(sK4) = sK3
% 1.24/1.06      | k1_relat_1(sK4) != sK2
% 1.24/1.06      | v1_funct_1(sK4) != iProver_top
% 1.24/1.06      | v1_funct_1(sK3) != iProver_top
% 1.24/1.06      | v2_funct_1(sK4) != iProver_top
% 1.24/1.06      | v1_relat_1(sK4) != iProver_top
% 1.24/1.06      | v1_relat_1(sK3) != iProver_top ),
% 1.24/1.06      inference(equality_resolution_simp,[status(thm)],[c_10054]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1700,plain,
% 1.24/1.06      ( v1_funct_1(sK4) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_15,plain,
% 1.24/1.06      ( ~ v1_funct_1(X0)
% 1.24/1.06      | ~ v2_funct_1(X0)
% 1.24/1.06      | ~ v1_relat_1(X0)
% 1.24/1.06      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 1.24/1.06      inference(cnf_transformation,[],[f85]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1725,plain,
% 1.24/1.06      ( k2_funct_1(X0) = k4_relat_1(X0)
% 1.24/1.06      | v1_funct_1(X0) != iProver_top
% 1.24/1.06      | v2_funct_1(X0) != iProver_top
% 1.24/1.06      | v1_relat_1(X0) != iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_7401,plain,
% 1.24/1.06      ( k2_funct_1(sK4) = k4_relat_1(sK4)
% 1.24/1.06      | v2_funct_1(sK4) != iProver_top
% 1.24/1.06      | v1_relat_1(sK4) != iProver_top ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1700,c_1725]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4,plain,
% 1.24/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.24/1.06      | ~ v1_relat_1(X1)
% 1.24/1.06      | v1_relat_1(X0) ),
% 1.24/1.06      inference(cnf_transformation,[],[f74]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1890,plain,
% 1.24/1.06      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 1.24/1.06      | ~ v1_relat_1(X0)
% 1.24/1.06      | v1_relat_1(sK4) ),
% 1.24/1.06      inference(instantiation,[status(thm)],[c_4]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_2194,plain,
% 1.24/1.06      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.24/1.06      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 1.24/1.06      | v1_relat_1(sK4) ),
% 1.24/1.06      inference(instantiation,[status(thm)],[c_1890]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_3088,plain,
% 1.24/1.06      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.24/1.06      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
% 1.24/1.06      | v1_relat_1(sK4) ),
% 1.24/1.06      inference(instantiation,[status(thm)],[c_2194]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_3089,plain,
% 1.24/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.24/1.06      | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 1.24/1.06      | v1_relat_1(sK4) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_3088]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_6,plain,
% 1.24/1.06      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.24/1.06      inference(cnf_transformation,[],[f76]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_3388,plain,
% 1.24/1.06      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
% 1.24/1.06      inference(instantiation,[status(thm)],[c_6]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_3389,plain,
% 1.24/1.06      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_3388]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_16,plain,
% 1.24/1.06      ( v2_funct_1(k6_partfun1(X0)) ),
% 1.24/1.06      inference(cnf_transformation,[],[f126]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1724,plain,
% 1.24/1.06      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_37,plain,
% 1.24/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 1.24/1.06      | ~ v1_funct_2(X3,X4,X1)
% 1.24/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 1.24/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.24/1.06      | ~ v1_funct_1(X0)
% 1.24/1.06      | ~ v1_funct_1(X3)
% 1.24/1.06      | v2_funct_1(X0)
% 1.24/1.06      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 1.24/1.06      | k2_relset_1(X4,X1,X3) != X1
% 1.24/1.06      | k1_xboole_0 = X2 ),
% 1.24/1.06      inference(cnf_transformation,[],[f109]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1706,plain,
% 1.24/1.06      ( k2_relset_1(X0,X1,X2) != X1
% 1.24/1.06      | k1_xboole_0 = X3
% 1.24/1.06      | v1_funct_2(X4,X1,X3) != iProver_top
% 1.24/1.06      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.24/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.24/1.06      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 1.24/1.06      | v1_funct_1(X4) != iProver_top
% 1.24/1.06      | v1_funct_1(X2) != iProver_top
% 1.24/1.06      | v2_funct_1(X4) = iProver_top
% 1.24/1.06      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_0,plain,
% 1.24/1.06      ( v1_xboole_0(o_0_0_xboole_0) ),
% 1.24/1.06      inference(cnf_transformation,[],[f70]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1739,plain,
% 1.24/1.06      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1,plain,
% 1.24/1.06      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.24/1.06      inference(cnf_transformation,[],[f71]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1738,plain,
% 1.24/1.06      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_3054,plain,
% 1.24/1.06      ( k1_xboole_0 = o_0_0_xboole_0 ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1739,c_1738]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4738,plain,
% 1.24/1.06      ( k2_relset_1(X0,X1,X2) != X1
% 1.24/1.06      | o_0_0_xboole_0 = X3
% 1.24/1.06      | v1_funct_2(X4,X1,X3) != iProver_top
% 1.24/1.06      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.24/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.24/1.06      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 1.24/1.06      | v1_funct_1(X4) != iProver_top
% 1.24/1.06      | v1_funct_1(X2) != iProver_top
% 1.24/1.06      | v2_funct_1(X4) = iProver_top
% 1.24/1.06      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 1.24/1.06      inference(demodulation,[status(thm)],[c_1706,c_3054]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4740,plain,
% 1.24/1.06      ( o_0_0_xboole_0 = X0
% 1.24/1.06      | v1_funct_2(X1,sK2,X0) != iProver_top
% 1.24/1.06      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 1.24/1.06      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 1.24/1.06      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 1.24/1.06      | v1_funct_1(X1) != iProver_top
% 1.24/1.06      | v1_funct_1(sK3) != iProver_top
% 1.24/1.06      | v2_funct_1(X1) = iProver_top
% 1.24/1.06      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_45,c_4738]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_5227,plain,
% 1.24/1.06      ( v1_funct_1(X1) != iProver_top
% 1.24/1.06      | v1_funct_2(X1,sK2,X0) != iProver_top
% 1.24/1.06      | o_0_0_xboole_0 = X0
% 1.24/1.06      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 1.24/1.06      | v2_funct_1(X1) = iProver_top
% 1.24/1.06      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
% 1.24/1.06      inference(global_propositional_subsumption,
% 1.24/1.06                [status(thm)],
% 1.24/1.06                [c_4740,c_52,c_53,c_54]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_5228,plain,
% 1.24/1.06      ( o_0_0_xboole_0 = X0
% 1.24/1.06      | v1_funct_2(X1,sK2,X0) != iProver_top
% 1.24/1.06      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 1.24/1.06      | v1_funct_1(X1) != iProver_top
% 1.24/1.06      | v2_funct_1(X1) = iProver_top
% 1.24/1.06      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
% 1.24/1.06      inference(renaming,[status(thm)],[c_5227]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_5233,plain,
% 1.24/1.06      ( sK1 = o_0_0_xboole_0
% 1.24/1.06      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 1.24/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.24/1.06      | v1_funct_1(sK4) != iProver_top
% 1.24/1.06      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 1.24/1.06      | v2_funct_1(sK4) = iProver_top ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_2859,c_5228]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_42,negated_conjecture,
% 1.24/1.06      ( k1_xboole_0 != sK1 ),
% 1.24/1.06      inference(cnf_transformation,[],[f120]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1836,plain,
% 1.24/1.06      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 1.24/1.06      inference(instantiation,[status(thm)],[c_1]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_951,plain,
% 1.24/1.06      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.24/1.06      theory(equality) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1916,plain,
% 1.24/1.06      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 1.24/1.06      inference(instantiation,[status(thm)],[c_951]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_2225,plain,
% 1.24/1.06      ( v1_xboole_0(sK1)
% 1.24/1.06      | ~ v1_xboole_0(o_0_0_xboole_0)
% 1.24/1.06      | sK1 != o_0_0_xboole_0 ),
% 1.24/1.06      inference(instantiation,[status(thm)],[c_1916]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_5271,plain,
% 1.24/1.06      ( v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 1.24/1.06      | v2_funct_1(sK4) = iProver_top ),
% 1.24/1.06      inference(global_propositional_subsumption,
% 1.24/1.06                [status(thm)],
% 1.24/1.06                [c_5233,c_55,c_56,c_57,c_42,c_0,c_1836,c_2225]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_5275,plain,
% 1.24/1.06      ( v2_funct_1(sK4) = iProver_top ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1724,c_5271]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_7717,plain,
% 1.24/1.06      ( k2_funct_1(sK4) = k4_relat_1(sK4) ),
% 1.24/1.06      inference(global_propositional_subsumption,
% 1.24/1.06                [status(thm)],
% 1.24/1.06                [c_7401,c_57,c_3089,c_3389,c_5275]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_10056,plain,
% 1.24/1.06      ( k1_relat_1(sK4) != sK2
% 1.24/1.06      | k4_relat_1(sK4) = sK3
% 1.24/1.06      | v1_funct_1(sK4) != iProver_top
% 1.24/1.06      | v1_funct_1(sK3) != iProver_top
% 1.24/1.06      | v2_funct_1(sK4) != iProver_top
% 1.24/1.06      | v1_relat_1(sK4) != iProver_top
% 1.24/1.06      | v1_relat_1(sK3) != iProver_top ),
% 1.24/1.06      inference(demodulation,[status(thm)],[c_10055,c_7717]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1733,plain,
% 1.24/1.06      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1735,plain,
% 1.24/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.24/1.06      | v1_relat_1(X1) != iProver_top
% 1.24/1.06      | v1_relat_1(X0) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4190,plain,
% 1.24/1.06      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 1.24/1.06      | v1_relat_1(sK3) = iProver_top ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1699,c_1735]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4320,plain,
% 1.24/1.06      ( v1_relat_1(sK3) = iProver_top ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1733,c_4190]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_30,plain,
% 1.24/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 1.24/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.24/1.06      | k1_relset_1(X1,X2,X0) = X1
% 1.24/1.06      | k1_xboole_0 = X2 ),
% 1.24/1.06      inference(cnf_transformation,[],[f95]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1712,plain,
% 1.24/1.06      ( k1_relset_1(X0,X1,X2) = X0
% 1.24/1.06      | k1_xboole_0 = X1
% 1.24/1.06      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.24/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_9032,plain,
% 1.24/1.06      ( k1_relset_1(X0,X1,X2) = X0
% 1.24/1.06      | o_0_0_xboole_0 = X1
% 1.24/1.06      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.24/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.24/1.06      inference(demodulation,[status(thm)],[c_1712,c_3054]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_9036,plain,
% 1.24/1.06      ( k1_relset_1(sK2,sK1,sK4) = sK2
% 1.24/1.06      | sK1 = o_0_0_xboole_0
% 1.24/1.06      | v1_funct_2(sK4,sK2,sK1) != iProver_top ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1702,c_9032]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_23,plain,
% 1.24/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.24/1.06      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 1.24/1.06      inference(cnf_transformation,[],[f94]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1719,plain,
% 1.24/1.06      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 1.24/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_5907,plain,
% 1.24/1.06      ( k8_relset_1(sK2,sK1,sK4,sK1) = k1_relset_1(sK2,sK1,sK4) ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1702,c_1719]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4189,plain,
% 1.24/1.06      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 1.24/1.06      | v1_relat_1(sK4) = iProver_top ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1702,c_1735]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4194,plain,
% 1.24/1.06      ( v1_relat_1(sK4) = iProver_top ),
% 1.24/1.06      inference(global_propositional_subsumption,
% 1.24/1.06                [status(thm)],
% 1.24/1.06                [c_4189,c_57,c_3089,c_3389]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_8,plain,
% 1.24/1.06      ( ~ v1_relat_1(X0)
% 1.24/1.06      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 1.24/1.06      inference(cnf_transformation,[],[f78]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1731,plain,
% 1.24/1.06      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 1.24/1.06      | v1_relat_1(X0) != iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4199,plain,
% 1.24/1.06      ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_4194,c_1731]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4207,plain,
% 1.24/1.06      ( k10_relat_1(sK4,sK1) = k1_relat_1(sK4) ),
% 1.24/1.06      inference(light_normalisation,[status(thm)],[c_4199,c_4139]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_20,plain,
% 1.24/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.24/1.06      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.24/1.06      inference(cnf_transformation,[],[f90]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1720,plain,
% 1.24/1.06      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.24/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4926,plain,
% 1.24/1.06      ( k8_relset_1(sK2,sK1,sK4,X0) = k10_relat_1(sK4,X0) ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1702,c_1720]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_5910,plain,
% 1.24/1.06      ( k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4) ),
% 1.24/1.06      inference(demodulation,[status(thm)],[c_5907,c_4207,c_4926]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_9039,plain,
% 1.24/1.06      ( k1_relat_1(sK4) = sK2
% 1.24/1.06      | sK1 = o_0_0_xboole_0
% 1.24/1.06      | v1_funct_2(sK4,sK2,sK1) != iProver_top ),
% 1.24/1.06      inference(demodulation,[status(thm)],[c_9036,c_5910]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_11349,plain,
% 1.24/1.06      ( k4_relat_1(sK4) = sK3 ),
% 1.24/1.06      inference(global_propositional_subsumption,
% 1.24/1.06                [status(thm)],
% 1.24/1.06                [c_10056,c_52,c_55,c_56,c_57,c_42,c_0,c_1836,c_2225,
% 1.24/1.06                 c_3089,c_3389,c_4320,c_5275,c_9039]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_7,plain,
% 1.24/1.06      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 1.24/1.06      inference(cnf_transformation,[],[f77]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1732,plain,
% 1.24/1.06      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_4204,plain,
% 1.24/1.06      ( k4_relat_1(k4_relat_1(sK4)) = sK4 ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_4194,c_1732]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_11359,plain,
% 1.24/1.06      ( k4_relat_1(sK3) = sK4 ),
% 1.24/1.06      inference(demodulation,[status(thm)],[c_11349,c_4204]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_1697,plain,
% 1.24/1.06      ( v1_funct_1(sK3) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_7402,plain,
% 1.24/1.06      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 1.24/1.06      | v2_funct_1(sK3) != iProver_top
% 1.24/1.06      | v1_relat_1(sK3) != iProver_top ),
% 1.24/1.06      inference(superposition,[status(thm)],[c_1697,c_1725]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_43,negated_conjecture,
% 1.24/1.06      ( v2_funct_1(sK3) ),
% 1.24/1.06      inference(cnf_transformation,[],[f119]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_59,plain,
% 1.24/1.06      ( v2_funct_1(sK3) = iProver_top ),
% 1.24/1.06      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_7720,plain,
% 1.24/1.06      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 1.24/1.06      inference(global_propositional_subsumption,
% 1.24/1.06                [status(thm)],
% 1.24/1.06                [c_7402,c_59,c_4320]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_40,negated_conjecture,
% 1.24/1.06      ( k2_funct_1(sK3) != sK4 ),
% 1.24/1.06      inference(cnf_transformation,[],[f122]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(c_7722,plain,
% 1.24/1.06      ( k4_relat_1(sK3) != sK4 ),
% 1.24/1.06      inference(demodulation,[status(thm)],[c_7720,c_40]) ).
% 1.24/1.06  
% 1.24/1.06  cnf(contradiction,plain,
% 1.24/1.06      ( $false ),
% 1.24/1.06      inference(minisat,[status(thm)],[c_11359,c_7722]) ).
% 1.24/1.06  
% 1.24/1.06  
% 1.24/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 1.24/1.06  
% 1.24/1.06  ------                               Statistics
% 1.24/1.06  
% 1.24/1.06  ------ General
% 1.24/1.06  
% 1.24/1.06  abstr_ref_over_cycles:                  0
% 1.24/1.06  abstr_ref_under_cycles:                 0
% 1.24/1.06  gc_basic_clause_elim:                   0
% 1.24/1.06  forced_gc_time:                         0
% 1.24/1.06  parsing_time:                           0.023
% 1.24/1.06  unif_index_cands_time:                  0.
% 1.24/1.06  unif_index_add_time:                    0.
% 1.24/1.06  orderings_time:                         0.
% 1.24/1.06  out_proof_time:                         0.015
% 1.24/1.06  total_time:                             0.42
% 1.24/1.06  num_of_symbols:                         59
% 1.24/1.06  num_of_terms:                           17758
% 1.24/1.06  
% 1.24/1.06  ------ Preprocessing
% 1.24/1.06  
% 1.24/1.06  num_of_splits:                          0
% 1.24/1.06  num_of_split_atoms:                     0
% 1.24/1.06  num_of_reused_defs:                     0
% 1.24/1.06  num_eq_ax_congr_red:                    33
% 1.24/1.06  num_of_sem_filtered_clauses:            1
% 1.24/1.06  num_of_subtypes:                        0
% 1.24/1.06  monotx_restored_types:                  0
% 1.24/1.06  sat_num_of_epr_types:                   0
% 1.24/1.06  sat_num_of_non_cyclic_types:            0
% 1.24/1.06  sat_guarded_non_collapsed_types:        0
% 1.24/1.06  num_pure_diseq_elim:                    0
% 1.24/1.06  simp_replaced_by:                       0
% 1.24/1.06  res_preprocessed:                       246
% 1.24/1.06  prep_upred:                             0
% 1.24/1.06  prep_unflattend:                        12
% 1.24/1.06  smt_new_axioms:                         0
% 1.24/1.06  pred_elim_cands:                        6
% 1.24/1.06  pred_elim:                              1
% 1.24/1.06  pred_elim_cl:                           1
% 1.24/1.06  pred_elim_cycles:                       3
% 1.24/1.06  merged_defs:                            0
% 1.24/1.06  merged_defs_ncl:                        0
% 1.24/1.06  bin_hyper_res:                          0
% 1.24/1.06  prep_cycles:                            4
% 1.24/1.06  pred_elim_time:                         0.005
% 1.24/1.06  splitting_time:                         0.
% 1.24/1.06  sem_filter_time:                        0.
% 1.24/1.06  monotx_time:                            0.
% 1.24/1.06  subtype_inf_time:                       0.
% 1.24/1.06  
% 1.24/1.06  ------ Problem properties
% 1.24/1.06  
% 1.24/1.06  clauses:                                51
% 1.24/1.06  conjectures:                            11
% 1.24/1.06  epr:                                    11
% 1.24/1.06  horn:                                   45
% 1.24/1.06  ground:                                 14
% 1.24/1.06  unary:                                  18
% 1.24/1.06  binary:                                 13
% 1.24/1.06  lits:                                   155
% 1.24/1.06  lits_eq:                                43
% 1.24/1.06  fd_pure:                                0
% 1.24/1.06  fd_pseudo:                              0
% 1.24/1.06  fd_cond:                                6
% 1.24/1.06  fd_pseudo_cond:                         2
% 1.24/1.06  ac_symbols:                             0
% 1.24/1.06  
% 1.24/1.06  ------ Propositional Solver
% 1.24/1.06  
% 1.24/1.06  prop_solver_calls:                      29
% 1.24/1.06  prop_fast_solver_calls:                 1914
% 1.24/1.06  smt_solver_calls:                       0
% 1.24/1.06  smt_fast_solver_calls:                  0
% 1.24/1.06  prop_num_of_clauses:                    5637
% 1.24/1.06  prop_preprocess_simplified:             15208
% 1.24/1.06  prop_fo_subsumed:                       53
% 1.24/1.06  prop_solver_time:                       0.
% 1.24/1.06  smt_solver_time:                        0.
% 1.24/1.06  smt_fast_solver_time:                   0.
% 1.24/1.06  prop_fast_solver_time:                  0.
% 1.24/1.06  prop_unsat_core_time:                   0.
% 1.24/1.06  
% 1.24/1.06  ------ QBF
% 1.24/1.06  
% 1.24/1.06  qbf_q_res:                              0
% 1.24/1.06  qbf_num_tautologies:                    0
% 1.24/1.06  qbf_prep_cycles:                        0
% 1.24/1.06  
% 1.24/1.06  ------ BMC1
% 1.24/1.06  
% 1.24/1.06  bmc1_current_bound:                     -1
% 1.24/1.06  bmc1_last_solved_bound:                 -1
% 1.24/1.06  bmc1_unsat_core_size:                   -1
% 1.24/1.06  bmc1_unsat_core_parents_size:           -1
% 1.24/1.06  bmc1_merge_next_fun:                    0
% 1.24/1.06  bmc1_unsat_core_clauses_time:           0.
% 1.24/1.06  
% 1.24/1.06  ------ Instantiation
% 1.24/1.06  
% 1.24/1.06  inst_num_of_clauses:                    1635
% 1.24/1.06  inst_num_in_passive:                    559
% 1.24/1.06  inst_num_in_active:                     623
% 1.24/1.06  inst_num_in_unprocessed:                453
% 1.24/1.06  inst_num_of_loops:                      660
% 1.24/1.06  inst_num_of_learning_restarts:          0
% 1.24/1.06  inst_num_moves_active_passive:          36
% 1.24/1.06  inst_lit_activity:                      0
% 1.24/1.06  inst_lit_activity_moves:                0
% 1.24/1.06  inst_num_tautologies:                   0
% 1.24/1.06  inst_num_prop_implied:                  0
% 1.24/1.06  inst_num_existing_simplified:           0
% 1.24/1.06  inst_num_eq_res_simplified:             0
% 1.24/1.06  inst_num_child_elim:                    0
% 1.24/1.06  inst_num_of_dismatching_blockings:      403
% 1.24/1.06  inst_num_of_non_proper_insts:           1502
% 1.24/1.06  inst_num_of_duplicates:                 0
% 1.24/1.06  inst_inst_num_from_inst_to_res:         0
% 1.24/1.06  inst_dismatching_checking_time:         0.
% 1.24/1.06  
% 1.24/1.06  ------ Resolution
% 1.24/1.06  
% 1.24/1.06  res_num_of_clauses:                     0
% 1.24/1.06  res_num_in_passive:                     0
% 1.24/1.06  res_num_in_active:                      0
% 1.24/1.06  res_num_of_loops:                       250
% 1.24/1.06  res_forward_subset_subsumed:            99
% 1.24/1.06  res_backward_subset_subsumed:           0
% 1.24/1.06  res_forward_subsumed:                   0
% 1.24/1.06  res_backward_subsumed:                  0
% 1.24/1.06  res_forward_subsumption_resolution:     2
% 1.24/1.06  res_backward_subsumption_resolution:    0
% 1.24/1.06  res_clause_to_clause_subsumption:       387
% 1.24/1.06  res_orphan_elimination:                 0
% 1.24/1.06  res_tautology_del:                      35
% 1.24/1.06  res_num_eq_res_simplified:              1
% 1.24/1.06  res_num_sel_changes:                    0
% 1.24/1.06  res_moves_from_active_to_pass:          0
% 1.24/1.06  
% 1.24/1.06  ------ Superposition
% 1.24/1.06  
% 1.24/1.06  sup_time_total:                         0.
% 1.24/1.06  sup_time_generating:                    0.
% 1.24/1.06  sup_time_sim_full:                      0.
% 1.24/1.06  sup_time_sim_immed:                     0.
% 1.24/1.06  
% 1.24/1.06  sup_num_of_clauses:                     200
% 1.24/1.06  sup_num_in_active:                      112
% 1.24/1.06  sup_num_in_passive:                     88
% 1.24/1.06  sup_num_of_loops:                       131
% 1.24/1.06  sup_fw_superposition:                   108
% 1.24/1.06  sup_bw_superposition:                   75
% 1.24/1.06  sup_immediate_simplified:               74
% 1.24/1.06  sup_given_eliminated:                   1
% 1.24/1.06  comparisons_done:                       0
% 1.24/1.06  comparisons_avoided:                    0
% 1.24/1.06  
% 1.24/1.06  ------ Simplifications
% 1.24/1.06  
% 1.24/1.06  
% 1.24/1.06  sim_fw_subset_subsumed:                 11
% 1.24/1.06  sim_bw_subset_subsumed:                 1
% 1.24/1.06  sim_fw_subsumed:                        3
% 1.24/1.06  sim_bw_subsumed:                        3
% 1.24/1.06  sim_fw_subsumption_res:                 0
% 1.24/1.06  sim_bw_subsumption_res:                 0
% 1.24/1.06  sim_tautology_del:                      1
% 1.24/1.06  sim_eq_tautology_del:                   11
% 1.24/1.06  sim_eq_res_simp:                        1
% 1.24/1.06  sim_fw_demodulated:                     29
% 1.24/1.06  sim_bw_demodulated:                     17
% 1.24/1.06  sim_light_normalised:                   46
% 1.24/1.06  sim_joinable_taut:                      0
% 1.24/1.06  sim_joinable_simp:                      0
% 1.24/1.06  sim_ac_normalised:                      0
% 1.24/1.06  sim_smt_subsumption:                    0
% 1.24/1.06  
%------------------------------------------------------------------------------
