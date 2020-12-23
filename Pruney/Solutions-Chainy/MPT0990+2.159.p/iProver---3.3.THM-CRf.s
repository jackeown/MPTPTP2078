%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:30 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 566 expanded)
%              Number of clauses        :   86 ( 152 expanded)
%              Number of leaves         :   17 ( 148 expanded)
%              Depth                    :   18
%              Number of atoms          :  622 (4990 expanded)
%              Number of equality atoms :  285 (1819 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f44,f43])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f55,f69])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f85,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f83,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1870,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1872,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1874,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4299,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_1874])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4631,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4299,c_40])).

cnf(c_4632,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4631])).

cnf(c_4642,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1870,c_4632])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2278,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2505,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2278])).

cnf(c_3132,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2505])).

cnf(c_4624,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3132])).

cnf(c_4847,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4642,c_36,c_34,c_33,c_31,c_4624])).

cnf(c_12,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_361,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_21,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_369,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_361,c_21])).

cnf(c_1867,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_4850,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4847,c_1867])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1877,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4852,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4847,c_1877])).

cnf(c_5054,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4850,c_37,c_39,c_40,c_42,c_4852])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_200,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_4])).

cnf(c_201,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_200])).

cnf(c_1868,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_5277,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5054,c_1868])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1878,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3065,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1870,c_1878])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_910,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_911,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_910])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_913,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_911,c_34,c_26])).

cnf(c_3067,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3065,c_913])).

cnf(c_3064,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1872,c_1878])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_886,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X2
    | sK1 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_32])).

cnf(c_887,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_886])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_889,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_887,c_31,c_27])).

cnf(c_3070,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3064,c_889])).

cnf(c_1869,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1879,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3555,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_1879])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_902,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_903,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_902])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_905,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_903,c_36,c_34,c_30,c_28,c_26])).

cnf(c_3559,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3555,c_905])).

cnf(c_3,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3560,plain,
    ( k2_relat_1(sK2) = sK1
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3559,c_3])).

cnf(c_44,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2148,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2464,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_2465,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2464])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3076,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3077,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3076])).

cnf(c_3631,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3560,c_39,c_44,c_2465,c_3077])).

cnf(c_5285,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5277,c_3067,c_3070,c_3631])).

cnf(c_5286,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5285])).

cnf(c_3049,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3050,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3049])).

cnf(c_2461,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_2462,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2461])).

cnf(c_25,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f83])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5286,c_3077,c_3050,c_2465,c_2462,c_25,c_42,c_40,c_39,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:50:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.16/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/0.99  
% 3.16/0.99  ------  iProver source info
% 3.16/0.99  
% 3.16/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.16/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/0.99  git: non_committed_changes: false
% 3.16/0.99  git: last_make_outside_of_git: false
% 3.16/0.99  
% 3.16/0.99  ------ 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options
% 3.16/0.99  
% 3.16/0.99  --out_options                           all
% 3.16/0.99  --tptp_safe_out                         true
% 3.16/0.99  --problem_path                          ""
% 3.16/0.99  --include_path                          ""
% 3.16/0.99  --clausifier                            res/vclausify_rel
% 3.16/0.99  --clausifier_options                    --mode clausify
% 3.16/0.99  --stdin                                 false
% 3.16/0.99  --stats_out                             all
% 3.16/0.99  
% 3.16/0.99  ------ General Options
% 3.16/0.99  
% 3.16/0.99  --fof                                   false
% 3.16/0.99  --time_out_real                         305.
% 3.16/0.99  --time_out_virtual                      -1.
% 3.16/0.99  --symbol_type_check                     false
% 3.16/0.99  --clausify_out                          false
% 3.16/0.99  --sig_cnt_out                           false
% 3.16/0.99  --trig_cnt_out                          false
% 3.16/0.99  --trig_cnt_out_tolerance                1.
% 3.16/0.99  --trig_cnt_out_sk_spl                   false
% 3.16/0.99  --abstr_cl_out                          false
% 3.16/0.99  
% 3.16/0.99  ------ Global Options
% 3.16/0.99  
% 3.16/0.99  --schedule                              default
% 3.16/0.99  --add_important_lit                     false
% 3.16/0.99  --prop_solver_per_cl                    1000
% 3.16/0.99  --min_unsat_core                        false
% 3.16/0.99  --soft_assumptions                      false
% 3.16/0.99  --soft_lemma_size                       3
% 3.16/0.99  --prop_impl_unit_size                   0
% 3.16/0.99  --prop_impl_unit                        []
% 3.16/0.99  --share_sel_clauses                     true
% 3.16/0.99  --reset_solvers                         false
% 3.16/0.99  --bc_imp_inh                            [conj_cone]
% 3.16/0.99  --conj_cone_tolerance                   3.
% 3.16/0.99  --extra_neg_conj                        none
% 3.16/0.99  --large_theory_mode                     true
% 3.16/0.99  --prolific_symb_bound                   200
% 3.16/0.99  --lt_threshold                          2000
% 3.16/0.99  --clause_weak_htbl                      true
% 3.16/0.99  --gc_record_bc_elim                     false
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing Options
% 3.16/0.99  
% 3.16/0.99  --preprocessing_flag                    true
% 3.16/0.99  --time_out_prep_mult                    0.1
% 3.16/0.99  --splitting_mode                        input
% 3.16/0.99  --splitting_grd                         true
% 3.16/0.99  --splitting_cvd                         false
% 3.16/0.99  --splitting_cvd_svl                     false
% 3.16/0.99  --splitting_nvd                         32
% 3.16/0.99  --sub_typing                            true
% 3.16/0.99  --prep_gs_sim                           true
% 3.16/0.99  --prep_unflatten                        true
% 3.16/0.99  --prep_res_sim                          true
% 3.16/0.99  --prep_upred                            true
% 3.16/0.99  --prep_sem_filter                       exhaustive
% 3.16/0.99  --prep_sem_filter_out                   false
% 3.16/0.99  --pred_elim                             true
% 3.16/0.99  --res_sim_input                         true
% 3.16/0.99  --eq_ax_congr_red                       true
% 3.16/0.99  --pure_diseq_elim                       true
% 3.16/0.99  --brand_transform                       false
% 3.16/0.99  --non_eq_to_eq                          false
% 3.16/0.99  --prep_def_merge                        true
% 3.16/0.99  --prep_def_merge_prop_impl              false
% 3.16/0.99  --prep_def_merge_mbd                    true
% 3.16/0.99  --prep_def_merge_tr_red                 false
% 3.16/0.99  --prep_def_merge_tr_cl                  false
% 3.16/0.99  --smt_preprocessing                     true
% 3.16/0.99  --smt_ac_axioms                         fast
% 3.16/0.99  --preprocessed_out                      false
% 3.16/0.99  --preprocessed_stats                    false
% 3.16/0.99  
% 3.16/0.99  ------ Abstraction refinement Options
% 3.16/0.99  
% 3.16/0.99  --abstr_ref                             []
% 3.16/0.99  --abstr_ref_prep                        false
% 3.16/0.99  --abstr_ref_until_sat                   false
% 3.16/0.99  --abstr_ref_sig_restrict                funpre
% 3.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.99  --abstr_ref_under                       []
% 3.16/0.99  
% 3.16/0.99  ------ SAT Options
% 3.16/0.99  
% 3.16/0.99  --sat_mode                              false
% 3.16/0.99  --sat_fm_restart_options                ""
% 3.16/0.99  --sat_gr_def                            false
% 3.16/0.99  --sat_epr_types                         true
% 3.16/0.99  --sat_non_cyclic_types                  false
% 3.16/0.99  --sat_finite_models                     false
% 3.16/0.99  --sat_fm_lemmas                         false
% 3.16/0.99  --sat_fm_prep                           false
% 3.16/0.99  --sat_fm_uc_incr                        true
% 3.16/0.99  --sat_out_model                         small
% 3.16/0.99  --sat_out_clauses                       false
% 3.16/0.99  
% 3.16/0.99  ------ QBF Options
% 3.16/0.99  
% 3.16/0.99  --qbf_mode                              false
% 3.16/0.99  --qbf_elim_univ                         false
% 3.16/0.99  --qbf_dom_inst                          none
% 3.16/0.99  --qbf_dom_pre_inst                      false
% 3.16/0.99  --qbf_sk_in                             false
% 3.16/0.99  --qbf_pred_elim                         true
% 3.16/0.99  --qbf_split                             512
% 3.16/0.99  
% 3.16/0.99  ------ BMC1 Options
% 3.16/0.99  
% 3.16/0.99  --bmc1_incremental                      false
% 3.16/0.99  --bmc1_axioms                           reachable_all
% 3.16/0.99  --bmc1_min_bound                        0
% 3.16/0.99  --bmc1_max_bound                        -1
% 3.16/0.99  --bmc1_max_bound_default                -1
% 3.16/0.99  --bmc1_symbol_reachability              true
% 3.16/0.99  --bmc1_property_lemmas                  false
% 3.16/0.99  --bmc1_k_induction                      false
% 3.16/0.99  --bmc1_non_equiv_states                 false
% 3.16/0.99  --bmc1_deadlock                         false
% 3.16/0.99  --bmc1_ucm                              false
% 3.16/0.99  --bmc1_add_unsat_core                   none
% 3.16/0.99  --bmc1_unsat_core_children              false
% 3.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.99  --bmc1_out_stat                         full
% 3.16/0.99  --bmc1_ground_init                      false
% 3.16/0.99  --bmc1_pre_inst_next_state              false
% 3.16/0.99  --bmc1_pre_inst_state                   false
% 3.16/0.99  --bmc1_pre_inst_reach_state             false
% 3.16/0.99  --bmc1_out_unsat_core                   false
% 3.16/0.99  --bmc1_aig_witness_out                  false
% 3.16/0.99  --bmc1_verbose                          false
% 3.16/0.99  --bmc1_dump_clauses_tptp                false
% 3.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.99  --bmc1_dump_file                        -
% 3.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.99  --bmc1_ucm_extend_mode                  1
% 3.16/0.99  --bmc1_ucm_init_mode                    2
% 3.16/0.99  --bmc1_ucm_cone_mode                    none
% 3.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.99  --bmc1_ucm_relax_model                  4
% 3.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.99  --bmc1_ucm_layered_model                none
% 3.16/0.99  --bmc1_ucm_max_lemma_size               10
% 3.16/0.99  
% 3.16/0.99  ------ AIG Options
% 3.16/0.99  
% 3.16/0.99  --aig_mode                              false
% 3.16/0.99  
% 3.16/0.99  ------ Instantiation Options
% 3.16/0.99  
% 3.16/0.99  --instantiation_flag                    true
% 3.16/0.99  --inst_sos_flag                         false
% 3.16/0.99  --inst_sos_phase                        true
% 3.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel_side                     num_symb
% 3.16/0.99  --inst_solver_per_active                1400
% 3.16/0.99  --inst_solver_calls_frac                1.
% 3.16/0.99  --inst_passive_queue_type               priority_queues
% 3.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.99  --inst_passive_queues_freq              [25;2]
% 3.16/0.99  --inst_dismatching                      true
% 3.16/0.99  --inst_eager_unprocessed_to_passive     true
% 3.16/0.99  --inst_prop_sim_given                   true
% 3.16/0.99  --inst_prop_sim_new                     false
% 3.16/0.99  --inst_subs_new                         false
% 3.16/0.99  --inst_eq_res_simp                      false
% 3.16/0.99  --inst_subs_given                       false
% 3.16/0.99  --inst_orphan_elimination               true
% 3.16/0.99  --inst_learning_loop_flag               true
% 3.16/0.99  --inst_learning_start                   3000
% 3.16/0.99  --inst_learning_factor                  2
% 3.16/0.99  --inst_start_prop_sim_after_learn       3
% 3.16/0.99  --inst_sel_renew                        solver
% 3.16/0.99  --inst_lit_activity_flag                true
% 3.16/0.99  --inst_restr_to_given                   false
% 3.16/0.99  --inst_activity_threshold               500
% 3.16/0.99  --inst_out_proof                        true
% 3.16/0.99  
% 3.16/0.99  ------ Resolution Options
% 3.16/0.99  
% 3.16/0.99  --resolution_flag                       true
% 3.16/0.99  --res_lit_sel                           adaptive
% 3.16/0.99  --res_lit_sel_side                      none
% 3.16/0.99  --res_ordering                          kbo
% 3.16/0.99  --res_to_prop_solver                    active
% 3.16/0.99  --res_prop_simpl_new                    false
% 3.16/0.99  --res_prop_simpl_given                  true
% 3.16/0.99  --res_passive_queue_type                priority_queues
% 3.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.99  --res_passive_queues_freq               [15;5]
% 3.16/0.99  --res_forward_subs                      full
% 3.16/0.99  --res_backward_subs                     full
% 3.16/0.99  --res_forward_subs_resolution           true
% 3.16/0.99  --res_backward_subs_resolution          true
% 3.16/0.99  --res_orphan_elimination                true
% 3.16/0.99  --res_time_limit                        2.
% 3.16/0.99  --res_out_proof                         true
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Options
% 3.16/0.99  
% 3.16/0.99  --superposition_flag                    true
% 3.16/0.99  --sup_passive_queue_type                priority_queues
% 3.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.99  --demod_completeness_check              fast
% 3.16/0.99  --demod_use_ground                      true
% 3.16/0.99  --sup_to_prop_solver                    passive
% 3.16/0.99  --sup_prop_simpl_new                    true
% 3.16/0.99  --sup_prop_simpl_given                  true
% 3.16/0.99  --sup_fun_splitting                     false
% 3.16/0.99  --sup_smt_interval                      50000
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Simplification Setup
% 3.16/0.99  
% 3.16/0.99  --sup_indices_passive                   []
% 3.16/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_full_bw                           [BwDemod]
% 3.16/0.99  --sup_immed_triv                        [TrivRules]
% 3.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_immed_bw_main                     []
% 3.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  
% 3.16/0.99  ------ Combination Options
% 3.16/0.99  
% 3.16/0.99  --comb_res_mult                         3
% 3.16/0.99  --comb_sup_mult                         2
% 3.16/0.99  --comb_inst_mult                        10
% 3.16/0.99  
% 3.16/0.99  ------ Debug Options
% 3.16/0.99  
% 3.16/0.99  --dbg_backtrace                         false
% 3.16/0.99  --dbg_dump_prop_clauses                 false
% 3.16/0.99  --dbg_dump_prop_clauses_file            -
% 3.16/0.99  --dbg_out_stat                          false
% 3.16/0.99  ------ Parsing...
% 3.16/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/0.99  ------ Proving...
% 3.16/0.99  ------ Problem Properties 
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  clauses                                 37
% 3.16/0.99  conjectures                             9
% 3.16/0.99  EPR                                     5
% 3.16/0.99  Horn                                    35
% 3.16/0.99  unary                                   17
% 3.16/0.99  binary                                  2
% 3.16/0.99  lits                                    100
% 3.16/0.99  lits eq                                 41
% 3.16/0.99  fd_pure                                 0
% 3.16/0.99  fd_pseudo                               0
% 3.16/0.99  fd_cond                                 2
% 3.16/0.99  fd_pseudo_cond                          1
% 3.16/0.99  AC symbols                              0
% 3.16/0.99  
% 3.16/0.99  ------ Schedule dynamic 5 is on 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  ------ 
% 3.16/0.99  Current options:
% 3.16/0.99  ------ 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options
% 3.16/0.99  
% 3.16/0.99  --out_options                           all
% 3.16/0.99  --tptp_safe_out                         true
% 3.16/0.99  --problem_path                          ""
% 3.16/0.99  --include_path                          ""
% 3.16/0.99  --clausifier                            res/vclausify_rel
% 3.16/0.99  --clausifier_options                    --mode clausify
% 3.16/0.99  --stdin                                 false
% 3.16/0.99  --stats_out                             all
% 3.16/0.99  
% 3.16/0.99  ------ General Options
% 3.16/0.99  
% 3.16/0.99  --fof                                   false
% 3.16/0.99  --time_out_real                         305.
% 3.16/0.99  --time_out_virtual                      -1.
% 3.16/0.99  --symbol_type_check                     false
% 3.16/0.99  --clausify_out                          false
% 3.16/0.99  --sig_cnt_out                           false
% 3.16/0.99  --trig_cnt_out                          false
% 3.16/0.99  --trig_cnt_out_tolerance                1.
% 3.16/0.99  --trig_cnt_out_sk_spl                   false
% 3.16/0.99  --abstr_cl_out                          false
% 3.16/0.99  
% 3.16/0.99  ------ Global Options
% 3.16/0.99  
% 3.16/0.99  --schedule                              default
% 3.16/0.99  --add_important_lit                     false
% 3.16/0.99  --prop_solver_per_cl                    1000
% 3.16/0.99  --min_unsat_core                        false
% 3.16/0.99  --soft_assumptions                      false
% 3.16/0.99  --soft_lemma_size                       3
% 3.16/0.99  --prop_impl_unit_size                   0
% 3.16/0.99  --prop_impl_unit                        []
% 3.16/0.99  --share_sel_clauses                     true
% 3.16/0.99  --reset_solvers                         false
% 3.16/0.99  --bc_imp_inh                            [conj_cone]
% 3.16/0.99  --conj_cone_tolerance                   3.
% 3.16/0.99  --extra_neg_conj                        none
% 3.16/0.99  --large_theory_mode                     true
% 3.16/0.99  --prolific_symb_bound                   200
% 3.16/0.99  --lt_threshold                          2000
% 3.16/0.99  --clause_weak_htbl                      true
% 3.16/0.99  --gc_record_bc_elim                     false
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing Options
% 3.16/0.99  
% 3.16/0.99  --preprocessing_flag                    true
% 3.16/0.99  --time_out_prep_mult                    0.1
% 3.16/0.99  --splitting_mode                        input
% 3.16/0.99  --splitting_grd                         true
% 3.16/0.99  --splitting_cvd                         false
% 3.16/0.99  --splitting_cvd_svl                     false
% 3.16/0.99  --splitting_nvd                         32
% 3.16/0.99  --sub_typing                            true
% 3.16/0.99  --prep_gs_sim                           true
% 3.16/0.99  --prep_unflatten                        true
% 3.16/0.99  --prep_res_sim                          true
% 3.16/0.99  --prep_upred                            true
% 3.16/0.99  --prep_sem_filter                       exhaustive
% 3.16/0.99  --prep_sem_filter_out                   false
% 3.16/0.99  --pred_elim                             true
% 3.16/0.99  --res_sim_input                         true
% 3.16/0.99  --eq_ax_congr_red                       true
% 3.16/0.99  --pure_diseq_elim                       true
% 3.16/0.99  --brand_transform                       false
% 3.16/0.99  --non_eq_to_eq                          false
% 3.16/0.99  --prep_def_merge                        true
% 3.16/0.99  --prep_def_merge_prop_impl              false
% 3.16/0.99  --prep_def_merge_mbd                    true
% 3.16/0.99  --prep_def_merge_tr_red                 false
% 3.16/0.99  --prep_def_merge_tr_cl                  false
% 3.16/0.99  --smt_preprocessing                     true
% 3.16/0.99  --smt_ac_axioms                         fast
% 3.16/0.99  --preprocessed_out                      false
% 3.16/0.99  --preprocessed_stats                    false
% 3.16/0.99  
% 3.16/0.99  ------ Abstraction refinement Options
% 3.16/0.99  
% 3.16/0.99  --abstr_ref                             []
% 3.16/0.99  --abstr_ref_prep                        false
% 3.16/0.99  --abstr_ref_until_sat                   false
% 3.16/0.99  --abstr_ref_sig_restrict                funpre
% 3.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.99  --abstr_ref_under                       []
% 3.16/0.99  
% 3.16/0.99  ------ SAT Options
% 3.16/0.99  
% 3.16/0.99  --sat_mode                              false
% 3.16/0.99  --sat_fm_restart_options                ""
% 3.16/0.99  --sat_gr_def                            false
% 3.16/0.99  --sat_epr_types                         true
% 3.16/0.99  --sat_non_cyclic_types                  false
% 3.16/0.99  --sat_finite_models                     false
% 3.16/0.99  --sat_fm_lemmas                         false
% 3.16/0.99  --sat_fm_prep                           false
% 3.16/0.99  --sat_fm_uc_incr                        true
% 3.16/0.99  --sat_out_model                         small
% 3.16/0.99  --sat_out_clauses                       false
% 3.16/0.99  
% 3.16/0.99  ------ QBF Options
% 3.16/0.99  
% 3.16/0.99  --qbf_mode                              false
% 3.16/0.99  --qbf_elim_univ                         false
% 3.16/0.99  --qbf_dom_inst                          none
% 3.16/0.99  --qbf_dom_pre_inst                      false
% 3.16/0.99  --qbf_sk_in                             false
% 3.16/0.99  --qbf_pred_elim                         true
% 3.16/0.99  --qbf_split                             512
% 3.16/0.99  
% 3.16/0.99  ------ BMC1 Options
% 3.16/0.99  
% 3.16/0.99  --bmc1_incremental                      false
% 3.16/0.99  --bmc1_axioms                           reachable_all
% 3.16/0.99  --bmc1_min_bound                        0
% 3.16/0.99  --bmc1_max_bound                        -1
% 3.16/0.99  --bmc1_max_bound_default                -1
% 3.16/0.99  --bmc1_symbol_reachability              true
% 3.16/0.99  --bmc1_property_lemmas                  false
% 3.16/0.99  --bmc1_k_induction                      false
% 3.16/0.99  --bmc1_non_equiv_states                 false
% 3.16/0.99  --bmc1_deadlock                         false
% 3.16/0.99  --bmc1_ucm                              false
% 3.16/0.99  --bmc1_add_unsat_core                   none
% 3.16/0.99  --bmc1_unsat_core_children              false
% 3.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.99  --bmc1_out_stat                         full
% 3.16/0.99  --bmc1_ground_init                      false
% 3.16/0.99  --bmc1_pre_inst_next_state              false
% 3.16/0.99  --bmc1_pre_inst_state                   false
% 3.16/0.99  --bmc1_pre_inst_reach_state             false
% 3.16/0.99  --bmc1_out_unsat_core                   false
% 3.16/0.99  --bmc1_aig_witness_out                  false
% 3.16/0.99  --bmc1_verbose                          false
% 3.16/0.99  --bmc1_dump_clauses_tptp                false
% 3.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.99  --bmc1_dump_file                        -
% 3.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.99  --bmc1_ucm_extend_mode                  1
% 3.16/0.99  --bmc1_ucm_init_mode                    2
% 3.16/0.99  --bmc1_ucm_cone_mode                    none
% 3.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.99  --bmc1_ucm_relax_model                  4
% 3.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.99  --bmc1_ucm_layered_model                none
% 3.16/0.99  --bmc1_ucm_max_lemma_size               10
% 3.16/0.99  
% 3.16/0.99  ------ AIG Options
% 3.16/0.99  
% 3.16/0.99  --aig_mode                              false
% 3.16/0.99  
% 3.16/0.99  ------ Instantiation Options
% 3.16/0.99  
% 3.16/0.99  --instantiation_flag                    true
% 3.16/0.99  --inst_sos_flag                         false
% 3.16/0.99  --inst_sos_phase                        true
% 3.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel_side                     none
% 3.16/0.99  --inst_solver_per_active                1400
% 3.16/0.99  --inst_solver_calls_frac                1.
% 3.16/0.99  --inst_passive_queue_type               priority_queues
% 3.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.99  --inst_passive_queues_freq              [25;2]
% 3.16/0.99  --inst_dismatching                      true
% 3.16/0.99  --inst_eager_unprocessed_to_passive     true
% 3.16/0.99  --inst_prop_sim_given                   true
% 3.16/0.99  --inst_prop_sim_new                     false
% 3.16/0.99  --inst_subs_new                         false
% 3.16/0.99  --inst_eq_res_simp                      false
% 3.16/0.99  --inst_subs_given                       false
% 3.16/0.99  --inst_orphan_elimination               true
% 3.16/0.99  --inst_learning_loop_flag               true
% 3.16/0.99  --inst_learning_start                   3000
% 3.16/0.99  --inst_learning_factor                  2
% 3.16/0.99  --inst_start_prop_sim_after_learn       3
% 3.16/0.99  --inst_sel_renew                        solver
% 3.16/0.99  --inst_lit_activity_flag                true
% 3.16/0.99  --inst_restr_to_given                   false
% 3.16/0.99  --inst_activity_threshold               500
% 3.16/0.99  --inst_out_proof                        true
% 3.16/0.99  
% 3.16/0.99  ------ Resolution Options
% 3.16/0.99  
% 3.16/0.99  --resolution_flag                       false
% 3.16/0.99  --res_lit_sel                           adaptive
% 3.16/0.99  --res_lit_sel_side                      none
% 3.16/0.99  --res_ordering                          kbo
% 3.16/0.99  --res_to_prop_solver                    active
% 3.16/0.99  --res_prop_simpl_new                    false
% 3.16/0.99  --res_prop_simpl_given                  true
% 3.16/0.99  --res_passive_queue_type                priority_queues
% 3.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.99  --res_passive_queues_freq               [15;5]
% 3.16/0.99  --res_forward_subs                      full
% 3.16/0.99  --res_backward_subs                     full
% 3.16/0.99  --res_forward_subs_resolution           true
% 3.16/0.99  --res_backward_subs_resolution          true
% 3.16/0.99  --res_orphan_elimination                true
% 3.16/0.99  --res_time_limit                        2.
% 3.16/0.99  --res_out_proof                         true
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Options
% 3.16/0.99  
% 3.16/0.99  --superposition_flag                    true
% 3.16/0.99  --sup_passive_queue_type                priority_queues
% 3.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.99  --demod_completeness_check              fast
% 3.16/0.99  --demod_use_ground                      true
% 3.16/0.99  --sup_to_prop_solver                    passive
% 3.16/0.99  --sup_prop_simpl_new                    true
% 3.16/0.99  --sup_prop_simpl_given                  true
% 3.16/0.99  --sup_fun_splitting                     false
% 3.16/0.99  --sup_smt_interval                      50000
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Simplification Setup
% 3.16/0.99  
% 3.16/0.99  --sup_indices_passive                   []
% 3.16/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_full_bw                           [BwDemod]
% 3.16/0.99  --sup_immed_triv                        [TrivRules]
% 3.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_immed_bw_main                     []
% 3.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  
% 3.16/0.99  ------ Combination Options
% 3.16/0.99  
% 3.16/0.99  --comb_res_mult                         3
% 3.16/0.99  --comb_sup_mult                         2
% 3.16/0.99  --comb_inst_mult                        10
% 3.16/0.99  
% 3.16/0.99  ------ Debug Options
% 3.16/0.99  
% 3.16/0.99  --dbg_backtrace                         false
% 3.16/0.99  --dbg_dump_prop_clauses                 false
% 3.16/0.99  --dbg_dump_prop_clauses_file            -
% 3.16/0.99  --dbg_out_stat                          false
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  ------ Proving...
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  % SZS status Theorem for theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  fof(f16,conjecture,(
% 3.16/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f17,negated_conjecture,(
% 3.16/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.16/0.99    inference(negated_conjecture,[],[f16])).
% 3.16/0.99  
% 3.16/0.99  fof(f39,plain,(
% 3.16/0.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.16/0.99    inference(ennf_transformation,[],[f17])).
% 3.16/0.99  
% 3.16/0.99  fof(f40,plain,(
% 3.16/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.16/0.99    inference(flattening,[],[f39])).
% 3.16/0.99  
% 3.16/0.99  fof(f44,plain,(
% 3.16/0.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.16/0.99    introduced(choice_axiom,[])).
% 3.16/0.99  
% 3.16/0.99  fof(f43,plain,(
% 3.16/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.16/0.99    introduced(choice_axiom,[])).
% 3.16/0.99  
% 3.16/0.99  fof(f45,plain,(
% 3.16/0.99    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.16/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f44,f43])).
% 3.16/0.99  
% 3.16/0.99  fof(f74,plain,(
% 3.16/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.16/0.99    inference(cnf_transformation,[],[f45])).
% 3.16/0.99  
% 3.16/0.99  fof(f77,plain,(
% 3.16/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.16/0.99    inference(cnf_transformation,[],[f45])).
% 3.16/0.99  
% 3.16/0.99  fof(f13,axiom,(
% 3.16/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f35,plain,(
% 3.16/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.16/0.99    inference(ennf_transformation,[],[f13])).
% 3.16/0.99  
% 3.16/0.99  fof(f36,plain,(
% 3.16/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.16/0.99    inference(flattening,[],[f35])).
% 3.16/0.99  
% 3.16/0.99  fof(f68,plain,(
% 3.16/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f36])).
% 3.16/0.99  
% 3.16/0.99  fof(f75,plain,(
% 3.16/0.99    v1_funct_1(sK3)),
% 3.16/0.99    inference(cnf_transformation,[],[f45])).
% 3.16/0.99  
% 3.16/0.99  fof(f72,plain,(
% 3.16/0.99    v1_funct_1(sK2)),
% 3.16/0.99    inference(cnf_transformation,[],[f45])).
% 3.16/0.99  
% 3.16/0.99  fof(f9,axiom,(
% 3.16/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f29,plain,(
% 3.16/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.16/0.99    inference(ennf_transformation,[],[f9])).
% 3.16/0.99  
% 3.16/0.99  fof(f30,plain,(
% 3.16/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.99    inference(flattening,[],[f29])).
% 3.16/0.99  
% 3.16/0.99  fof(f41,plain,(
% 3.16/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.99    inference(nnf_transformation,[],[f30])).
% 3.16/0.99  
% 3.16/0.99  fof(f57,plain,(
% 3.16/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/0.99    inference(cnf_transformation,[],[f41])).
% 3.16/0.99  
% 3.16/0.99  fof(f79,plain,(
% 3.16/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.16/0.99    inference(cnf_transformation,[],[f45])).
% 3.16/0.99  
% 3.16/0.99  fof(f12,axiom,(
% 3.16/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f18,plain,(
% 3.16/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.16/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.16/0.99  
% 3.16/0.99  fof(f67,plain,(
% 3.16/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.16/0.99    inference(cnf_transformation,[],[f18])).
% 3.16/0.99  
% 3.16/0.99  fof(f11,axiom,(
% 3.16/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f33,plain,(
% 3.16/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.16/0.99    inference(ennf_transformation,[],[f11])).
% 3.16/0.99  
% 3.16/0.99  fof(f34,plain,(
% 3.16/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.16/0.99    inference(flattening,[],[f33])).
% 3.16/0.99  
% 3.16/0.99  fof(f66,plain,(
% 3.16/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f34])).
% 3.16/0.99  
% 3.16/0.99  fof(f7,axiom,(
% 3.16/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f26,plain,(
% 3.16/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.16/0.99    inference(ennf_transformation,[],[f7])).
% 3.16/0.99  
% 3.16/0.99  fof(f27,plain,(
% 3.16/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.16/0.99    inference(flattening,[],[f26])).
% 3.16/0.99  
% 3.16/0.99  fof(f55,plain,(
% 3.16/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f27])).
% 3.16/0.99  
% 3.16/0.99  fof(f14,axiom,(
% 3.16/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f69,plain,(
% 3.16/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f14])).
% 3.16/0.99  
% 3.16/0.99  fof(f87,plain,(
% 3.16/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.16/0.99    inference(definition_unfolding,[],[f55,f69])).
% 3.16/0.99  
% 3.16/0.99  fof(f4,axiom,(
% 3.16/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f20,plain,(
% 3.16/0.99    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.16/0.99    inference(ennf_transformation,[],[f4])).
% 3.16/0.99  
% 3.16/0.99  fof(f21,plain,(
% 3.16/0.99    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.16/0.99    inference(flattening,[],[f20])).
% 3.16/0.99  
% 3.16/0.99  fof(f50,plain,(
% 3.16/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f21])).
% 3.16/0.99  
% 3.16/0.99  fof(f86,plain,(
% 3.16/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.16/0.99    inference(definition_unfolding,[],[f50,f69])).
% 3.16/0.99  
% 3.16/0.99  fof(f8,axiom,(
% 3.16/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f28,plain,(
% 3.16/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.99    inference(ennf_transformation,[],[f8])).
% 3.16/0.99  
% 3.16/0.99  fof(f56,plain,(
% 3.16/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/0.99    inference(cnf_transformation,[],[f28])).
% 3.16/0.99  
% 3.16/0.99  fof(f10,axiom,(
% 3.16/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f31,plain,(
% 3.16/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.99    inference(ennf_transformation,[],[f10])).
% 3.16/0.99  
% 3.16/0.99  fof(f32,plain,(
% 3.16/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.99    inference(flattening,[],[f31])).
% 3.16/0.99  
% 3.16/0.99  fof(f42,plain,(
% 3.16/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.99    inference(nnf_transformation,[],[f32])).
% 3.16/0.99  
% 3.16/0.99  fof(f59,plain,(
% 3.16/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/0.99    inference(cnf_transformation,[],[f42])).
% 3.16/0.99  
% 3.16/0.99  fof(f73,plain,(
% 3.16/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.16/0.99    inference(cnf_transformation,[],[f45])).
% 3.16/0.99  
% 3.16/0.99  fof(f82,plain,(
% 3.16/0.99    k1_xboole_0 != sK1),
% 3.16/0.99    inference(cnf_transformation,[],[f45])).
% 3.16/0.99  
% 3.16/0.99  fof(f76,plain,(
% 3.16/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.16/0.99    inference(cnf_transformation,[],[f45])).
% 3.16/0.99  
% 3.16/0.99  fof(f81,plain,(
% 3.16/0.99    k1_xboole_0 != sK0),
% 3.16/0.99    inference(cnf_transformation,[],[f45])).
% 3.16/0.99  
% 3.16/0.99  fof(f6,axiom,(
% 3.16/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f24,plain,(
% 3.16/0.99    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.16/0.99    inference(ennf_transformation,[],[f6])).
% 3.16/0.99  
% 3.16/0.99  fof(f25,plain,(
% 3.16/0.99    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.16/0.99    inference(flattening,[],[f24])).
% 3.16/0.99  
% 3.16/0.99  fof(f53,plain,(
% 3.16/0.99    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f25])).
% 3.16/0.99  
% 3.16/0.99  fof(f15,axiom,(
% 3.16/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f37,plain,(
% 3.16/0.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.16/0.99    inference(ennf_transformation,[],[f15])).
% 3.16/0.99  
% 3.16/0.99  fof(f38,plain,(
% 3.16/0.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.16/0.99    inference(flattening,[],[f37])).
% 3.16/0.99  
% 3.16/0.99  fof(f71,plain,(
% 3.16/0.99    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f38])).
% 3.16/0.99  
% 3.16/0.99  fof(f78,plain,(
% 3.16/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.16/0.99    inference(cnf_transformation,[],[f45])).
% 3.16/0.99  
% 3.16/0.99  fof(f80,plain,(
% 3.16/0.99    v2_funct_1(sK2)),
% 3.16/0.99    inference(cnf_transformation,[],[f45])).
% 3.16/0.99  
% 3.16/0.99  fof(f3,axiom,(
% 3.16/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f48,plain,(
% 3.16/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.16/0.99    inference(cnf_transformation,[],[f3])).
% 3.16/0.99  
% 3.16/0.99  fof(f85,plain,(
% 3.16/0.99    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.16/0.99    inference(definition_unfolding,[],[f48,f69])).
% 3.16/0.99  
% 3.16/0.99  fof(f1,axiom,(
% 3.16/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f19,plain,(
% 3.16/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.16/0.99    inference(ennf_transformation,[],[f1])).
% 3.16/0.99  
% 3.16/0.99  fof(f46,plain,(
% 3.16/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f19])).
% 3.16/0.99  
% 3.16/0.99  fof(f2,axiom,(
% 3.16/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f47,plain,(
% 3.16/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.16/0.99    inference(cnf_transformation,[],[f2])).
% 3.16/0.99  
% 3.16/0.99  fof(f83,plain,(
% 3.16/0.99    k2_funct_1(sK2) != sK3),
% 3.16/0.99    inference(cnf_transformation,[],[f45])).
% 3.16/0.99  
% 3.16/0.99  cnf(c_34,negated_conjecture,
% 3.16/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.16/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1870,plain,
% 3.16/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_31,negated_conjecture,
% 3.16/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.16/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1872,plain,
% 3.16/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_22,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.16/0.99      | ~ v1_funct_1(X0)
% 3.16/0.99      | ~ v1_funct_1(X3)
% 3.16/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.16/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1874,plain,
% 3.16/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.16/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.16/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.16/0.99      | v1_funct_1(X5) != iProver_top
% 3.16/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_4299,plain,
% 3.16/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.16/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.16/0.99      | v1_funct_1(X2) != iProver_top
% 3.16/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.16/0.99      inference(superposition,[status(thm)],[c_1872,c_1874]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_33,negated_conjecture,
% 3.16/0.99      ( v1_funct_1(sK3) ),
% 3.16/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_40,plain,
% 3.16/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_4631,plain,
% 3.16/0.99      ( v1_funct_1(X2) != iProver_top
% 3.16/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.16/0.99      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_4299,c_40]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_4632,plain,
% 3.16/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.16/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.16/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.16/0.99      inference(renaming,[status(thm)],[c_4631]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_4642,plain,
% 3.16/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.16/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.16/0.99      inference(superposition,[status(thm)],[c_1870,c_4632]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_36,negated_conjecture,
% 3.16/0.99      ( v1_funct_1(sK2) ),
% 3.16/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2278,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.16/0.99      | ~ v1_funct_1(X0)
% 3.16/0.99      | ~ v1_funct_1(sK3)
% 3.16/0.99      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2505,plain,
% 3.16/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.16/0.99      | ~ v1_funct_1(sK3)
% 3.16/0.99      | ~ v1_funct_1(sK2)
% 3.16/0.99      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_2278]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3132,plain,
% 3.16/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.16/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/0.99      | ~ v1_funct_1(sK3)
% 3.16/0.99      | ~ v1_funct_1(sK2)
% 3.16/0.99      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_2505]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_4624,plain,
% 3.16/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.16/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.16/0.99      | ~ v1_funct_1(sK3)
% 3.16/0.99      | ~ v1_funct_1(sK2)
% 3.16/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_3132]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_4847,plain,
% 3.16/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_4642,c_36,c_34,c_33,c_31,c_4624]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_12,plain,
% 3.16/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/0.99      | X3 = X2 ),
% 3.16/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_29,negated_conjecture,
% 3.16/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.16/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_360,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.99      | X3 = X0
% 3.16/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.16/0.99      | k6_partfun1(sK0) != X3
% 3.16/0.99      | sK0 != X2
% 3.16/0.99      | sK0 != X1 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_361,plain,
% 3.16/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.16/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.16/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_360]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_21,plain,
% 3.16/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.16/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_369,plain,
% 3.16/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.16/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.16/0.99      inference(forward_subsumption_resolution,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_361,c_21]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1867,plain,
% 3.16/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.16/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_4850,plain,
% 3.16/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.16/0.99      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.16/0.99      inference(demodulation,[status(thm)],[c_4847,c_1867]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_37,plain,
% 3.16/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_39,plain,
% 3.16/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_42,plain,
% 3.16/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_19,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.16/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.16/0.99      | ~ v1_funct_1(X0)
% 3.16/0.99      | ~ v1_funct_1(X3) ),
% 3.16/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1877,plain,
% 3.16/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.16/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.16/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.16/0.99      | v1_funct_1(X0) != iProver_top
% 3.16/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_4852,plain,
% 3.16/0.99      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.16/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.16/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.16/0.99      | v1_funct_1(sK3) != iProver_top
% 3.16/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.16/0.99      inference(superposition,[status(thm)],[c_4847,c_1877]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_5054,plain,
% 3.16/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_4850,c_37,c_39,c_40,c_42,c_4852]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_9,plain,
% 3.16/0.99      ( ~ v1_funct_1(X0)
% 3.16/0.99      | ~ v1_funct_1(X1)
% 3.16/0.99      | ~ v2_funct_1(X1)
% 3.16/0.99      | ~ v1_relat_1(X1)
% 3.16/0.99      | ~ v1_relat_1(X0)
% 3.16/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.16/0.99      | k2_funct_1(X1) = X0
% 3.16/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.16/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_4,plain,
% 3.16/0.99      ( ~ v1_funct_1(X0)
% 3.16/0.99      | ~ v1_funct_1(X1)
% 3.16/0.99      | v2_funct_1(X1)
% 3.16/0.99      | ~ v1_relat_1(X1)
% 3.16/0.99      | ~ v1_relat_1(X0)
% 3.16/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1)) ),
% 3.16/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_200,plain,
% 3.16/0.99      ( ~ v1_funct_1(X1)
% 3.16/0.99      | ~ v1_funct_1(X0)
% 3.16/0.99      | ~ v1_relat_1(X1)
% 3.16/0.99      | ~ v1_relat_1(X0)
% 3.16/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.16/0.99      | k2_funct_1(X1) = X0
% 3.16/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.16/0.99      inference(global_propositional_subsumption,[status(thm)],[c_9,c_4]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_201,plain,
% 3.16/0.99      ( ~ v1_funct_1(X0)
% 3.16/0.99      | ~ v1_funct_1(X1)
% 3.16/0.99      | ~ v1_relat_1(X1)
% 3.16/0.99      | ~ v1_relat_1(X0)
% 3.16/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.16/0.99      | k2_funct_1(X1) = X0
% 3.16/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.16/0.99      inference(renaming,[status(thm)],[c_200]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1868,plain,
% 3.16/0.99      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 3.16/0.99      | k2_funct_1(X0) = X1
% 3.16/0.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.16/0.99      | v1_funct_1(X1) != iProver_top
% 3.16/0.99      | v1_funct_1(X0) != iProver_top
% 3.16/0.99      | v1_relat_1(X0) != iProver_top
% 3.16/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_5277,plain,
% 3.16/0.99      ( k2_funct_1(sK2) = sK3
% 3.16/0.99      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 3.16/0.99      | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
% 3.16/0.99      | v1_funct_1(sK3) != iProver_top
% 3.16/0.99      | v1_funct_1(sK2) != iProver_top
% 3.16/0.99      | v1_relat_1(sK3) != iProver_top
% 3.16/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.16/0.99      inference(superposition,[status(thm)],[c_5054,c_1868]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_10,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.16/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1878,plain,
% 3.16/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.16/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3065,plain,
% 3.16/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.16/0.99      inference(superposition,[status(thm)],[c_1870,c_1878]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_18,plain,
% 3.16/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.16/0.99      | k1_xboole_0 = X2 ),
% 3.16/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_35,negated_conjecture,
% 3.16/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.16/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_910,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.16/0.99      | sK0 != X1
% 3.16/0.99      | sK1 != X2
% 3.16/0.99      | sK2 != X0
% 3.16/0.99      | k1_xboole_0 = X2 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_911,plain,
% 3.16/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.16/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.16/0.99      | k1_xboole_0 = sK1 ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_910]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_26,negated_conjecture,
% 3.16/0.99      ( k1_xboole_0 != sK1 ),
% 3.16/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_913,plain,
% 3.16/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_911,c_34,c_26]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3067,plain,
% 3.16/0.99      ( k1_relat_1(sK2) = sK0 ),
% 3.16/0.99      inference(light_normalisation,[status(thm)],[c_3065,c_913]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3064,plain,
% 3.16/0.99      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 3.16/0.99      inference(superposition,[status(thm)],[c_1872,c_1878]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_32,negated_conjecture,
% 3.16/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.16/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_886,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.16/0.99      | sK0 != X2
% 3.16/0.99      | sK1 != X1
% 3.16/0.99      | sK3 != X0
% 3.16/0.99      | k1_xboole_0 = X2 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_32]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_887,plain,
% 3.16/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.16/0.99      | k1_relset_1(sK1,sK0,sK3) = sK1
% 3.16/0.99      | k1_xboole_0 = sK0 ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_886]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_27,negated_conjecture,
% 3.16/0.99      ( k1_xboole_0 != sK0 ),
% 3.16/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_889,plain,
% 3.16/0.99      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_887,c_31,c_27]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3070,plain,
% 3.16/0.99      ( k1_relat_1(sK3) = sK1 ),
% 3.16/0.99      inference(light_normalisation,[status(thm)],[c_3064,c_889]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1869,plain,
% 3.16/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_8,plain,
% 3.16/0.99      ( ~ v1_funct_1(X0)
% 3.16/0.99      | ~ v2_funct_1(X0)
% 3.16/0.99      | ~ v1_relat_1(X0)
% 3.16/0.99      | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 3.16/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1879,plain,
% 3.16/0.99      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
% 3.16/0.99      | v1_funct_1(X0) != iProver_top
% 3.16/0.99      | v2_funct_1(X0) != iProver_top
% 3.16/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3555,plain,
% 3.16/0.99      ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
% 3.16/0.99      | v2_funct_1(sK2) != iProver_top
% 3.16/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.16/0.99      inference(superposition,[status(thm)],[c_1869,c_1879]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_23,plain,
% 3.16/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.99      | ~ v1_funct_1(X0)
% 3.16/0.99      | ~ v2_funct_1(X0)
% 3.16/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.16/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 3.16/0.99      | k1_xboole_0 = X2 ),
% 3.16/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_902,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.99      | ~ v1_funct_1(X0)
% 3.16/0.99      | ~ v2_funct_1(X0)
% 3.16/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.16/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 3.16/0.99      | sK0 != X1
% 3.16/0.99      | sK1 != X2
% 3.16/0.99      | sK2 != X0
% 3.16/0.99      | k1_xboole_0 = X2 ),
% 3.16/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_35]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_903,plain,
% 3.16/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.16/0.99      | ~ v1_funct_1(sK2)
% 3.16/0.99      | ~ v2_funct_1(sK2)
% 3.16/0.99      | k2_relset_1(sK0,sK1,sK2) != sK1
% 3.16/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.16/0.99      | k1_xboole_0 = sK1 ),
% 3.16/0.99      inference(unflattening,[status(thm)],[c_902]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_30,negated_conjecture,
% 3.16/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.16/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_28,negated_conjecture,
% 3.16/0.99      ( v2_funct_1(sK2) ),
% 3.16/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_905,plain,
% 3.16/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_903,c_36,c_34,c_30,c_28,c_26]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3559,plain,
% 3.16/0.99      ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
% 3.16/0.99      | v2_funct_1(sK2) != iProver_top
% 3.16/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.16/0.99      inference(light_normalisation,[status(thm)],[c_3555,c_905]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3,plain,
% 3.16/0.99      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.16/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3560,plain,
% 3.16/0.99      ( k2_relat_1(sK2) = sK1
% 3.16/0.99      | v2_funct_1(sK2) != iProver_top
% 3.16/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.16/0.99      inference(demodulation,[status(thm)],[c_3559,c_3]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_44,plain,
% 3.16/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_0,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.16/0.99      | ~ v1_relat_1(X1)
% 3.16/0.99      | v1_relat_1(X0) ),
% 3.16/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2148,plain,
% 3.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/0.99      | v1_relat_1(X0)
% 3.16/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2464,plain,
% 3.16/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.16/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.16/0.99      | v1_relat_1(sK2) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_2148]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2465,plain,
% 3.16/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.16/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.16/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_2464]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1,plain,
% 3.16/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.16/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3076,plain,
% 3.16/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3077,plain,
% 3.16/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_3076]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3631,plain,
% 3.16/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.16/0.99      inference(global_propositional_subsumption,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_3560,c_39,c_44,c_2465,c_3077]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_5285,plain,
% 3.16/0.99      ( k2_funct_1(sK2) = sK3
% 3.16/0.99      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 3.16/0.99      | sK1 != sK1
% 3.16/0.99      | v1_funct_1(sK3) != iProver_top
% 3.16/0.99      | v1_funct_1(sK2) != iProver_top
% 3.16/0.99      | v1_relat_1(sK3) != iProver_top
% 3.16/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.16/0.99      inference(light_normalisation,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_5277,c_3067,c_3070,c_3631]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_5286,plain,
% 3.16/0.99      ( k2_funct_1(sK2) = sK3
% 3.16/0.99      | v1_funct_1(sK3) != iProver_top
% 3.16/0.99      | v1_funct_1(sK2) != iProver_top
% 3.16/0.99      | v1_relat_1(sK3) != iProver_top
% 3.16/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.16/0.99      inference(equality_resolution_simp,[status(thm)],[c_5285]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3049,plain,
% 3.16/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3050,plain,
% 3.16/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_3049]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2461,plain,
% 3.16/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.16/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 3.16/0.99      | v1_relat_1(sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_2148]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2462,plain,
% 3.16/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.16/0.99      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.16/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_2461]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_25,negated_conjecture,
% 3.16/0.99      ( k2_funct_1(sK2) != sK3 ),
% 3.16/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(contradiction,plain,
% 3.16/0.99      ( $false ),
% 3.16/0.99      inference(minisat,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_5286,c_3077,c_3050,c_2465,c_2462,c_25,c_42,c_40,c_39,
% 3.16/0.99                 c_37]) ).
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  ------                               Statistics
% 3.16/0.99  
% 3.16/0.99  ------ General
% 3.16/0.99  
% 3.16/0.99  abstr_ref_over_cycles:                  0
% 3.16/0.99  abstr_ref_under_cycles:                 0
% 3.16/0.99  gc_basic_clause_elim:                   0
% 3.16/0.99  forced_gc_time:                         0
% 3.16/0.99  parsing_time:                           0.009
% 3.16/0.99  unif_index_cands_time:                  0.
% 3.16/0.99  unif_index_add_time:                    0.
% 3.16/0.99  orderings_time:                         0.
% 3.16/0.99  out_proof_time:                         0.01
% 3.16/0.99  total_time:                             0.186
% 3.16/0.99  num_of_symbols:                         52
% 3.16/0.99  num_of_terms:                           5282
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing
% 3.16/0.99  
% 3.16/0.99  num_of_splits:                          0
% 3.16/0.99  num_of_split_atoms:                     0
% 3.16/0.99  num_of_reused_defs:                     0
% 3.16/0.99  num_eq_ax_congr_red:                    2
% 3.16/0.99  num_of_sem_filtered_clauses:            1
% 3.16/0.99  num_of_subtypes:                        0
% 3.16/0.99  monotx_restored_types:                  0
% 3.16/0.99  sat_num_of_epr_types:                   0
% 3.16/0.99  sat_num_of_non_cyclic_types:            0
% 3.16/0.99  sat_guarded_non_collapsed_types:        0
% 3.16/0.99  num_pure_diseq_elim:                    0
% 3.16/0.99  simp_replaced_by:                       0
% 3.16/0.99  res_preprocessed:                       144
% 3.16/0.99  prep_upred:                             0
% 3.16/0.99  prep_unflattend:                        92
% 3.16/0.99  smt_new_axioms:                         0
% 3.16/0.99  pred_elim_cands:                        6
% 3.16/0.99  pred_elim:                              2
% 3.16/0.99  pred_elim_cl:                           0
% 3.16/0.99  pred_elim_cycles:                       4
% 3.16/0.99  merged_defs:                            0
% 3.16/0.99  merged_defs_ncl:                        0
% 3.16/0.99  bin_hyper_res:                          0
% 3.16/0.99  prep_cycles:                            3
% 3.16/0.99  pred_elim_time:                         0.021
% 3.16/0.99  splitting_time:                         0.
% 3.16/0.99  sem_filter_time:                        0.
% 3.16/0.99  monotx_time:                            0.002
% 3.16/0.99  subtype_inf_time:                       0.
% 3.16/0.99  
% 3.16/0.99  ------ Problem properties
% 3.16/0.99  
% 3.16/0.99  clauses:                                37
% 3.16/0.99  conjectures:                            9
% 3.16/0.99  epr:                                    5
% 3.16/0.99  horn:                                   35
% 3.16/0.99  ground:                                 20
% 3.16/0.99  unary:                                  17
% 3.16/0.99  binary:                                 2
% 3.16/0.99  lits:                                   100
% 3.16/0.99  lits_eq:                                41
% 3.16/0.99  fd_pure:                                0
% 3.16/0.99  fd_pseudo:                              0
% 3.16/0.99  fd_cond:                                2
% 3.16/0.99  fd_pseudo_cond:                         1
% 3.16/0.99  ac_symbols:                             0
% 3.16/0.99  
% 3.16/0.99  ------ Propositional Solver
% 3.16/0.99  
% 3.16/0.99  prop_solver_calls:                      22
% 3.16/0.99  prop_fast_solver_calls:                 1301
% 3.16/0.99  smt_solver_calls:                       0
% 3.16/0.99  smt_fast_solver_calls:                  0
% 3.16/0.99  prop_num_of_clauses:                    1923
% 3.16/0.99  prop_preprocess_simplified:             6127
% 3.16/0.99  prop_fo_subsumed:                       66
% 3.16/0.99  prop_solver_time:                       0.
% 3.16/0.99  smt_solver_time:                        0.
% 3.16/0.99  smt_fast_solver_time:                   0.
% 3.16/0.99  prop_fast_solver_time:                  0.
% 3.16/0.99  prop_unsat_core_time:                   0.
% 3.16/0.99  
% 3.16/0.99  ------ QBF
% 3.16/0.99  
% 3.16/0.99  qbf_q_res:                              0
% 3.16/0.99  qbf_num_tautologies:                    0
% 3.16/0.99  qbf_prep_cycles:                        0
% 3.16/0.99  
% 3.16/0.99  ------ BMC1
% 3.16/0.99  
% 3.16/0.99  bmc1_current_bound:                     -1
% 3.16/0.99  bmc1_last_solved_bound:                 -1
% 3.16/0.99  bmc1_unsat_core_size:                   -1
% 3.16/0.99  bmc1_unsat_core_parents_size:           -1
% 3.16/0.99  bmc1_merge_next_fun:                    0
% 3.16/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.16/0.99  
% 3.16/0.99  ------ Instantiation
% 3.16/0.99  
% 3.16/0.99  inst_num_of_clauses:                    517
% 3.16/0.99  inst_num_in_passive:                    160
% 3.16/0.99  inst_num_in_active:                     289
% 3.16/0.99  inst_num_in_unprocessed:                68
% 3.16/0.99  inst_num_of_loops:                      300
% 3.16/0.99  inst_num_of_learning_restarts:          0
% 3.16/0.99  inst_num_moves_active_passive:          10
% 3.16/0.99  inst_lit_activity:                      0
% 3.16/0.99  inst_lit_activity_moves:                0
% 3.16/0.99  inst_num_tautologies:                   0
% 3.16/0.99  inst_num_prop_implied:                  0
% 3.16/0.99  inst_num_existing_simplified:           0
% 3.16/0.99  inst_num_eq_res_simplified:             0
% 3.16/0.99  inst_num_child_elim:                    0
% 3.16/0.99  inst_num_of_dismatching_blockings:      8
% 3.16/0.99  inst_num_of_non_proper_insts:           311
% 3.16/0.99  inst_num_of_duplicates:                 0
% 3.16/0.99  inst_inst_num_from_inst_to_res:         0
% 3.16/0.99  inst_dismatching_checking_time:         0.
% 3.16/0.99  
% 3.16/0.99  ------ Resolution
% 3.16/0.99  
% 3.16/0.99  res_num_of_clauses:                     0
% 3.16/0.99  res_num_in_passive:                     0
% 3.16/0.99  res_num_in_active:                      0
% 3.16/0.99  res_num_of_loops:                       147
% 3.16/0.99  res_forward_subset_subsumed:            26
% 3.16/0.99  res_backward_subset_subsumed:           0
% 3.16/0.99  res_forward_subsumed:                   2
% 3.16/0.99  res_backward_subsumed:                  0
% 3.16/0.99  res_forward_subsumption_resolution:     1
% 3.16/0.99  res_backward_subsumption_resolution:    0
% 3.16/0.99  res_clause_to_clause_subsumption:       194
% 3.16/0.99  res_orphan_elimination:                 0
% 3.16/0.99  res_tautology_del:                      23
% 3.16/0.99  res_num_eq_res_simplified:              0
% 3.16/0.99  res_num_sel_changes:                    0
% 3.16/0.99  res_moves_from_active_to_pass:          0
% 3.16/0.99  
% 3.16/0.99  ------ Superposition
% 3.16/0.99  
% 3.16/0.99  sup_time_total:                         0.
% 3.16/0.99  sup_time_generating:                    0.
% 3.16/0.99  sup_time_sim_full:                      0.
% 3.16/0.99  sup_time_sim_immed:                     0.
% 3.16/0.99  
% 3.16/0.99  sup_num_of_clauses:                     83
% 3.16/0.99  sup_num_in_active:                      57
% 3.16/0.99  sup_num_in_passive:                     26
% 3.16/0.99  sup_num_of_loops:                       58
% 3.16/0.99  sup_fw_superposition:                   31
% 3.16/0.99  sup_bw_superposition:                   28
% 3.16/0.99  sup_immediate_simplified:               16
% 3.16/0.99  sup_given_eliminated:                   0
% 3.16/0.99  comparisons_done:                       0
% 3.16/0.99  comparisons_avoided:                    0
% 3.16/0.99  
% 3.16/0.99  ------ Simplifications
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  sim_fw_subset_subsumed:                 4
% 3.16/0.99  sim_bw_subset_subsumed:                 1
% 3.16/0.99  sim_fw_subsumed:                        1
% 3.16/0.99  sim_bw_subsumed:                        0
% 3.16/0.99  sim_fw_subsumption_res:                 1
% 3.16/0.99  sim_bw_subsumption_res:                 0
% 3.16/0.99  sim_tautology_del:                      0
% 3.16/0.99  sim_eq_tautology_del:                   4
% 3.16/0.99  sim_eq_res_simp:                        1
% 3.16/0.99  sim_fw_demodulated:                     4
% 3.16/0.99  sim_bw_demodulated:                     2
% 3.16/0.99  sim_light_normalised:                   11
% 3.16/0.99  sim_joinable_taut:                      0
% 3.16/0.99  sim_joinable_simp:                      0
% 3.16/0.99  sim_ac_normalised:                      0
% 3.16/0.99  sim_smt_subsumption:                    0
% 3.16/0.99  
%------------------------------------------------------------------------------
