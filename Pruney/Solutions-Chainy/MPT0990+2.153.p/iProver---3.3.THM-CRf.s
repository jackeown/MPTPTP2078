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
% DateTime   : Thu Dec  3 12:03:29 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  174 (1423 expanded)
%              Number of clauses        :  103 ( 397 expanded)
%              Number of leaves         :   20 ( 375 expanded)
%              Depth                    :   21
%              Number of atoms          :  709 (12870 expanded)
%              Number of equality atoms :  338 (4632 expanded)
%              Maximal formula depth    :   16 (   5 average)
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

fof(f38,plain,(
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
    inference(flattening,[],[f38])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f43,f42])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f64])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f44])).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f82,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1204,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1207,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1213,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4457,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_1213])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4850,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4457,c_39])).

cnf(c_4851,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4850])).

cnf(c_4862,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_4851])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1722,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2070,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1722])).

cnf(c_2339,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2070])).

cnf(c_2453,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2339])).

cnf(c_4950,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4862,c_35,c_33,c_32,c_30,c_2453])).

cnf(c_8,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_28,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_28])).

cnf(c_391,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_399,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_391,c_17])).

cnf(c_1200,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_4953,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4950,c_1200])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1216,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4979,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4950,c_1216])).

cnf(c_5166,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4953,c_36,c_38,c_39,c_41,c_4979])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k2_funct_1(X1) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1226,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k2_funct_1(X1) = X0
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5170,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5166,c_1226])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1223,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2140,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1204,c_1223])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2142,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2140,c_29])).

cnf(c_2139,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1207,c_1223])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_403,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_404,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_489,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_404])).

cnf(c_1199,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_1831,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1199])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_37,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_40,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2040,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1831,c_36,c_37,c_38,c_39,c_40,c_41])).

cnf(c_2145,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2139,c_2040])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1217,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3011,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_1217])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1224,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2291,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1207,c_1224])).

cnf(c_3023,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3011,c_2291])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_666,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_693,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_667,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1601,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_1602,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1601])).

cnf(c_3401,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3023,c_40,c_26,c_693,c_1602])).

cnf(c_5171,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5170,c_2142,c_2145,c_3401])).

cnf(c_5172,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5171])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1565,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2048,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1565])).

cnf(c_2049,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2048])).

cnf(c_2051,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1565])).

cnf(c_2052,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2051])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2255,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2256,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2255])).

cnf(c_2268,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2269,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2268])).

cnf(c_5169,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_5166,c_4950])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k2_relset_1(X1,X2,X0) != X2
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1211,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5255,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_1211])).

cnf(c_5318,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5255,c_36,c_37,c_38])).

cnf(c_5319,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5318])).

cnf(c_5328,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5169,c_5319])).

cnf(c_5645,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5328,c_39,c_40,c_41,c_26,c_693,c_1602])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1227,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5651,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5645,c_1227])).

cnf(c_7700,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5172,c_36,c_38,c_39,c_41,c_2049,c_2052,c_2256,c_2269,c_5651])).

cnf(c_1205,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1225,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2383,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1225])).

cnf(c_2585,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2383,c_41,c_2049,c_2256])).

cnf(c_2586,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2585])).

cnf(c_5653,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_5651,c_2586])).

cnf(c_7703,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_7700,c_5653])).

cnf(c_24,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f81])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7703,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:46:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.28/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/0.98  
% 3.28/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.28/0.98  
% 3.28/0.98  ------  iProver source info
% 3.28/0.98  
% 3.28/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.28/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.28/0.98  git: non_committed_changes: false
% 3.28/0.98  git: last_make_outside_of_git: false
% 3.28/0.98  
% 3.28/0.98  ------ 
% 3.28/0.98  
% 3.28/0.98  ------ Input Options
% 3.28/0.98  
% 3.28/0.98  --out_options                           all
% 3.28/0.98  --tptp_safe_out                         true
% 3.28/0.98  --problem_path                          ""
% 3.28/0.98  --include_path                          ""
% 3.28/0.98  --clausifier                            res/vclausify_rel
% 3.28/0.98  --clausifier_options                    --mode clausify
% 3.28/0.98  --stdin                                 false
% 3.28/0.98  --stats_out                             all
% 3.28/0.98  
% 3.28/0.98  ------ General Options
% 3.28/0.98  
% 3.28/0.98  --fof                                   false
% 3.28/0.98  --time_out_real                         305.
% 3.28/0.98  --time_out_virtual                      -1.
% 3.28/0.98  --symbol_type_check                     false
% 3.28/0.98  --clausify_out                          false
% 3.28/0.98  --sig_cnt_out                           false
% 3.28/0.98  --trig_cnt_out                          false
% 3.28/0.98  --trig_cnt_out_tolerance                1.
% 3.28/0.98  --trig_cnt_out_sk_spl                   false
% 3.28/0.98  --abstr_cl_out                          false
% 3.28/0.98  
% 3.28/0.98  ------ Global Options
% 3.28/0.98  
% 3.28/0.98  --schedule                              default
% 3.28/0.98  --add_important_lit                     false
% 3.28/0.98  --prop_solver_per_cl                    1000
% 3.28/0.98  --min_unsat_core                        false
% 3.28/0.98  --soft_assumptions                      false
% 3.28/0.98  --soft_lemma_size                       3
% 3.28/0.98  --prop_impl_unit_size                   0
% 3.28/0.98  --prop_impl_unit                        []
% 3.28/0.98  --share_sel_clauses                     true
% 3.28/0.98  --reset_solvers                         false
% 3.28/0.98  --bc_imp_inh                            [conj_cone]
% 3.28/0.98  --conj_cone_tolerance                   3.
% 3.28/0.98  --extra_neg_conj                        none
% 3.28/0.98  --large_theory_mode                     true
% 3.28/0.98  --prolific_symb_bound                   200
% 3.28/0.98  --lt_threshold                          2000
% 3.28/0.98  --clause_weak_htbl                      true
% 3.28/0.98  --gc_record_bc_elim                     false
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing Options
% 3.28/0.98  
% 3.28/0.98  --preprocessing_flag                    true
% 3.28/0.98  --time_out_prep_mult                    0.1
% 3.28/0.98  --splitting_mode                        input
% 3.28/0.98  --splitting_grd                         true
% 3.28/0.98  --splitting_cvd                         false
% 3.28/0.98  --splitting_cvd_svl                     false
% 3.28/0.98  --splitting_nvd                         32
% 3.28/0.98  --sub_typing                            true
% 3.28/0.98  --prep_gs_sim                           true
% 3.28/0.98  --prep_unflatten                        true
% 3.28/0.98  --prep_res_sim                          true
% 3.28/0.98  --prep_upred                            true
% 3.28/0.98  --prep_sem_filter                       exhaustive
% 3.28/0.98  --prep_sem_filter_out                   false
% 3.28/0.98  --pred_elim                             true
% 3.28/0.98  --res_sim_input                         true
% 3.28/0.98  --eq_ax_congr_red                       true
% 3.28/0.98  --pure_diseq_elim                       true
% 3.28/0.98  --brand_transform                       false
% 3.28/0.98  --non_eq_to_eq                          false
% 3.28/0.98  --prep_def_merge                        true
% 3.28/0.98  --prep_def_merge_prop_impl              false
% 3.28/0.98  --prep_def_merge_mbd                    true
% 3.28/0.98  --prep_def_merge_tr_red                 false
% 3.28/0.98  --prep_def_merge_tr_cl                  false
% 3.28/0.98  --smt_preprocessing                     true
% 3.28/0.98  --smt_ac_axioms                         fast
% 3.28/0.98  --preprocessed_out                      false
% 3.28/0.98  --preprocessed_stats                    false
% 3.28/0.98  
% 3.28/0.98  ------ Abstraction refinement Options
% 3.28/0.98  
% 3.28/0.98  --abstr_ref                             []
% 3.28/0.98  --abstr_ref_prep                        false
% 3.28/0.98  --abstr_ref_until_sat                   false
% 3.28/0.98  --abstr_ref_sig_restrict                funpre
% 3.28/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.28/0.98  --abstr_ref_under                       []
% 3.28/0.98  
% 3.28/0.98  ------ SAT Options
% 3.28/0.98  
% 3.28/0.98  --sat_mode                              false
% 3.28/0.98  --sat_fm_restart_options                ""
% 3.28/0.98  --sat_gr_def                            false
% 3.28/0.98  --sat_epr_types                         true
% 3.28/0.98  --sat_non_cyclic_types                  false
% 3.28/0.98  --sat_finite_models                     false
% 3.28/0.98  --sat_fm_lemmas                         false
% 3.28/0.98  --sat_fm_prep                           false
% 3.28/0.98  --sat_fm_uc_incr                        true
% 3.28/0.98  --sat_out_model                         small
% 3.28/0.98  --sat_out_clauses                       false
% 3.28/0.98  
% 3.28/0.98  ------ QBF Options
% 3.28/0.98  
% 3.28/0.98  --qbf_mode                              false
% 3.28/0.98  --qbf_elim_univ                         false
% 3.28/0.98  --qbf_dom_inst                          none
% 3.28/0.98  --qbf_dom_pre_inst                      false
% 3.28/0.98  --qbf_sk_in                             false
% 3.28/0.98  --qbf_pred_elim                         true
% 3.28/0.98  --qbf_split                             512
% 3.28/0.98  
% 3.28/0.98  ------ BMC1 Options
% 3.28/0.98  
% 3.28/0.98  --bmc1_incremental                      false
% 3.28/0.98  --bmc1_axioms                           reachable_all
% 3.28/0.98  --bmc1_min_bound                        0
% 3.28/0.98  --bmc1_max_bound                        -1
% 3.28/0.98  --bmc1_max_bound_default                -1
% 3.28/0.98  --bmc1_symbol_reachability              true
% 3.28/0.98  --bmc1_property_lemmas                  false
% 3.28/0.98  --bmc1_k_induction                      false
% 3.28/0.98  --bmc1_non_equiv_states                 false
% 3.28/0.98  --bmc1_deadlock                         false
% 3.28/0.98  --bmc1_ucm                              false
% 3.28/0.98  --bmc1_add_unsat_core                   none
% 3.28/0.98  --bmc1_unsat_core_children              false
% 3.28/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.28/0.98  --bmc1_out_stat                         full
% 3.28/0.98  --bmc1_ground_init                      false
% 3.28/0.98  --bmc1_pre_inst_next_state              false
% 3.28/0.98  --bmc1_pre_inst_state                   false
% 3.28/0.98  --bmc1_pre_inst_reach_state             false
% 3.28/0.98  --bmc1_out_unsat_core                   false
% 3.28/0.98  --bmc1_aig_witness_out                  false
% 3.28/0.98  --bmc1_verbose                          false
% 3.28/0.98  --bmc1_dump_clauses_tptp                false
% 3.28/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.28/0.98  --bmc1_dump_file                        -
% 3.28/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.28/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.28/0.98  --bmc1_ucm_extend_mode                  1
% 3.28/0.98  --bmc1_ucm_init_mode                    2
% 3.28/0.98  --bmc1_ucm_cone_mode                    none
% 3.28/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.28/0.98  --bmc1_ucm_relax_model                  4
% 3.28/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.28/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.28/0.98  --bmc1_ucm_layered_model                none
% 3.28/0.98  --bmc1_ucm_max_lemma_size               10
% 3.28/0.98  
% 3.28/0.98  ------ AIG Options
% 3.28/0.98  
% 3.28/0.98  --aig_mode                              false
% 3.28/0.98  
% 3.28/0.98  ------ Instantiation Options
% 3.28/0.98  
% 3.28/0.98  --instantiation_flag                    true
% 3.28/0.98  --inst_sos_flag                         false
% 3.28/0.98  --inst_sos_phase                        true
% 3.28/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.28/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.28/0.98  --inst_lit_sel_side                     num_symb
% 3.28/0.98  --inst_solver_per_active                1400
% 3.28/0.98  --inst_solver_calls_frac                1.
% 3.28/0.98  --inst_passive_queue_type               priority_queues
% 3.28/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.28/0.98  --inst_passive_queues_freq              [25;2]
% 3.28/0.98  --inst_dismatching                      true
% 3.28/0.98  --inst_eager_unprocessed_to_passive     true
% 3.28/0.98  --inst_prop_sim_given                   true
% 3.28/0.98  --inst_prop_sim_new                     false
% 3.28/0.98  --inst_subs_new                         false
% 3.28/0.98  --inst_eq_res_simp                      false
% 3.28/0.98  --inst_subs_given                       false
% 3.28/0.98  --inst_orphan_elimination               true
% 3.28/0.98  --inst_learning_loop_flag               true
% 3.28/0.98  --inst_learning_start                   3000
% 3.28/0.98  --inst_learning_factor                  2
% 3.28/0.98  --inst_start_prop_sim_after_learn       3
% 3.28/0.98  --inst_sel_renew                        solver
% 3.28/0.98  --inst_lit_activity_flag                true
% 3.28/0.98  --inst_restr_to_given                   false
% 3.28/0.98  --inst_activity_threshold               500
% 3.28/0.98  --inst_out_proof                        true
% 3.28/0.98  
% 3.28/0.98  ------ Resolution Options
% 3.28/0.98  
% 3.28/0.98  --resolution_flag                       true
% 3.28/0.98  --res_lit_sel                           adaptive
% 3.28/0.98  --res_lit_sel_side                      none
% 3.28/0.98  --res_ordering                          kbo
% 3.28/0.98  --res_to_prop_solver                    active
% 3.28/0.98  --res_prop_simpl_new                    false
% 3.28/0.98  --res_prop_simpl_given                  true
% 3.28/0.98  --res_passive_queue_type                priority_queues
% 3.28/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.28/0.98  --res_passive_queues_freq               [15;5]
% 3.28/0.98  --res_forward_subs                      full
% 3.28/0.98  --res_backward_subs                     full
% 3.28/0.98  --res_forward_subs_resolution           true
% 3.28/0.98  --res_backward_subs_resolution          true
% 3.28/0.98  --res_orphan_elimination                true
% 3.28/0.98  --res_time_limit                        2.
% 3.28/0.98  --res_out_proof                         true
% 3.28/0.98  
% 3.28/0.98  ------ Superposition Options
% 3.28/0.98  
% 3.28/0.98  --superposition_flag                    true
% 3.28/0.98  --sup_passive_queue_type                priority_queues
% 3.28/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.28/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.28/0.98  --demod_completeness_check              fast
% 3.28/0.98  --demod_use_ground                      true
% 3.28/0.98  --sup_to_prop_solver                    passive
% 3.28/0.98  --sup_prop_simpl_new                    true
% 3.28/0.98  --sup_prop_simpl_given                  true
% 3.28/0.98  --sup_fun_splitting                     false
% 3.28/0.98  --sup_smt_interval                      50000
% 3.28/0.98  
% 3.28/0.98  ------ Superposition Simplification Setup
% 3.28/0.98  
% 3.28/0.98  --sup_indices_passive                   []
% 3.28/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.28/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/0.98  --sup_full_bw                           [BwDemod]
% 3.28/0.98  --sup_immed_triv                        [TrivRules]
% 3.28/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.28/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/0.98  --sup_immed_bw_main                     []
% 3.28/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.28/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/0.98  
% 3.28/0.98  ------ Combination Options
% 3.28/0.98  
% 3.28/0.98  --comb_res_mult                         3
% 3.28/0.98  --comb_sup_mult                         2
% 3.28/0.98  --comb_inst_mult                        10
% 3.28/0.98  
% 3.28/0.98  ------ Debug Options
% 3.28/0.98  
% 3.28/0.98  --dbg_backtrace                         false
% 3.28/0.98  --dbg_dump_prop_clauses                 false
% 3.28/0.98  --dbg_dump_prop_clauses_file            -
% 3.28/0.98  --dbg_out_stat                          false
% 3.28/0.98  ------ Parsing...
% 3.28/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.28/0.98  ------ Proving...
% 3.28/0.98  ------ Problem Properties 
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  clauses                                 35
% 3.28/0.98  conjectures                             11
% 3.28/0.98  EPR                                     7
% 3.28/0.98  Horn                                    29
% 3.28/0.98  unary                                   14
% 3.28/0.98  binary                                  3
% 3.28/0.98  lits                                    125
% 3.28/0.98  lits eq                                 31
% 3.28/0.98  fd_pure                                 0
% 3.28/0.98  fd_pseudo                               0
% 3.28/0.98  fd_cond                                 5
% 3.28/0.98  fd_pseudo_cond                          1
% 3.28/0.98  AC symbols                              0
% 3.28/0.98  
% 3.28/0.98  ------ Schedule dynamic 5 is on 
% 3.28/0.98  
% 3.28/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  ------ 
% 3.28/0.98  Current options:
% 3.28/0.98  ------ 
% 3.28/0.98  
% 3.28/0.98  ------ Input Options
% 3.28/0.98  
% 3.28/0.98  --out_options                           all
% 3.28/0.98  --tptp_safe_out                         true
% 3.28/0.98  --problem_path                          ""
% 3.28/0.98  --include_path                          ""
% 3.28/0.98  --clausifier                            res/vclausify_rel
% 3.28/0.98  --clausifier_options                    --mode clausify
% 3.28/0.98  --stdin                                 false
% 3.28/0.98  --stats_out                             all
% 3.28/0.98  
% 3.28/0.98  ------ General Options
% 3.28/0.98  
% 3.28/0.98  --fof                                   false
% 3.28/0.98  --time_out_real                         305.
% 3.28/0.98  --time_out_virtual                      -1.
% 3.28/0.98  --symbol_type_check                     false
% 3.28/0.98  --clausify_out                          false
% 3.28/0.98  --sig_cnt_out                           false
% 3.28/0.98  --trig_cnt_out                          false
% 3.28/0.98  --trig_cnt_out_tolerance                1.
% 3.28/0.98  --trig_cnt_out_sk_spl                   false
% 3.28/0.98  --abstr_cl_out                          false
% 3.28/0.98  
% 3.28/0.98  ------ Global Options
% 3.28/0.98  
% 3.28/0.98  --schedule                              default
% 3.28/0.98  --add_important_lit                     false
% 3.28/0.98  --prop_solver_per_cl                    1000
% 3.28/0.98  --min_unsat_core                        false
% 3.28/0.98  --soft_assumptions                      false
% 3.28/0.98  --soft_lemma_size                       3
% 3.28/0.98  --prop_impl_unit_size                   0
% 3.28/0.98  --prop_impl_unit                        []
% 3.28/0.98  --share_sel_clauses                     true
% 3.28/0.98  --reset_solvers                         false
% 3.28/0.98  --bc_imp_inh                            [conj_cone]
% 3.28/0.98  --conj_cone_tolerance                   3.
% 3.28/0.98  --extra_neg_conj                        none
% 3.28/0.98  --large_theory_mode                     true
% 3.28/0.98  --prolific_symb_bound                   200
% 3.28/0.98  --lt_threshold                          2000
% 3.28/0.98  --clause_weak_htbl                      true
% 3.28/0.98  --gc_record_bc_elim                     false
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing Options
% 3.28/0.98  
% 3.28/0.98  --preprocessing_flag                    true
% 3.28/0.98  --time_out_prep_mult                    0.1
% 3.28/0.98  --splitting_mode                        input
% 3.28/0.98  --splitting_grd                         true
% 3.28/0.98  --splitting_cvd                         false
% 3.28/0.98  --splitting_cvd_svl                     false
% 3.28/0.98  --splitting_nvd                         32
% 3.28/0.98  --sub_typing                            true
% 3.28/0.98  --prep_gs_sim                           true
% 3.28/0.98  --prep_unflatten                        true
% 3.28/0.98  --prep_res_sim                          true
% 3.28/0.98  --prep_upred                            true
% 3.28/0.98  --prep_sem_filter                       exhaustive
% 3.28/0.98  --prep_sem_filter_out                   false
% 3.28/0.98  --pred_elim                             true
% 3.28/0.98  --res_sim_input                         true
% 3.28/0.98  --eq_ax_congr_red                       true
% 3.28/0.98  --pure_diseq_elim                       true
% 3.28/0.98  --brand_transform                       false
% 3.28/0.98  --non_eq_to_eq                          false
% 3.28/0.98  --prep_def_merge                        true
% 3.28/0.98  --prep_def_merge_prop_impl              false
% 3.28/0.98  --prep_def_merge_mbd                    true
% 3.28/0.98  --prep_def_merge_tr_red                 false
% 3.28/0.98  --prep_def_merge_tr_cl                  false
% 3.28/0.98  --smt_preprocessing                     true
% 3.28/0.98  --smt_ac_axioms                         fast
% 3.28/0.98  --preprocessed_out                      false
% 3.28/0.98  --preprocessed_stats                    false
% 3.28/0.98  
% 3.28/0.98  ------ Abstraction refinement Options
% 3.28/0.98  
% 3.28/0.98  --abstr_ref                             []
% 3.28/0.98  --abstr_ref_prep                        false
% 3.28/0.98  --abstr_ref_until_sat                   false
% 3.28/0.98  --abstr_ref_sig_restrict                funpre
% 3.28/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.28/0.98  --abstr_ref_under                       []
% 3.28/0.98  
% 3.28/0.98  ------ SAT Options
% 3.28/0.98  
% 3.28/0.98  --sat_mode                              false
% 3.28/0.98  --sat_fm_restart_options                ""
% 3.28/0.98  --sat_gr_def                            false
% 3.28/0.98  --sat_epr_types                         true
% 3.28/0.98  --sat_non_cyclic_types                  false
% 3.28/0.98  --sat_finite_models                     false
% 3.28/0.98  --sat_fm_lemmas                         false
% 3.28/0.98  --sat_fm_prep                           false
% 3.28/0.98  --sat_fm_uc_incr                        true
% 3.28/0.98  --sat_out_model                         small
% 3.28/0.98  --sat_out_clauses                       false
% 3.28/0.98  
% 3.28/0.98  ------ QBF Options
% 3.28/0.98  
% 3.28/0.98  --qbf_mode                              false
% 3.28/0.98  --qbf_elim_univ                         false
% 3.28/0.98  --qbf_dom_inst                          none
% 3.28/0.98  --qbf_dom_pre_inst                      false
% 3.28/0.98  --qbf_sk_in                             false
% 3.28/0.98  --qbf_pred_elim                         true
% 3.28/0.98  --qbf_split                             512
% 3.28/0.98  
% 3.28/0.98  ------ BMC1 Options
% 3.28/0.98  
% 3.28/0.98  --bmc1_incremental                      false
% 3.28/0.98  --bmc1_axioms                           reachable_all
% 3.28/0.98  --bmc1_min_bound                        0
% 3.28/0.98  --bmc1_max_bound                        -1
% 3.28/0.98  --bmc1_max_bound_default                -1
% 3.28/0.98  --bmc1_symbol_reachability              true
% 3.28/0.98  --bmc1_property_lemmas                  false
% 3.28/0.98  --bmc1_k_induction                      false
% 3.28/0.98  --bmc1_non_equiv_states                 false
% 3.28/0.98  --bmc1_deadlock                         false
% 3.28/0.98  --bmc1_ucm                              false
% 3.28/0.98  --bmc1_add_unsat_core                   none
% 3.28/0.98  --bmc1_unsat_core_children              false
% 3.28/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.28/0.98  --bmc1_out_stat                         full
% 3.28/0.98  --bmc1_ground_init                      false
% 3.28/0.98  --bmc1_pre_inst_next_state              false
% 3.28/0.98  --bmc1_pre_inst_state                   false
% 3.28/0.98  --bmc1_pre_inst_reach_state             false
% 3.28/0.98  --bmc1_out_unsat_core                   false
% 3.28/0.98  --bmc1_aig_witness_out                  false
% 3.28/0.98  --bmc1_verbose                          false
% 3.28/0.98  --bmc1_dump_clauses_tptp                false
% 3.28/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.28/0.98  --bmc1_dump_file                        -
% 3.28/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.28/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.28/0.98  --bmc1_ucm_extend_mode                  1
% 3.28/0.98  --bmc1_ucm_init_mode                    2
% 3.28/0.98  --bmc1_ucm_cone_mode                    none
% 3.28/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.28/0.98  --bmc1_ucm_relax_model                  4
% 3.28/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.28/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.28/0.98  --bmc1_ucm_layered_model                none
% 3.28/0.98  --bmc1_ucm_max_lemma_size               10
% 3.28/0.98  
% 3.28/0.98  ------ AIG Options
% 3.28/0.98  
% 3.28/0.98  --aig_mode                              false
% 3.28/0.98  
% 3.28/0.98  ------ Instantiation Options
% 3.28/0.98  
% 3.28/0.98  --instantiation_flag                    true
% 3.28/0.98  --inst_sos_flag                         false
% 3.28/0.98  --inst_sos_phase                        true
% 3.28/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.28/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.28/0.98  --inst_lit_sel_side                     none
% 3.28/0.98  --inst_solver_per_active                1400
% 3.28/0.98  --inst_solver_calls_frac                1.
% 3.28/0.98  --inst_passive_queue_type               priority_queues
% 3.28/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.28/0.98  --inst_passive_queues_freq              [25;2]
% 3.28/0.98  --inst_dismatching                      true
% 3.28/0.98  --inst_eager_unprocessed_to_passive     true
% 3.28/0.98  --inst_prop_sim_given                   true
% 3.28/0.98  --inst_prop_sim_new                     false
% 3.28/0.98  --inst_subs_new                         false
% 3.28/0.98  --inst_eq_res_simp                      false
% 3.28/0.98  --inst_subs_given                       false
% 3.28/0.98  --inst_orphan_elimination               true
% 3.28/0.98  --inst_learning_loop_flag               true
% 3.28/0.98  --inst_learning_start                   3000
% 3.28/0.98  --inst_learning_factor                  2
% 3.28/0.98  --inst_start_prop_sim_after_learn       3
% 3.28/0.98  --inst_sel_renew                        solver
% 3.28/0.98  --inst_lit_activity_flag                true
% 3.28/0.98  --inst_restr_to_given                   false
% 3.28/0.98  --inst_activity_threshold               500
% 3.28/0.98  --inst_out_proof                        true
% 3.28/0.98  
% 3.28/0.98  ------ Resolution Options
% 3.28/0.98  
% 3.28/0.98  --resolution_flag                       false
% 3.28/0.98  --res_lit_sel                           adaptive
% 3.28/0.98  --res_lit_sel_side                      none
% 3.28/0.98  --res_ordering                          kbo
% 3.28/0.98  --res_to_prop_solver                    active
% 3.28/0.98  --res_prop_simpl_new                    false
% 3.28/0.98  --res_prop_simpl_given                  true
% 3.28/0.98  --res_passive_queue_type                priority_queues
% 3.28/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.28/0.98  --res_passive_queues_freq               [15;5]
% 3.28/0.98  --res_forward_subs                      full
% 3.28/0.98  --res_backward_subs                     full
% 3.28/0.98  --res_forward_subs_resolution           true
% 3.28/0.98  --res_backward_subs_resolution          true
% 3.28/0.98  --res_orphan_elimination                true
% 3.28/0.98  --res_time_limit                        2.
% 3.28/0.98  --res_out_proof                         true
% 3.28/0.98  
% 3.28/0.98  ------ Superposition Options
% 3.28/0.98  
% 3.28/0.98  --superposition_flag                    true
% 3.28/0.98  --sup_passive_queue_type                priority_queues
% 3.28/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.28/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.28/0.98  --demod_completeness_check              fast
% 3.28/0.98  --demod_use_ground                      true
% 3.28/0.98  --sup_to_prop_solver                    passive
% 3.28/0.98  --sup_prop_simpl_new                    true
% 3.28/0.98  --sup_prop_simpl_given                  true
% 3.28/0.98  --sup_fun_splitting                     false
% 3.28/0.98  --sup_smt_interval                      50000
% 3.28/0.98  
% 3.28/0.98  ------ Superposition Simplification Setup
% 3.28/0.98  
% 3.28/0.98  --sup_indices_passive                   []
% 3.28/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.28/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/0.98  --sup_full_bw                           [BwDemod]
% 3.28/0.98  --sup_immed_triv                        [TrivRules]
% 3.28/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.28/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/0.98  --sup_immed_bw_main                     []
% 3.28/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.28/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/0.98  
% 3.28/0.98  ------ Combination Options
% 3.28/0.98  
% 3.28/0.98  --comb_res_mult                         3
% 3.28/0.98  --comb_sup_mult                         2
% 3.28/0.98  --comb_inst_mult                        10
% 3.28/0.98  
% 3.28/0.98  ------ Debug Options
% 3.28/0.98  
% 3.28/0.98  --dbg_backtrace                         false
% 3.28/0.98  --dbg_dump_prop_clauses                 false
% 3.28/0.98  --dbg_dump_prop_clauses_file            -
% 3.28/0.98  --dbg_out_stat                          false
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  ------ Proving...
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  % SZS status Theorem for theBenchmark.p
% 3.28/0.98  
% 3.28/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.28/0.98  
% 3.28/0.98  fof(f16,conjecture,(
% 3.28/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f17,negated_conjecture,(
% 3.28/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.28/0.98    inference(negated_conjecture,[],[f16])).
% 3.28/0.98  
% 3.28/0.98  fof(f38,plain,(
% 3.28/0.98    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.28/0.98    inference(ennf_transformation,[],[f17])).
% 3.28/0.98  
% 3.28/0.98  fof(f39,plain,(
% 3.28/0.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.28/0.98    inference(flattening,[],[f38])).
% 3.28/0.98  
% 3.28/0.98  fof(f43,plain,(
% 3.28/0.98    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.28/0.98    introduced(choice_axiom,[])).
% 3.28/0.98  
% 3.28/0.98  fof(f42,plain,(
% 3.28/0.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.28/0.98    introduced(choice_axiom,[])).
% 3.28/0.98  
% 3.28/0.98  fof(f44,plain,(
% 3.28/0.98    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.28/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f43,f42])).
% 3.28/0.98  
% 3.28/0.98  fof(f72,plain,(
% 3.28/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.28/0.98    inference(cnf_transformation,[],[f44])).
% 3.28/0.98  
% 3.28/0.98  fof(f75,plain,(
% 3.28/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.28/0.98    inference(cnf_transformation,[],[f44])).
% 3.28/0.98  
% 3.28/0.98  fof(f12,axiom,(
% 3.28/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f32,plain,(
% 3.28/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.28/0.98    inference(ennf_transformation,[],[f12])).
% 3.28/0.98  
% 3.28/0.98  fof(f33,plain,(
% 3.28/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.28/0.98    inference(flattening,[],[f32])).
% 3.28/0.98  
% 3.28/0.98  fof(f63,plain,(
% 3.28/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f33])).
% 3.28/0.98  
% 3.28/0.98  fof(f73,plain,(
% 3.28/0.98    v1_funct_1(sK3)),
% 3.28/0.98    inference(cnf_transformation,[],[f44])).
% 3.28/0.98  
% 3.28/0.98  fof(f70,plain,(
% 3.28/0.98    v1_funct_1(sK2)),
% 3.28/0.98    inference(cnf_transformation,[],[f44])).
% 3.28/0.98  
% 3.28/0.98  fof(f8,axiom,(
% 3.28/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f26,plain,(
% 3.28/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.28/0.98    inference(ennf_transformation,[],[f8])).
% 3.28/0.98  
% 3.28/0.98  fof(f27,plain,(
% 3.28/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.28/0.98    inference(flattening,[],[f26])).
% 3.28/0.98  
% 3.28/0.98  fof(f40,plain,(
% 3.28/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.28/0.98    inference(nnf_transformation,[],[f27])).
% 3.28/0.98  
% 3.28/0.98  fof(f52,plain,(
% 3.28/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.28/0.98    inference(cnf_transformation,[],[f40])).
% 3.28/0.98  
% 3.28/0.98  fof(f77,plain,(
% 3.28/0.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.28/0.98    inference(cnf_transformation,[],[f44])).
% 3.28/0.98  
% 3.28/0.98  fof(f11,axiom,(
% 3.28/0.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f18,plain,(
% 3.28/0.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.28/0.98    inference(pure_predicate_removal,[],[f11])).
% 3.28/0.98  
% 3.28/0.98  fof(f62,plain,(
% 3.28/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.28/0.98    inference(cnf_transformation,[],[f18])).
% 3.28/0.98  
% 3.28/0.98  fof(f10,axiom,(
% 3.28/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f30,plain,(
% 3.28/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.28/0.98    inference(ennf_transformation,[],[f10])).
% 3.28/0.98  
% 3.28/0.98  fof(f31,plain,(
% 3.28/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.28/0.98    inference(flattening,[],[f30])).
% 3.28/0.98  
% 3.28/0.98  fof(f61,plain,(
% 3.28/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f31])).
% 3.28/0.98  
% 3.28/0.98  fof(f4,axiom,(
% 3.28/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f20,plain,(
% 3.28/0.98    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.28/0.98    inference(ennf_transformation,[],[f4])).
% 3.28/0.98  
% 3.28/0.98  fof(f21,plain,(
% 3.28/0.98    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.28/0.98    inference(flattening,[],[f20])).
% 3.28/0.98  
% 3.28/0.98  fof(f48,plain,(
% 3.28/0.98    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f21])).
% 3.28/0.98  
% 3.28/0.98  fof(f13,axiom,(
% 3.28/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f64,plain,(
% 3.28/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f13])).
% 3.28/0.98  
% 3.28/0.98  fof(f83,plain,(
% 3.28/0.98    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.28/0.98    inference(definition_unfolding,[],[f48,f64])).
% 3.28/0.98  
% 3.28/0.98  fof(f7,axiom,(
% 3.28/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f25,plain,(
% 3.28/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.28/0.98    inference(ennf_transformation,[],[f7])).
% 3.28/0.98  
% 3.28/0.98  fof(f51,plain,(
% 3.28/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.28/0.98    inference(cnf_transformation,[],[f25])).
% 3.28/0.98  
% 3.28/0.98  fof(f76,plain,(
% 3.28/0.98    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.28/0.98    inference(cnf_transformation,[],[f44])).
% 3.28/0.98  
% 3.28/0.98  fof(f14,axiom,(
% 3.28/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f34,plain,(
% 3.28/0.98    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.28/0.98    inference(ennf_transformation,[],[f14])).
% 3.28/0.98  
% 3.28/0.98  fof(f35,plain,(
% 3.28/0.98    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.28/0.98    inference(flattening,[],[f34])).
% 3.28/0.98  
% 3.28/0.98  fof(f65,plain,(
% 3.28/0.98    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f35])).
% 3.28/0.98  
% 3.28/0.98  fof(f71,plain,(
% 3.28/0.98    v1_funct_2(sK2,sK0,sK1)),
% 3.28/0.98    inference(cnf_transformation,[],[f44])).
% 3.28/0.98  
% 3.28/0.98  fof(f74,plain,(
% 3.28/0.98    v1_funct_2(sK3,sK1,sK0)),
% 3.28/0.98    inference(cnf_transformation,[],[f44])).
% 3.28/0.98  
% 3.28/0.98  fof(f9,axiom,(
% 3.28/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f28,plain,(
% 3.28/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.28/0.98    inference(ennf_transformation,[],[f9])).
% 3.28/0.98  
% 3.28/0.98  fof(f29,plain,(
% 3.28/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.28/0.98    inference(flattening,[],[f28])).
% 3.28/0.98  
% 3.28/0.98  fof(f41,plain,(
% 3.28/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.28/0.98    inference(nnf_transformation,[],[f29])).
% 3.28/0.98  
% 3.28/0.98  fof(f54,plain,(
% 3.28/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.28/0.98    inference(cnf_transformation,[],[f41])).
% 3.28/0.98  
% 3.28/0.98  fof(f6,axiom,(
% 3.28/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f24,plain,(
% 3.28/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.28/0.98    inference(ennf_transformation,[],[f6])).
% 3.28/0.98  
% 3.28/0.98  fof(f50,plain,(
% 3.28/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.28/0.98    inference(cnf_transformation,[],[f24])).
% 3.28/0.98  
% 3.28/0.98  fof(f79,plain,(
% 3.28/0.98    k1_xboole_0 != sK0),
% 3.28/0.98    inference(cnf_transformation,[],[f44])).
% 3.28/0.98  
% 3.28/0.98  fof(f1,axiom,(
% 3.28/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f19,plain,(
% 3.28/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.28/0.98    inference(ennf_transformation,[],[f1])).
% 3.28/0.98  
% 3.28/0.98  fof(f45,plain,(
% 3.28/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f19])).
% 3.28/0.98  
% 3.28/0.98  fof(f2,axiom,(
% 3.28/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f46,plain,(
% 3.28/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.28/0.99    inference(cnf_transformation,[],[f2])).
% 3.28/0.99  
% 3.28/0.99  fof(f15,axiom,(
% 3.28/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.99  
% 3.28/0.99  fof(f36,plain,(
% 3.28/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.28/0.99    inference(ennf_transformation,[],[f15])).
% 3.28/0.99  
% 3.28/0.99  fof(f37,plain,(
% 3.28/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.28/0.99    inference(flattening,[],[f36])).
% 3.28/0.99  
% 3.28/0.99  fof(f68,plain,(
% 3.28/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.28/0.99    inference(cnf_transformation,[],[f37])).
% 3.28/0.99  
% 3.28/0.99  fof(f3,axiom,(
% 3.28/0.99    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.99  
% 3.28/0.99  fof(f47,plain,(
% 3.28/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.28/0.99    inference(cnf_transformation,[],[f3])).
% 3.28/0.99  
% 3.28/0.99  fof(f82,plain,(
% 3.28/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.28/0.99    inference(definition_unfolding,[],[f47,f64])).
% 3.28/0.99  
% 3.28/0.99  fof(f5,axiom,(
% 3.28/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.99  
% 3.28/0.99  fof(f22,plain,(
% 3.28/0.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.28/0.99    inference(ennf_transformation,[],[f5])).
% 3.28/0.99  
% 3.28/0.99  fof(f23,plain,(
% 3.28/0.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.28/0.99    inference(flattening,[],[f22])).
% 3.28/0.99  
% 3.28/0.99  fof(f49,plain,(
% 3.28/0.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.28/0.99    inference(cnf_transformation,[],[f23])).
% 3.28/0.99  
% 3.28/0.99  fof(f81,plain,(
% 3.28/0.99    k2_funct_1(sK2) != sK3),
% 3.28/0.99    inference(cnf_transformation,[],[f44])).
% 3.28/0.99  
% 3.28/0.99  cnf(c_33,negated_conjecture,
% 3.28/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.28/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1204,plain,
% 3.28/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_30,negated_conjecture,
% 3.28/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.28/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1207,plain,
% 3.28/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_18,plain,
% 3.28/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.28/0.99      | ~ v1_funct_1(X0)
% 3.28/0.99      | ~ v1_funct_1(X3)
% 3.28/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.28/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1213,plain,
% 3.28/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.28/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.28/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.28/0.99      | v1_funct_1(X4) != iProver_top
% 3.28/0.99      | v1_funct_1(X5) != iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_4457,plain,
% 3.28/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.28/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.28/0.99      | v1_funct_1(X2) != iProver_top
% 3.28/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.28/0.99      inference(superposition,[status(thm)],[c_1207,c_1213]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_32,negated_conjecture,
% 3.28/0.99      ( v1_funct_1(sK3) ),
% 3.28/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_39,plain,
% 3.28/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_4850,plain,
% 3.28/0.99      ( v1_funct_1(X2) != iProver_top
% 3.28/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.28/0.99      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.28/0.99      inference(global_propositional_subsumption,
% 3.28/0.99                [status(thm)],
% 3.28/0.99                [c_4457,c_39]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_4851,plain,
% 3.28/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.28/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.28/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.28/0.99      inference(renaming,[status(thm)],[c_4850]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_4862,plain,
% 3.28/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.28/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.28/0.99      inference(superposition,[status(thm)],[c_1204,c_4851]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_35,negated_conjecture,
% 3.28/0.99      ( v1_funct_1(sK2) ),
% 3.28/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1722,plain,
% 3.28/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.28/0.99      | ~ v1_funct_1(X0)
% 3.28/0.99      | ~ v1_funct_1(sK3)
% 3.28/0.99      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 3.28/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2070,plain,
% 3.28/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.28/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.28/0.99      | ~ v1_funct_1(sK3)
% 3.28/0.99      | ~ v1_funct_1(sK2)
% 3.28/0.99      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.28/0.99      inference(instantiation,[status(thm)],[c_1722]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2339,plain,
% 3.28/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.28/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.28/0.99      | ~ v1_funct_1(sK3)
% 3.28/0.99      | ~ v1_funct_1(sK2)
% 3.28/0.99      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.28/0.99      inference(instantiation,[status(thm)],[c_2070]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2453,plain,
% 3.28/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.28/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.28/0.99      | ~ v1_funct_1(sK3)
% 3.28/0.99      | ~ v1_funct_1(sK2)
% 3.28/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.28/0.99      inference(instantiation,[status(thm)],[c_2339]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_4950,plain,
% 3.28/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.28/0.99      inference(global_propositional_subsumption,
% 3.28/0.99                [status(thm)],
% 3.28/0.99                [c_4862,c_35,c_33,c_32,c_30,c_2453]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_8,plain,
% 3.28/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.28/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.28/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.28/0.99      | X3 = X2 ),
% 3.28/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_28,negated_conjecture,
% 3.28/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.28/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_390,plain,
% 3.28/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/0.99      | X3 = X0
% 3.28/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.28/0.99      | k6_partfun1(sK0) != X3
% 3.28/0.99      | sK0 != X2
% 3.28/0.99      | sK0 != X1 ),
% 3.28/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_28]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_391,plain,
% 3.28/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.28/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.28/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.28/0.99      inference(unflattening,[status(thm)],[c_390]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_17,plain,
% 3.28/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.28/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_399,plain,
% 3.28/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.28/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.28/0.99      inference(forward_subsumption_resolution,
% 3.28/0.99                [status(thm)],
% 3.28/0.99                [c_391,c_17]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1200,plain,
% 3.28/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.28/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_4953,plain,
% 3.28/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.28/0.99      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.28/0.99      inference(demodulation,[status(thm)],[c_4950,c_1200]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_36,plain,
% 3.28/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_38,plain,
% 3.28/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_41,plain,
% 3.28/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_15,plain,
% 3.28/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.28/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.28/0.99      | ~ v1_funct_1(X0)
% 3.28/0.99      | ~ v1_funct_1(X3) ),
% 3.28/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1216,plain,
% 3.28/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.28/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.28/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.28/0.99      | v1_funct_1(X3) != iProver_top
% 3.28/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_4979,plain,
% 3.28/0.99      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.28/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.28/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.28/0.99      | v1_funct_1(sK3) != iProver_top
% 3.28/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.28/0.99      inference(superposition,[status(thm)],[c_4950,c_1216]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_5166,plain,
% 3.28/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.28/0.99      inference(global_propositional_subsumption,
% 3.28/0.99                [status(thm)],
% 3.28/0.99                [c_4953,c_36,c_38,c_39,c_41,c_4979]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_3,plain,
% 3.28/0.99      ( ~ v1_funct_1(X0)
% 3.28/0.99      | ~ v1_funct_1(X1)
% 3.28/0.99      | ~ v2_funct_1(X1)
% 3.28/0.99      | ~ v1_relat_1(X1)
% 3.28/0.99      | ~ v1_relat_1(X0)
% 3.28/0.99      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.28/0.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.28/0.99      | k2_funct_1(X1) = X0 ),
% 3.28/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1226,plain,
% 3.28/0.99      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.28/0.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.28/0.99      | k2_funct_1(X1) = X0
% 3.28/0.99      | v1_funct_1(X0) != iProver_top
% 3.28/0.99      | v1_funct_1(X1) != iProver_top
% 3.28/0.99      | v2_funct_1(X1) != iProver_top
% 3.28/0.99      | v1_relat_1(X0) != iProver_top
% 3.28/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_5170,plain,
% 3.28/0.99      ( k1_relat_1(sK3) != k2_relat_1(sK2)
% 3.28/0.99      | k2_funct_1(sK3) = sK2
% 3.28/0.99      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 3.28/0.99      | v1_funct_1(sK3) != iProver_top
% 3.28/0.99      | v1_funct_1(sK2) != iProver_top
% 3.28/0.99      | v2_funct_1(sK3) != iProver_top
% 3.28/0.99      | v1_relat_1(sK3) != iProver_top
% 3.28/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.28/0.99      inference(superposition,[status(thm)],[c_5166,c_1226]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_6,plain,
% 3.28/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.28/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1223,plain,
% 3.28/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.28/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2140,plain,
% 3.28/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.28/0.99      inference(superposition,[status(thm)],[c_1204,c_1223]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_29,negated_conjecture,
% 3.28/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.28/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2142,plain,
% 3.28/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.28/0.99      inference(light_normalisation,[status(thm)],[c_2140,c_29]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2139,plain,
% 3.28/0.99      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.28/0.99      inference(superposition,[status(thm)],[c_1207,c_1223]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_19,plain,
% 3.28/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.28/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.28/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.28/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.28/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.28/0.99      | ~ v1_funct_1(X2)
% 3.28/0.99      | ~ v1_funct_1(X3)
% 3.28/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.28/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_403,plain,
% 3.28/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.28/0.99      | ~ v1_funct_2(X3,X2,X1)
% 3.28/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.28/0.99      | ~ v1_funct_1(X0)
% 3.28/0.99      | ~ v1_funct_1(X3)
% 3.28/0.99      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.28/0.99      | k2_relset_1(X1,X2,X0) = X2
% 3.28/0.99      | k6_partfun1(X2) != k6_partfun1(sK0)
% 3.28/0.99      | sK0 != X2 ),
% 3.28/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_404,plain,
% 3.28/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 3.28/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 3.28/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.28/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.28/0.99      | ~ v1_funct_1(X0)
% 3.28/0.99      | ~ v1_funct_1(X2)
% 3.28/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.28/0.99      | k2_relset_1(X1,sK0,X0) = sK0
% 3.28/0.99      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.28/0.99      inference(unflattening,[status(thm)],[c_403]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_489,plain,
% 3.28/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 3.28/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 3.28/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.28/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.28/0.99      | ~ v1_funct_1(X0)
% 3.28/0.99      | ~ v1_funct_1(X2)
% 3.28/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.28/0.99      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.28/0.99      inference(equality_resolution_simp,[status(thm)],[c_404]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1199,plain,
% 3.28/0.99      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.28/0.99      | k2_relset_1(X0,sK0,X2) = sK0
% 3.28/0.99      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.28/0.99      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.28/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.28/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.28/0.99      | v1_funct_1(X2) != iProver_top
% 3.28/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1831,plain,
% 3.28/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.28/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.28/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.28/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.28/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.28/0.99      | v1_funct_1(sK3) != iProver_top
% 3.28/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.28/0.99      inference(equality_resolution,[status(thm)],[c_1199]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_34,negated_conjecture,
% 3.28/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.28/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_37,plain,
% 3.28/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_31,negated_conjecture,
% 3.28/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.28/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_40,plain,
% 3.28/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2040,plain,
% 3.28/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.28/0.99      inference(global_propositional_subsumption,
% 3.28/0.99                [status(thm)],
% 3.28/0.99                [c_1831,c_36,c_37,c_38,c_39,c_40,c_41]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2145,plain,
% 3.28/0.99      ( k2_relat_1(sK3) = sK0 ),
% 3.28/0.99      inference(light_normalisation,[status(thm)],[c_2139,c_2040]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_14,plain,
% 3.28/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.28/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.28/0.99      | k1_xboole_0 = X2 ),
% 3.28/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1217,plain,
% 3.28/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.28/0.99      | k1_xboole_0 = X1
% 3.28/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.28/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_3011,plain,
% 3.28/0.99      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 3.28/0.99      | sK0 = k1_xboole_0
% 3.28/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.28/0.99      inference(superposition,[status(thm)],[c_1207,c_1217]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_5,plain,
% 3.28/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.28/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1224,plain,
% 3.28/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.28/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2291,plain,
% 3.28/0.99      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 3.28/0.99      inference(superposition,[status(thm)],[c_1207,c_1224]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_3023,plain,
% 3.28/0.99      ( k1_relat_1(sK3) = sK1
% 3.28/0.99      | sK0 = k1_xboole_0
% 3.28/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.28/0.99      inference(demodulation,[status(thm)],[c_3011,c_2291]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_26,negated_conjecture,
% 3.28/0.99      ( k1_xboole_0 != sK0 ),
% 3.28/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_666,plain,( X0 = X0 ),theory(equality) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_693,plain,
% 3.28/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.28/0.99      inference(instantiation,[status(thm)],[c_666]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_667,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1601,plain,
% 3.28/0.99      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.28/0.99      inference(instantiation,[status(thm)],[c_667]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1602,plain,
% 3.28/0.99      ( sK0 != k1_xboole_0
% 3.28/0.99      | k1_xboole_0 = sK0
% 3.28/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.28/0.99      inference(instantiation,[status(thm)],[c_1601]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_3401,plain,
% 3.28/0.99      ( k1_relat_1(sK3) = sK1 ),
% 3.28/0.99      inference(global_propositional_subsumption,
% 3.28/0.99                [status(thm)],
% 3.28/0.99                [c_3023,c_40,c_26,c_693,c_1602]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_5171,plain,
% 3.28/0.99      ( k2_funct_1(sK3) = sK2
% 3.28/0.99      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 3.28/0.99      | sK1 != sK1
% 3.28/0.99      | v1_funct_1(sK3) != iProver_top
% 3.28/0.99      | v1_funct_1(sK2) != iProver_top
% 3.28/0.99      | v2_funct_1(sK3) != iProver_top
% 3.28/0.99      | v1_relat_1(sK3) != iProver_top
% 3.28/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.28/0.99      inference(light_normalisation,
% 3.28/0.99                [status(thm)],
% 3.28/0.99                [c_5170,c_2142,c_2145,c_3401]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_5172,plain,
% 3.28/0.99      ( k2_funct_1(sK3) = sK2
% 3.28/0.99      | v1_funct_1(sK3) != iProver_top
% 3.28/0.99      | v1_funct_1(sK2) != iProver_top
% 3.28/0.99      | v2_funct_1(sK3) != iProver_top
% 3.28/0.99      | v1_relat_1(sK3) != iProver_top
% 3.28/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.28/0.99      inference(equality_resolution_simp,[status(thm)],[c_5171]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_0,plain,
% 3.28/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.28/0.99      | ~ v1_relat_1(X1)
% 3.28/0.99      | v1_relat_1(X0) ),
% 3.28/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1565,plain,
% 3.28/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/0.99      | v1_relat_1(X0)
% 3.28/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.28/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2048,plain,
% 3.28/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.28/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 3.28/0.99      | v1_relat_1(sK3) ),
% 3.28/0.99      inference(instantiation,[status(thm)],[c_1565]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2049,plain,
% 3.28/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.28/0.99      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.28/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_2048]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2051,plain,
% 3.28/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.28/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.28/0.99      | v1_relat_1(sK2) ),
% 3.28/0.99      inference(instantiation,[status(thm)],[c_1565]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2052,plain,
% 3.28/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.28/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.28/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_2051]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1,plain,
% 3.28/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.28/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2255,plain,
% 3.28/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.28/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2256,plain,
% 3.28/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_2255]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2268,plain,
% 3.28/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.28/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2269,plain,
% 3.28/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_2268]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_5169,plain,
% 3.28/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 3.28/0.99      inference(demodulation,[status(thm)],[c_5166,c_4950]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_21,plain,
% 3.28/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.28/0.99      | ~ v1_funct_2(X3,X2,X4)
% 3.28/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.28/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.28/0.99      | ~ v1_funct_1(X3)
% 3.28/0.99      | ~ v1_funct_1(X0)
% 3.28/0.99      | v2_funct_1(X3)
% 3.28/0.99      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 3.28/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.28/0.99      | k1_xboole_0 = X4 ),
% 3.28/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1211,plain,
% 3.28/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.28/0.99      | k1_xboole_0 = X3
% 3.28/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.28/0.99      | v1_funct_2(X4,X1,X3) != iProver_top
% 3.28/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.28/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 3.28/0.99      | v1_funct_1(X4) != iProver_top
% 3.28/0.99      | v1_funct_1(X2) != iProver_top
% 3.28/0.99      | v2_funct_1(X4) = iProver_top
% 3.28/0.99      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_5255,plain,
% 3.28/0.99      ( k1_xboole_0 = X0
% 3.28/0.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.28/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.28/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.28/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.28/0.99      | v1_funct_1(X1) != iProver_top
% 3.28/0.99      | v1_funct_1(sK2) != iProver_top
% 3.28/0.99      | v2_funct_1(X1) = iProver_top
% 3.28/0.99      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.28/0.99      inference(superposition,[status(thm)],[c_29,c_1211]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_5318,plain,
% 3.28/0.99      ( v1_funct_1(X1) != iProver_top
% 3.28/0.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.28/0.99      | k1_xboole_0 = X0
% 3.28/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.28/0.99      | v2_funct_1(X1) = iProver_top
% 3.28/0.99      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.28/0.99      inference(global_propositional_subsumption,
% 3.28/0.99                [status(thm)],
% 3.28/0.99                [c_5255,c_36,c_37,c_38]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_5319,plain,
% 3.28/0.99      ( k1_xboole_0 = X0
% 3.28/0.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.28/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.28/0.99      | v1_funct_1(X1) != iProver_top
% 3.28/0.99      | v2_funct_1(X1) = iProver_top
% 3.28/0.99      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.28/0.99      inference(renaming,[status(thm)],[c_5318]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_5328,plain,
% 3.28/0.99      ( sK0 = k1_xboole_0
% 3.28/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.28/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.28/0.99      | v1_funct_1(sK3) != iProver_top
% 3.28/0.99      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.28/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.28/0.99      inference(superposition,[status(thm)],[c_5169,c_5319]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_5645,plain,
% 3.28/0.99      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.28/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.28/0.99      inference(global_propositional_subsumption,
% 3.28/0.99                [status(thm)],
% 3.28/0.99                [c_5328,c_39,c_40,c_41,c_26,c_693,c_1602]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2,plain,
% 3.28/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.28/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1227,plain,
% 3.28/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_5651,plain,
% 3.28/0.99      ( v2_funct_1(sK3) = iProver_top ),
% 3.28/0.99      inference(forward_subsumption_resolution,
% 3.28/0.99                [status(thm)],
% 3.28/0.99                [c_5645,c_1227]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_7700,plain,
% 3.28/0.99      ( k2_funct_1(sK3) = sK2 ),
% 3.28/0.99      inference(global_propositional_subsumption,
% 3.28/0.99                [status(thm)],
% 3.28/0.99                [c_5172,c_36,c_38,c_39,c_41,c_2049,c_2052,c_2256,c_2269,
% 3.28/0.99                 c_5651]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1205,plain,
% 3.28/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_4,plain,
% 3.28/0.99      ( ~ v1_funct_1(X0)
% 3.28/0.99      | ~ v2_funct_1(X0)
% 3.28/0.99      | ~ v1_relat_1(X0)
% 3.28/0.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.28/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_1225,plain,
% 3.28/0.99      ( k2_funct_1(k2_funct_1(X0)) = X0
% 3.28/0.99      | v1_funct_1(X0) != iProver_top
% 3.28/0.99      | v2_funct_1(X0) != iProver_top
% 3.28/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.28/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2383,plain,
% 3.28/0.99      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.28/0.99      | v2_funct_1(sK3) != iProver_top
% 3.28/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.28/0.99      inference(superposition,[status(thm)],[c_1205,c_1225]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2585,plain,
% 3.28/0.99      ( v2_funct_1(sK3) != iProver_top
% 3.28/0.99      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 3.28/0.99      inference(global_propositional_subsumption,
% 3.28/0.99                [status(thm)],
% 3.28/0.99                [c_2383,c_41,c_2049,c_2256]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_2586,plain,
% 3.28/0.99      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.28/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.28/0.99      inference(renaming,[status(thm)],[c_2585]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_5653,plain,
% 3.28/0.99      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 3.28/0.99      inference(superposition,[status(thm)],[c_5651,c_2586]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_7703,plain,
% 3.28/0.99      ( k2_funct_1(sK2) = sK3 ),
% 3.28/0.99      inference(demodulation,[status(thm)],[c_7700,c_5653]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(c_24,negated_conjecture,
% 3.28/0.99      ( k2_funct_1(sK2) != sK3 ),
% 3.28/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.28/0.99  
% 3.28/0.99  cnf(contradiction,plain,
% 3.28/0.99      ( $false ),
% 3.28/0.99      inference(minisat,[status(thm)],[c_7703,c_24]) ).
% 3.28/0.99  
% 3.28/0.99  
% 3.28/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.28/0.99  
% 3.28/0.99  ------                               Statistics
% 3.28/0.99  
% 3.28/0.99  ------ General
% 3.28/0.99  
% 3.28/0.99  abstr_ref_over_cycles:                  0
% 3.28/0.99  abstr_ref_under_cycles:                 0
% 3.28/0.99  gc_basic_clause_elim:                   0
% 3.28/0.99  forced_gc_time:                         0
% 3.28/0.99  parsing_time:                           0.012
% 3.28/0.99  unif_index_cands_time:                  0.
% 3.28/0.99  unif_index_add_time:                    0.
% 3.28/0.99  orderings_time:                         0.
% 3.28/0.99  out_proof_time:                         0.011
% 3.28/0.99  total_time:                             0.31
% 3.28/0.99  num_of_symbols:                         52
% 3.28/0.99  num_of_terms:                           9620
% 3.28/0.99  
% 3.28/0.99  ------ Preprocessing
% 3.28/0.99  
% 3.28/0.99  num_of_splits:                          0
% 3.28/0.99  num_of_split_atoms:                     0
% 3.28/0.99  num_of_reused_defs:                     0
% 3.28/0.99  num_eq_ax_congr_red:                    18
% 3.28/0.99  num_of_sem_filtered_clauses:            1
% 3.28/0.99  num_of_subtypes:                        0
% 3.28/0.99  monotx_restored_types:                  0
% 3.28/0.99  sat_num_of_epr_types:                   0
% 3.28/0.99  sat_num_of_non_cyclic_types:            0
% 3.28/0.99  sat_guarded_non_collapsed_types:        0
% 3.28/0.99  num_pure_diseq_elim:                    0
% 3.28/0.99  simp_replaced_by:                       0
% 3.28/0.99  res_preprocessed:                       170
% 3.28/0.99  prep_upred:                             0
% 3.28/0.99  prep_unflattend:                        12
% 3.28/0.99  smt_new_axioms:                         0
% 3.28/0.99  pred_elim_cands:                        5
% 3.28/0.99  pred_elim:                              1
% 3.28/0.99  pred_elim_cl:                           1
% 3.28/0.99  pred_elim_cycles:                       3
% 3.28/0.99  merged_defs:                            0
% 3.28/0.99  merged_defs_ncl:                        0
% 3.28/0.99  bin_hyper_res:                          0
% 3.28/0.99  prep_cycles:                            4
% 3.28/0.99  pred_elim_time:                         0.005
% 3.28/0.99  splitting_time:                         0.
% 3.28/0.99  sem_filter_time:                        0.
% 3.28/0.99  monotx_time:                            0.001
% 3.28/0.99  subtype_inf_time:                       0.
% 3.28/0.99  
% 3.28/0.99  ------ Problem properties
% 3.28/0.99  
% 3.28/0.99  clauses:                                35
% 3.28/0.99  conjectures:                            11
% 3.28/0.99  epr:                                    7
% 3.28/0.99  horn:                                   29
% 3.28/0.99  ground:                                 12
% 3.28/0.99  unary:                                  14
% 3.28/0.99  binary:                                 3
% 3.28/0.99  lits:                                   125
% 3.28/0.99  lits_eq:                                31
% 3.28/0.99  fd_pure:                                0
% 3.28/0.99  fd_pseudo:                              0
% 3.28/0.99  fd_cond:                                5
% 3.28/0.99  fd_pseudo_cond:                         1
% 3.28/0.99  ac_symbols:                             0
% 3.28/0.99  
% 3.28/0.99  ------ Propositional Solver
% 3.28/0.99  
% 3.28/0.99  prop_solver_calls:                      27
% 3.28/0.99  prop_fast_solver_calls:                 1489
% 3.28/0.99  smt_solver_calls:                       0
% 3.28/0.99  smt_fast_solver_calls:                  0
% 3.28/0.99  prop_num_of_clauses:                    3130
% 3.28/0.99  prop_preprocess_simplified:             9526
% 3.28/0.99  prop_fo_subsumed:                       52
% 3.28/0.99  prop_solver_time:                       0.
% 3.28/0.99  smt_solver_time:                        0.
% 3.28/0.99  smt_fast_solver_time:                   0.
% 3.28/0.99  prop_fast_solver_time:                  0.
% 3.28/0.99  prop_unsat_core_time:                   0.
% 3.28/0.99  
% 3.28/0.99  ------ QBF
% 3.28/0.99  
% 3.28/0.99  qbf_q_res:                              0
% 3.28/0.99  qbf_num_tautologies:                    0
% 3.28/0.99  qbf_prep_cycles:                        0
% 3.28/0.99  
% 3.28/0.99  ------ BMC1
% 3.28/0.99  
% 3.28/0.99  bmc1_current_bound:                     -1
% 3.28/0.99  bmc1_last_solved_bound:                 -1
% 3.28/0.99  bmc1_unsat_core_size:                   -1
% 3.28/0.99  bmc1_unsat_core_parents_size:           -1
% 3.28/0.99  bmc1_merge_next_fun:                    0
% 3.28/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.28/0.99  
% 3.28/0.99  ------ Instantiation
% 3.28/0.99  
% 3.28/0.99  inst_num_of_clauses:                    900
% 3.28/0.99  inst_num_in_passive:                    476
% 3.28/0.99  inst_num_in_active:                     399
% 3.28/0.99  inst_num_in_unprocessed:                25
% 3.28/0.99  inst_num_of_loops:                      410
% 3.28/0.99  inst_num_of_learning_restarts:          0
% 3.28/0.99  inst_num_moves_active_passive:          9
% 3.28/0.99  inst_lit_activity:                      0
% 3.28/0.99  inst_lit_activity_moves:                0
% 3.28/0.99  inst_num_tautologies:                   0
% 3.28/0.99  inst_num_prop_implied:                  0
% 3.28/0.99  inst_num_existing_simplified:           0
% 3.28/0.99  inst_num_eq_res_simplified:             0
% 3.28/0.99  inst_num_child_elim:                    0
% 3.28/0.99  inst_num_of_dismatching_blockings:      60
% 3.28/0.99  inst_num_of_non_proper_insts:           658
% 3.28/0.99  inst_num_of_duplicates:                 0
% 3.28/0.99  inst_inst_num_from_inst_to_res:         0
% 3.28/0.99  inst_dismatching_checking_time:         0.
% 3.28/0.99  
% 3.28/0.99  ------ Resolution
% 3.28/0.99  
% 3.28/0.99  res_num_of_clauses:                     0
% 3.28/0.99  res_num_in_passive:                     0
% 3.28/0.99  res_num_in_active:                      0
% 3.28/0.99  res_num_of_loops:                       174
% 3.28/0.99  res_forward_subset_subsumed:            94
% 3.28/0.99  res_backward_subset_subsumed:           0
% 3.28/0.99  res_forward_subsumed:                   0
% 3.28/0.99  res_backward_subsumed:                  0
% 3.28/0.99  res_forward_subsumption_resolution:     2
% 3.28/0.99  res_backward_subsumption_resolution:    0
% 3.28/0.99  res_clause_to_clause_subsumption:       158
% 3.28/0.99  res_orphan_elimination:                 0
% 3.28/0.99  res_tautology_del:                      24
% 3.28/0.99  res_num_eq_res_simplified:              1
% 3.28/0.99  res_num_sel_changes:                    0
% 3.28/0.99  res_moves_from_active_to_pass:          0
% 3.28/0.99  
% 3.28/0.99  ------ Superposition
% 3.28/0.99  
% 3.28/0.99  sup_time_total:                         0.
% 3.28/0.99  sup_time_generating:                    0.
% 3.28/0.99  sup_time_sim_full:                      0.
% 3.28/0.99  sup_time_sim_immed:                     0.
% 3.28/0.99  
% 3.28/0.99  sup_num_of_clauses:                     117
% 3.28/0.99  sup_num_in_active:                      73
% 3.28/0.99  sup_num_in_passive:                     44
% 3.28/0.99  sup_num_of_loops:                       80
% 3.28/0.99  sup_fw_superposition:                   40
% 3.28/0.99  sup_bw_superposition:                   54
% 3.28/0.99  sup_immediate_simplified:               19
% 3.28/0.99  sup_given_eliminated:                   0
% 3.28/0.99  comparisons_done:                       0
% 3.28/0.99  comparisons_avoided:                    0
% 3.28/0.99  
% 3.28/0.99  ------ Simplifications
% 3.28/0.99  
% 3.28/0.99  
% 3.28/0.99  sim_fw_subset_subsumed:                 8
% 3.28/0.99  sim_bw_subset_subsumed:                 2
% 3.28/0.99  sim_fw_subsumed:                        2
% 3.28/0.99  sim_bw_subsumed:                        0
% 3.28/0.99  sim_fw_subsumption_res:                 2
% 3.28/0.99  sim_bw_subsumption_res:                 0
% 3.28/0.99  sim_tautology_del:                      0
% 3.28/0.99  sim_eq_tautology_del:                   1
% 3.28/0.99  sim_eq_res_simp:                        1
% 3.28/0.99  sim_fw_demodulated:                     6
% 3.28/0.99  sim_bw_demodulated:                     6
% 3.28/0.99  sim_light_normalised:                   3
% 3.28/0.99  sim_joinable_taut:                      0
% 3.28/0.99  sim_joinable_simp:                      0
% 3.28/0.99  sim_ac_normalised:                      0
% 3.28/0.99  sim_smt_subsumption:                    0
% 3.28/0.99  
%------------------------------------------------------------------------------
