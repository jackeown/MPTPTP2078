%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:29 EST 2020

% Result     : Theorem 11.10s
% Output     : CNFRefutation 11.10s
% Verified   : 
% Statistics : Number of formulae       :  177 (1391 expanded)
%              Number of clauses        :  106 ( 419 expanded)
%              Number of leaves         :   20 ( 355 expanded)
%              Depth                    :   21
%              Number of atoms          :  688 (11878 expanded)
%              Number of equality atoms :  325 (4308 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(definition_unfolding,[],[f51,f67])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f44])).

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

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f81,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1175,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1178,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1180,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2556,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1180])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2856,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2556,c_38])).

cnf(c_2857,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2856])).

cnf(c_2867,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1175,c_2857])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1670,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1920,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1670])).

cnf(c_2165,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1920])).

cnf(c_2308,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2165])).

cnf(c_3037,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2867,c_34,c_32,c_31,c_29,c_2308])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1183,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4074,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3037,c_1183])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5410,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4074,c_35,c_37,c_38,c_40])).

cnf(c_11,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_382,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_390,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_382,c_20])).

cnf(c_1171,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_3040,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3037,c_1171])).

cnf(c_5422,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(superposition,[status(thm)],[c_5410,c_3040])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1193,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_33690,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5422,c_1193])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1190,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2065,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1175,c_1190])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2067,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2065,c_28])).

cnf(c_2064,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1178,c_1190])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_394,plain,
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
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_395,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_479,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_395])).

cnf(c_1170,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_1702,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1170])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1966,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1702,c_35,c_36,c_37,c_38,c_39,c_40])).

cnf(c_2070,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2064,c_1966])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1184,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2829,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1184])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1191,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2139,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1178,c_1191])).

cnf(c_2841,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2829,c_2139])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_651,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_678,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_652,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1533,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_1534,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1533])).

cnf(c_9589,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2841,c_39,c_25,c_678,c_1534])).

cnf(c_33691,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33690,c_2067,c_2070,c_9589])).

cnf(c_33692,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_33691])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1487,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2009,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1487])).

cnf(c_2010,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2009])).

cnf(c_2012,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1487])).

cnf(c_2013,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2012])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2082,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2083,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2082])).

cnf(c_2101,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2102,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2101])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_19659,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_19660,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19659])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1195,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9593,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9589,c_1195])).

cnf(c_22652,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9593,c_38,c_40,c_2010,c_2083])).

cnf(c_22653,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_22652])).

cnf(c_22664,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2067,c_22653])).

cnf(c_22736,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22664,c_35,c_37,c_2013,c_2102])).

cnf(c_22737,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_22736])).

cnf(c_33481,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5422,c_22737])).

cnf(c_34731,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_33692,c_35,c_37,c_38,c_40,c_2010,c_2013,c_2083,c_2102,c_19660,c_33481])).

cnf(c_34434,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33481,c_19660])).

cnf(c_1176,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1192,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2216,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_1192])).

cnf(c_2366,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2216,c_40,c_2010,c_2083])).

cnf(c_2367,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2366])).

cnf(c_34439,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_34434,c_2367])).

cnf(c_34734,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_34731,c_34439])).

cnf(c_23,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f80])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34734,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:41:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.10/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.10/1.99  
% 11.10/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.10/1.99  
% 11.10/1.99  ------  iProver source info
% 11.10/1.99  
% 11.10/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.10/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.10/1.99  git: non_committed_changes: false
% 11.10/1.99  git: last_make_outside_of_git: false
% 11.10/1.99  
% 11.10/1.99  ------ 
% 11.10/1.99  
% 11.10/1.99  ------ Input Options
% 11.10/1.99  
% 11.10/1.99  --out_options                           all
% 11.10/1.99  --tptp_safe_out                         true
% 11.10/1.99  --problem_path                          ""
% 11.10/1.99  --include_path                          ""
% 11.10/1.99  --clausifier                            res/vclausify_rel
% 11.10/1.99  --clausifier_options                    --mode clausify
% 11.10/1.99  --stdin                                 false
% 11.10/1.99  --stats_out                             all
% 11.10/1.99  
% 11.10/1.99  ------ General Options
% 11.10/1.99  
% 11.10/1.99  --fof                                   false
% 11.10/1.99  --time_out_real                         305.
% 11.10/1.99  --time_out_virtual                      -1.
% 11.10/1.99  --symbol_type_check                     false
% 11.10/1.99  --clausify_out                          false
% 11.10/1.99  --sig_cnt_out                           false
% 11.10/1.99  --trig_cnt_out                          false
% 11.10/1.99  --trig_cnt_out_tolerance                1.
% 11.10/1.99  --trig_cnt_out_sk_spl                   false
% 11.10/1.99  --abstr_cl_out                          false
% 11.10/1.99  
% 11.10/1.99  ------ Global Options
% 11.10/1.99  
% 11.10/1.99  --schedule                              default
% 11.10/1.99  --add_important_lit                     false
% 11.10/1.99  --prop_solver_per_cl                    1000
% 11.10/1.99  --min_unsat_core                        false
% 11.10/1.99  --soft_assumptions                      false
% 11.10/1.99  --soft_lemma_size                       3
% 11.10/1.99  --prop_impl_unit_size                   0
% 11.10/1.99  --prop_impl_unit                        []
% 11.10/1.99  --share_sel_clauses                     true
% 11.10/1.99  --reset_solvers                         false
% 11.10/1.99  --bc_imp_inh                            [conj_cone]
% 11.10/1.99  --conj_cone_tolerance                   3.
% 11.10/1.99  --extra_neg_conj                        none
% 11.10/1.99  --large_theory_mode                     true
% 11.10/1.99  --prolific_symb_bound                   200
% 11.10/1.99  --lt_threshold                          2000
% 11.10/1.99  --clause_weak_htbl                      true
% 11.10/1.99  --gc_record_bc_elim                     false
% 11.10/1.99  
% 11.10/1.99  ------ Preprocessing Options
% 11.10/1.99  
% 11.10/1.99  --preprocessing_flag                    true
% 11.10/1.99  --time_out_prep_mult                    0.1
% 11.10/1.99  --splitting_mode                        input
% 11.10/1.99  --splitting_grd                         true
% 11.10/1.99  --splitting_cvd                         false
% 11.10/1.99  --splitting_cvd_svl                     false
% 11.10/1.99  --splitting_nvd                         32
% 11.10/1.99  --sub_typing                            true
% 11.10/1.99  --prep_gs_sim                           true
% 11.10/1.99  --prep_unflatten                        true
% 11.10/1.99  --prep_res_sim                          true
% 11.10/1.99  --prep_upred                            true
% 11.10/1.99  --prep_sem_filter                       exhaustive
% 11.10/1.99  --prep_sem_filter_out                   false
% 11.10/1.99  --pred_elim                             true
% 11.10/1.99  --res_sim_input                         true
% 11.10/1.99  --eq_ax_congr_red                       true
% 11.10/1.99  --pure_diseq_elim                       true
% 11.10/1.99  --brand_transform                       false
% 11.10/1.99  --non_eq_to_eq                          false
% 11.10/1.99  --prep_def_merge                        true
% 11.10/1.99  --prep_def_merge_prop_impl              false
% 11.10/1.99  --prep_def_merge_mbd                    true
% 11.10/1.99  --prep_def_merge_tr_red                 false
% 11.10/1.99  --prep_def_merge_tr_cl                  false
% 11.10/1.99  --smt_preprocessing                     true
% 11.10/1.99  --smt_ac_axioms                         fast
% 11.10/1.99  --preprocessed_out                      false
% 11.10/1.99  --preprocessed_stats                    false
% 11.10/1.99  
% 11.10/1.99  ------ Abstraction refinement Options
% 11.10/1.99  
% 11.10/1.99  --abstr_ref                             []
% 11.10/1.99  --abstr_ref_prep                        false
% 11.10/1.99  --abstr_ref_until_sat                   false
% 11.10/1.99  --abstr_ref_sig_restrict                funpre
% 11.10/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.10/1.99  --abstr_ref_under                       []
% 11.10/1.99  
% 11.10/1.99  ------ SAT Options
% 11.10/1.99  
% 11.10/1.99  --sat_mode                              false
% 11.10/1.99  --sat_fm_restart_options                ""
% 11.10/1.99  --sat_gr_def                            false
% 11.10/1.99  --sat_epr_types                         true
% 11.10/1.99  --sat_non_cyclic_types                  false
% 11.10/1.99  --sat_finite_models                     false
% 11.10/1.99  --sat_fm_lemmas                         false
% 11.10/1.99  --sat_fm_prep                           false
% 11.10/1.99  --sat_fm_uc_incr                        true
% 11.10/1.99  --sat_out_model                         small
% 11.10/1.99  --sat_out_clauses                       false
% 11.10/1.99  
% 11.10/1.99  ------ QBF Options
% 11.10/1.99  
% 11.10/1.99  --qbf_mode                              false
% 11.10/1.99  --qbf_elim_univ                         false
% 11.10/1.99  --qbf_dom_inst                          none
% 11.10/1.99  --qbf_dom_pre_inst                      false
% 11.10/1.99  --qbf_sk_in                             false
% 11.10/1.99  --qbf_pred_elim                         true
% 11.10/1.99  --qbf_split                             512
% 11.10/1.99  
% 11.10/1.99  ------ BMC1 Options
% 11.10/1.99  
% 11.10/1.99  --bmc1_incremental                      false
% 11.10/1.99  --bmc1_axioms                           reachable_all
% 11.10/1.99  --bmc1_min_bound                        0
% 11.10/1.99  --bmc1_max_bound                        -1
% 11.10/1.99  --bmc1_max_bound_default                -1
% 11.10/1.99  --bmc1_symbol_reachability              true
% 11.10/1.99  --bmc1_property_lemmas                  false
% 11.10/1.99  --bmc1_k_induction                      false
% 11.10/1.99  --bmc1_non_equiv_states                 false
% 11.10/1.99  --bmc1_deadlock                         false
% 11.10/1.99  --bmc1_ucm                              false
% 11.10/1.99  --bmc1_add_unsat_core                   none
% 11.10/1.99  --bmc1_unsat_core_children              false
% 11.10/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.10/1.99  --bmc1_out_stat                         full
% 11.10/1.99  --bmc1_ground_init                      false
% 11.10/1.99  --bmc1_pre_inst_next_state              false
% 11.10/1.99  --bmc1_pre_inst_state                   false
% 11.10/1.99  --bmc1_pre_inst_reach_state             false
% 11.10/1.99  --bmc1_out_unsat_core                   false
% 11.10/1.99  --bmc1_aig_witness_out                  false
% 11.10/1.99  --bmc1_verbose                          false
% 11.10/1.99  --bmc1_dump_clauses_tptp                false
% 11.10/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.10/1.99  --bmc1_dump_file                        -
% 11.10/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.10/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.10/1.99  --bmc1_ucm_extend_mode                  1
% 11.10/1.99  --bmc1_ucm_init_mode                    2
% 11.10/1.99  --bmc1_ucm_cone_mode                    none
% 11.10/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.10/1.99  --bmc1_ucm_relax_model                  4
% 11.10/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.10/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.10/1.99  --bmc1_ucm_layered_model                none
% 11.10/1.99  --bmc1_ucm_max_lemma_size               10
% 11.10/1.99  
% 11.10/1.99  ------ AIG Options
% 11.10/1.99  
% 11.10/1.99  --aig_mode                              false
% 11.10/1.99  
% 11.10/1.99  ------ Instantiation Options
% 11.10/1.99  
% 11.10/1.99  --instantiation_flag                    true
% 11.10/1.99  --inst_sos_flag                         false
% 11.10/1.99  --inst_sos_phase                        true
% 11.10/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.10/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.10/1.99  --inst_lit_sel_side                     num_symb
% 11.10/1.99  --inst_solver_per_active                1400
% 11.10/1.99  --inst_solver_calls_frac                1.
% 11.10/1.99  --inst_passive_queue_type               priority_queues
% 11.10/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.10/1.99  --inst_passive_queues_freq              [25;2]
% 11.10/1.99  --inst_dismatching                      true
% 11.10/1.99  --inst_eager_unprocessed_to_passive     true
% 11.10/1.99  --inst_prop_sim_given                   true
% 11.10/1.99  --inst_prop_sim_new                     false
% 11.10/1.99  --inst_subs_new                         false
% 11.10/1.99  --inst_eq_res_simp                      false
% 11.10/1.99  --inst_subs_given                       false
% 11.10/1.99  --inst_orphan_elimination               true
% 11.10/1.99  --inst_learning_loop_flag               true
% 11.10/1.99  --inst_learning_start                   3000
% 11.10/1.99  --inst_learning_factor                  2
% 11.10/1.99  --inst_start_prop_sim_after_learn       3
% 11.10/1.99  --inst_sel_renew                        solver
% 11.10/1.99  --inst_lit_activity_flag                true
% 11.10/1.99  --inst_restr_to_given                   false
% 11.10/1.99  --inst_activity_threshold               500
% 11.10/1.99  --inst_out_proof                        true
% 11.10/1.99  
% 11.10/1.99  ------ Resolution Options
% 11.10/1.99  
% 11.10/1.99  --resolution_flag                       true
% 11.10/1.99  --res_lit_sel                           adaptive
% 11.10/1.99  --res_lit_sel_side                      none
% 11.10/1.99  --res_ordering                          kbo
% 11.10/1.99  --res_to_prop_solver                    active
% 11.10/1.99  --res_prop_simpl_new                    false
% 11.10/1.99  --res_prop_simpl_given                  true
% 11.10/1.99  --res_passive_queue_type                priority_queues
% 11.10/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.10/1.99  --res_passive_queues_freq               [15;5]
% 11.10/1.99  --res_forward_subs                      full
% 11.10/1.99  --res_backward_subs                     full
% 11.10/1.99  --res_forward_subs_resolution           true
% 11.10/1.99  --res_backward_subs_resolution          true
% 11.10/1.99  --res_orphan_elimination                true
% 11.10/1.99  --res_time_limit                        2.
% 11.10/1.99  --res_out_proof                         true
% 11.10/1.99  
% 11.10/1.99  ------ Superposition Options
% 11.10/1.99  
% 11.10/1.99  --superposition_flag                    true
% 11.10/1.99  --sup_passive_queue_type                priority_queues
% 11.10/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.10/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.10/1.99  --demod_completeness_check              fast
% 11.10/1.99  --demod_use_ground                      true
% 11.10/1.99  --sup_to_prop_solver                    passive
% 11.10/1.99  --sup_prop_simpl_new                    true
% 11.10/1.99  --sup_prop_simpl_given                  true
% 11.10/1.99  --sup_fun_splitting                     false
% 11.10/1.99  --sup_smt_interval                      50000
% 11.10/1.99  
% 11.10/1.99  ------ Superposition Simplification Setup
% 11.10/1.99  
% 11.10/1.99  --sup_indices_passive                   []
% 11.10/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.10/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.10/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.10/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.10/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.10/1.99  --sup_full_bw                           [BwDemod]
% 11.10/1.99  --sup_immed_triv                        [TrivRules]
% 11.10/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.10/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.10/1.99  --sup_immed_bw_main                     []
% 11.10/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.10/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.10/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.10/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.10/1.99  
% 11.10/1.99  ------ Combination Options
% 11.10/1.99  
% 11.10/1.99  --comb_res_mult                         3
% 11.10/1.99  --comb_sup_mult                         2
% 11.10/1.99  --comb_inst_mult                        10
% 11.10/1.99  
% 11.10/1.99  ------ Debug Options
% 11.10/1.99  
% 11.10/1.99  --dbg_backtrace                         false
% 11.10/1.99  --dbg_dump_prop_clauses                 false
% 11.10/1.99  --dbg_dump_prop_clauses_file            -
% 11.10/1.99  --dbg_out_stat                          false
% 11.10/1.99  ------ Parsing...
% 11.10/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.10/1.99  
% 11.10/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.10/1.99  
% 11.10/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.10/1.99  
% 11.10/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.10/1.99  ------ Proving...
% 11.10/1.99  ------ Problem Properties 
% 11.10/1.99  
% 11.10/1.99  
% 11.10/1.99  clauses                                 34
% 11.10/1.99  conjectures                             11
% 11.10/1.99  EPR                                     7
% 11.10/1.99  Horn                                    30
% 11.10/1.99  unary                                   15
% 11.10/1.99  binary                                  3
% 11.10/1.99  lits                                    102
% 11.10/1.99  lits eq                                 27
% 11.10/1.99  fd_pure                                 0
% 11.10/1.99  fd_pseudo                               0
% 11.10/1.99  fd_cond                                 3
% 11.10/1.99  fd_pseudo_cond                          1
% 11.10/1.99  AC symbols                              0
% 11.10/1.99  
% 11.10/1.99  ------ Schedule dynamic 5 is on 
% 11.10/1.99  
% 11.10/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.10/1.99  
% 11.10/1.99  
% 11.10/1.99  ------ 
% 11.10/1.99  Current options:
% 11.10/1.99  ------ 
% 11.10/1.99  
% 11.10/1.99  ------ Input Options
% 11.10/1.99  
% 11.10/1.99  --out_options                           all
% 11.10/1.99  --tptp_safe_out                         true
% 11.10/1.99  --problem_path                          ""
% 11.10/1.99  --include_path                          ""
% 11.10/1.99  --clausifier                            res/vclausify_rel
% 11.10/1.99  --clausifier_options                    --mode clausify
% 11.10/1.99  --stdin                                 false
% 11.10/1.99  --stats_out                             all
% 11.10/1.99  
% 11.10/1.99  ------ General Options
% 11.10/1.99  
% 11.10/1.99  --fof                                   false
% 11.10/1.99  --time_out_real                         305.
% 11.10/1.99  --time_out_virtual                      -1.
% 11.10/1.99  --symbol_type_check                     false
% 11.10/1.99  --clausify_out                          false
% 11.10/1.99  --sig_cnt_out                           false
% 11.10/1.99  --trig_cnt_out                          false
% 11.10/1.99  --trig_cnt_out_tolerance                1.
% 11.10/1.99  --trig_cnt_out_sk_spl                   false
% 11.10/1.99  --abstr_cl_out                          false
% 11.10/1.99  
% 11.10/1.99  ------ Global Options
% 11.10/1.99  
% 11.10/1.99  --schedule                              default
% 11.10/1.99  --add_important_lit                     false
% 11.10/1.99  --prop_solver_per_cl                    1000
% 11.10/1.99  --min_unsat_core                        false
% 11.10/1.99  --soft_assumptions                      false
% 11.10/1.99  --soft_lemma_size                       3
% 11.10/1.99  --prop_impl_unit_size                   0
% 11.10/1.99  --prop_impl_unit                        []
% 11.10/1.99  --share_sel_clauses                     true
% 11.10/1.99  --reset_solvers                         false
% 11.10/1.99  --bc_imp_inh                            [conj_cone]
% 11.10/1.99  --conj_cone_tolerance                   3.
% 11.10/1.99  --extra_neg_conj                        none
% 11.10/1.99  --large_theory_mode                     true
% 11.10/1.99  --prolific_symb_bound                   200
% 11.10/1.99  --lt_threshold                          2000
% 11.10/1.99  --clause_weak_htbl                      true
% 11.10/1.99  --gc_record_bc_elim                     false
% 11.10/1.99  
% 11.10/1.99  ------ Preprocessing Options
% 11.10/1.99  
% 11.10/1.99  --preprocessing_flag                    true
% 11.10/1.99  --time_out_prep_mult                    0.1
% 11.10/1.99  --splitting_mode                        input
% 11.10/1.99  --splitting_grd                         true
% 11.10/1.99  --splitting_cvd                         false
% 11.10/1.99  --splitting_cvd_svl                     false
% 11.10/1.99  --splitting_nvd                         32
% 11.10/1.99  --sub_typing                            true
% 11.10/1.99  --prep_gs_sim                           true
% 11.10/1.99  --prep_unflatten                        true
% 11.10/1.99  --prep_res_sim                          true
% 11.10/1.99  --prep_upred                            true
% 11.10/1.99  --prep_sem_filter                       exhaustive
% 11.10/1.99  --prep_sem_filter_out                   false
% 11.10/1.99  --pred_elim                             true
% 11.10/1.99  --res_sim_input                         true
% 11.10/1.99  --eq_ax_congr_red                       true
% 11.10/1.99  --pure_diseq_elim                       true
% 11.10/1.99  --brand_transform                       false
% 11.10/1.99  --non_eq_to_eq                          false
% 11.10/1.99  --prep_def_merge                        true
% 11.10/1.99  --prep_def_merge_prop_impl              false
% 11.10/1.99  --prep_def_merge_mbd                    true
% 11.10/1.99  --prep_def_merge_tr_red                 false
% 11.10/1.99  --prep_def_merge_tr_cl                  false
% 11.10/1.99  --smt_preprocessing                     true
% 11.10/1.99  --smt_ac_axioms                         fast
% 11.10/1.99  --preprocessed_out                      false
% 11.10/1.99  --preprocessed_stats                    false
% 11.10/1.99  
% 11.10/1.99  ------ Abstraction refinement Options
% 11.10/1.99  
% 11.10/1.99  --abstr_ref                             []
% 11.10/1.99  --abstr_ref_prep                        false
% 11.10/1.99  --abstr_ref_until_sat                   false
% 11.10/1.99  --abstr_ref_sig_restrict                funpre
% 11.10/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.10/1.99  --abstr_ref_under                       []
% 11.10/1.99  
% 11.10/1.99  ------ SAT Options
% 11.10/1.99  
% 11.10/1.99  --sat_mode                              false
% 11.10/1.99  --sat_fm_restart_options                ""
% 11.10/1.99  --sat_gr_def                            false
% 11.10/1.99  --sat_epr_types                         true
% 11.10/1.99  --sat_non_cyclic_types                  false
% 11.10/1.99  --sat_finite_models                     false
% 11.10/1.99  --sat_fm_lemmas                         false
% 11.10/1.99  --sat_fm_prep                           false
% 11.10/1.99  --sat_fm_uc_incr                        true
% 11.10/1.99  --sat_out_model                         small
% 11.10/1.99  --sat_out_clauses                       false
% 11.10/1.99  
% 11.10/1.99  ------ QBF Options
% 11.10/1.99  
% 11.10/1.99  --qbf_mode                              false
% 11.10/1.99  --qbf_elim_univ                         false
% 11.10/1.99  --qbf_dom_inst                          none
% 11.10/1.99  --qbf_dom_pre_inst                      false
% 11.10/1.99  --qbf_sk_in                             false
% 11.10/1.99  --qbf_pred_elim                         true
% 11.10/1.99  --qbf_split                             512
% 11.10/1.99  
% 11.10/1.99  ------ BMC1 Options
% 11.10/1.99  
% 11.10/1.99  --bmc1_incremental                      false
% 11.10/1.99  --bmc1_axioms                           reachable_all
% 11.10/1.99  --bmc1_min_bound                        0
% 11.10/1.99  --bmc1_max_bound                        -1
% 11.10/1.99  --bmc1_max_bound_default                -1
% 11.10/1.99  --bmc1_symbol_reachability              true
% 11.10/1.99  --bmc1_property_lemmas                  false
% 11.10/1.99  --bmc1_k_induction                      false
% 11.10/1.99  --bmc1_non_equiv_states                 false
% 11.10/1.99  --bmc1_deadlock                         false
% 11.10/1.99  --bmc1_ucm                              false
% 11.10/1.99  --bmc1_add_unsat_core                   none
% 11.10/1.99  --bmc1_unsat_core_children              false
% 11.10/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.10/1.99  --bmc1_out_stat                         full
% 11.10/1.99  --bmc1_ground_init                      false
% 11.10/1.99  --bmc1_pre_inst_next_state              false
% 11.10/1.99  --bmc1_pre_inst_state                   false
% 11.10/1.99  --bmc1_pre_inst_reach_state             false
% 11.10/1.99  --bmc1_out_unsat_core                   false
% 11.10/1.99  --bmc1_aig_witness_out                  false
% 11.10/1.99  --bmc1_verbose                          false
% 11.10/1.99  --bmc1_dump_clauses_tptp                false
% 11.10/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.10/1.99  --bmc1_dump_file                        -
% 11.10/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.10/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.10/1.99  --bmc1_ucm_extend_mode                  1
% 11.10/1.99  --bmc1_ucm_init_mode                    2
% 11.10/1.99  --bmc1_ucm_cone_mode                    none
% 11.10/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.10/1.99  --bmc1_ucm_relax_model                  4
% 11.10/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.10/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.10/1.99  --bmc1_ucm_layered_model                none
% 11.10/1.99  --bmc1_ucm_max_lemma_size               10
% 11.10/1.99  
% 11.10/1.99  ------ AIG Options
% 11.10/1.99  
% 11.10/1.99  --aig_mode                              false
% 11.10/1.99  
% 11.10/1.99  ------ Instantiation Options
% 11.10/1.99  
% 11.10/1.99  --instantiation_flag                    true
% 11.10/1.99  --inst_sos_flag                         false
% 11.10/1.99  --inst_sos_phase                        true
% 11.10/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.10/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.10/1.99  --inst_lit_sel_side                     none
% 11.10/1.99  --inst_solver_per_active                1400
% 11.10/1.99  --inst_solver_calls_frac                1.
% 11.10/1.99  --inst_passive_queue_type               priority_queues
% 11.10/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.10/1.99  --inst_passive_queues_freq              [25;2]
% 11.10/1.99  --inst_dismatching                      true
% 11.10/1.99  --inst_eager_unprocessed_to_passive     true
% 11.10/1.99  --inst_prop_sim_given                   true
% 11.10/1.99  --inst_prop_sim_new                     false
% 11.10/1.99  --inst_subs_new                         false
% 11.10/1.99  --inst_eq_res_simp                      false
% 11.10/1.99  --inst_subs_given                       false
% 11.10/1.99  --inst_orphan_elimination               true
% 11.10/1.99  --inst_learning_loop_flag               true
% 11.10/1.99  --inst_learning_start                   3000
% 11.10/1.99  --inst_learning_factor                  2
% 11.10/1.99  --inst_start_prop_sim_after_learn       3
% 11.10/1.99  --inst_sel_renew                        solver
% 11.10/1.99  --inst_lit_activity_flag                true
% 11.10/1.99  --inst_restr_to_given                   false
% 11.10/1.99  --inst_activity_threshold               500
% 11.10/1.99  --inst_out_proof                        true
% 11.10/1.99  
% 11.10/1.99  ------ Resolution Options
% 11.10/1.99  
% 11.10/1.99  --resolution_flag                       false
% 11.10/1.99  --res_lit_sel                           adaptive
% 11.10/1.99  --res_lit_sel_side                      none
% 11.10/1.99  --res_ordering                          kbo
% 11.10/1.99  --res_to_prop_solver                    active
% 11.10/1.99  --res_prop_simpl_new                    false
% 11.10/1.99  --res_prop_simpl_given                  true
% 11.10/1.99  --res_passive_queue_type                priority_queues
% 11.10/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.10/1.99  --res_passive_queues_freq               [15;5]
% 11.10/1.99  --res_forward_subs                      full
% 11.10/1.99  --res_backward_subs                     full
% 11.10/1.99  --res_forward_subs_resolution           true
% 11.10/1.99  --res_backward_subs_resolution          true
% 11.10/1.99  --res_orphan_elimination                true
% 11.10/1.99  --res_time_limit                        2.
% 11.10/1.99  --res_out_proof                         true
% 11.10/1.99  
% 11.10/1.99  ------ Superposition Options
% 11.10/1.99  
% 11.10/1.99  --superposition_flag                    true
% 11.10/1.99  --sup_passive_queue_type                priority_queues
% 11.10/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.10/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.10/1.99  --demod_completeness_check              fast
% 11.10/1.99  --demod_use_ground                      true
% 11.10/1.99  --sup_to_prop_solver                    passive
% 11.10/1.99  --sup_prop_simpl_new                    true
% 11.10/1.99  --sup_prop_simpl_given                  true
% 11.10/1.99  --sup_fun_splitting                     false
% 11.10/1.99  --sup_smt_interval                      50000
% 11.10/1.99  
% 11.10/1.99  ------ Superposition Simplification Setup
% 11.10/1.99  
% 11.10/1.99  --sup_indices_passive                   []
% 11.10/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.10/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.10/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.10/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.10/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.10/1.99  --sup_full_bw                           [BwDemod]
% 11.10/1.99  --sup_immed_triv                        [TrivRules]
% 11.10/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.10/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.10/1.99  --sup_immed_bw_main                     []
% 11.10/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.10/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.10/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.10/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.10/1.99  
% 11.10/1.99  ------ Combination Options
% 11.10/1.99  
% 11.10/1.99  --comb_res_mult                         3
% 11.10/1.99  --comb_sup_mult                         2
% 11.10/1.99  --comb_inst_mult                        10
% 11.10/1.99  
% 11.10/1.99  ------ Debug Options
% 11.10/1.99  
% 11.10/1.99  --dbg_backtrace                         false
% 11.10/1.99  --dbg_dump_prop_clauses                 false
% 11.10/1.99  --dbg_dump_prop_clauses_file            -
% 11.10/1.99  --dbg_out_stat                          false
% 11.10/1.99  
% 11.10/1.99  
% 11.10/1.99  
% 11.10/1.99  
% 11.10/1.99  ------ Proving...
% 11.10/1.99  
% 11.10/1.99  
% 11.10/1.99  % SZS status Theorem for theBenchmark.p
% 11.10/1.99  
% 11.10/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.10/1.99  
% 11.10/1.99  fof(f16,conjecture,(
% 11.10/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f17,negated_conjecture,(
% 11.10/1.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.10/1.99    inference(negated_conjecture,[],[f16])).
% 11.10/1.99  
% 11.10/1.99  fof(f38,plain,(
% 11.10/1.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.10/1.99    inference(ennf_transformation,[],[f17])).
% 11.10/1.99  
% 11.10/1.99  fof(f39,plain,(
% 11.10/1.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.10/1.99    inference(flattening,[],[f38])).
% 11.10/1.99  
% 11.10/1.99  fof(f43,plain,(
% 11.10/1.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 11.10/1.99    introduced(choice_axiom,[])).
% 11.10/1.99  
% 11.10/1.99  fof(f42,plain,(
% 11.10/1.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 11.10/1.99    introduced(choice_axiom,[])).
% 11.10/1.99  
% 11.10/1.99  fof(f44,plain,(
% 11.10/1.99    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 11.10/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f43,f42])).
% 11.10/1.99  
% 11.10/1.99  fof(f71,plain,(
% 11.10/1.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.10/1.99    inference(cnf_transformation,[],[f44])).
% 11.10/1.99  
% 11.10/1.99  fof(f74,plain,(
% 11.10/1.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.10/1.99    inference(cnf_transformation,[],[f44])).
% 11.10/1.99  
% 11.10/1.99  fof(f13,axiom,(
% 11.10/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f34,plain,(
% 11.10/1.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.10/1.99    inference(ennf_transformation,[],[f13])).
% 11.10/1.99  
% 11.10/1.99  fof(f35,plain,(
% 11.10/1.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.10/1.99    inference(flattening,[],[f34])).
% 11.10/1.99  
% 11.10/1.99  fof(f66,plain,(
% 11.10/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.10/1.99    inference(cnf_transformation,[],[f35])).
% 11.10/1.99  
% 11.10/1.99  fof(f72,plain,(
% 11.10/1.99    v1_funct_1(sK3)),
% 11.10/1.99    inference(cnf_transformation,[],[f44])).
% 11.10/1.99  
% 11.10/1.99  fof(f69,plain,(
% 11.10/1.99    v1_funct_1(sK2)),
% 11.10/1.99    inference(cnf_transformation,[],[f44])).
% 11.10/1.99  
% 11.10/1.99  fof(f11,axiom,(
% 11.10/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f32,plain,(
% 11.10/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.10/1.99    inference(ennf_transformation,[],[f11])).
% 11.10/1.99  
% 11.10/1.99  fof(f33,plain,(
% 11.10/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.10/1.99    inference(flattening,[],[f32])).
% 11.10/1.99  
% 11.10/1.99  fof(f64,plain,(
% 11.10/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.10/1.99    inference(cnf_transformation,[],[f33])).
% 11.10/1.99  
% 11.10/1.99  fof(f9,axiom,(
% 11.10/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f28,plain,(
% 11.10/1.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.10/1.99    inference(ennf_transformation,[],[f9])).
% 11.10/1.99  
% 11.10/1.99  fof(f29,plain,(
% 11.10/1.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.10/1.99    inference(flattening,[],[f28])).
% 11.10/1.99  
% 11.10/1.99  fof(f40,plain,(
% 11.10/1.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.10/1.99    inference(nnf_transformation,[],[f29])).
% 11.10/1.99  
% 11.10/1.99  fof(f55,plain,(
% 11.10/1.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.10/1.99    inference(cnf_transformation,[],[f40])).
% 11.10/1.99  
% 11.10/1.99  fof(f76,plain,(
% 11.10/1.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 11.10/1.99    inference(cnf_transformation,[],[f44])).
% 11.10/1.99  
% 11.10/1.99  fof(f12,axiom,(
% 11.10/1.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f18,plain,(
% 11.10/1.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.10/1.99    inference(pure_predicate_removal,[],[f12])).
% 11.10/1.99  
% 11.10/1.99  fof(f65,plain,(
% 11.10/1.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.10/1.99    inference(cnf_transformation,[],[f18])).
% 11.10/1.99  
% 11.10/1.99  fof(f5,axiom,(
% 11.10/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f22,plain,(
% 11.10/1.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.10/1.99    inference(ennf_transformation,[],[f5])).
% 11.10/1.99  
% 11.10/1.99  fof(f23,plain,(
% 11.10/1.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.10/1.99    inference(flattening,[],[f22])).
% 11.10/1.99  
% 11.10/1.99  fof(f51,plain,(
% 11.10/1.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.10/1.99    inference(cnf_transformation,[],[f23])).
% 11.10/1.99  
% 11.10/1.99  fof(f14,axiom,(
% 11.10/1.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f67,plain,(
% 11.10/1.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.10/1.99    inference(cnf_transformation,[],[f14])).
% 11.10/1.99  
% 11.10/1.99  fof(f83,plain,(
% 11.10/1.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.10/1.99    inference(definition_unfolding,[],[f51,f67])).
% 11.10/1.99  
% 11.10/1.99  fof(f8,axiom,(
% 11.10/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f27,plain,(
% 11.10/1.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.10/1.99    inference(ennf_transformation,[],[f8])).
% 11.10/1.99  
% 11.10/1.99  fof(f54,plain,(
% 11.10/1.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.10/1.99    inference(cnf_transformation,[],[f27])).
% 11.10/1.99  
% 11.10/1.99  fof(f75,plain,(
% 11.10/1.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 11.10/1.99    inference(cnf_transformation,[],[f44])).
% 11.10/1.99  
% 11.10/1.99  fof(f15,axiom,(
% 11.10/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f36,plain,(
% 11.10/1.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.10/1.99    inference(ennf_transformation,[],[f15])).
% 11.10/1.99  
% 11.10/1.99  fof(f37,plain,(
% 11.10/1.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.10/1.99    inference(flattening,[],[f36])).
% 11.10/1.99  
% 11.10/1.99  fof(f68,plain,(
% 11.10/1.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.10/1.99    inference(cnf_transformation,[],[f37])).
% 11.10/1.99  
% 11.10/1.99  fof(f70,plain,(
% 11.10/1.99    v1_funct_2(sK2,sK0,sK1)),
% 11.10/1.99    inference(cnf_transformation,[],[f44])).
% 11.10/1.99  
% 11.10/1.99  fof(f73,plain,(
% 11.10/1.99    v1_funct_2(sK3,sK1,sK0)),
% 11.10/1.99    inference(cnf_transformation,[],[f44])).
% 11.10/1.99  
% 11.10/1.99  fof(f10,axiom,(
% 11.10/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f30,plain,(
% 11.10/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.10/1.99    inference(ennf_transformation,[],[f10])).
% 11.10/1.99  
% 11.10/1.99  fof(f31,plain,(
% 11.10/1.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.10/1.99    inference(flattening,[],[f30])).
% 11.10/1.99  
% 11.10/1.99  fof(f41,plain,(
% 11.10/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.10/1.99    inference(nnf_transformation,[],[f31])).
% 11.10/1.99  
% 11.10/1.99  fof(f57,plain,(
% 11.10/1.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.10/1.99    inference(cnf_transformation,[],[f41])).
% 11.10/1.99  
% 11.10/1.99  fof(f7,axiom,(
% 11.10/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f26,plain,(
% 11.10/1.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.10/1.99    inference(ennf_transformation,[],[f7])).
% 11.10/1.99  
% 11.10/1.99  fof(f53,plain,(
% 11.10/1.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.10/1.99    inference(cnf_transformation,[],[f26])).
% 11.10/1.99  
% 11.10/1.99  fof(f78,plain,(
% 11.10/1.99    k1_xboole_0 != sK0),
% 11.10/1.99    inference(cnf_transformation,[],[f44])).
% 11.10/1.99  
% 11.10/1.99  fof(f1,axiom,(
% 11.10/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f19,plain,(
% 11.10/1.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.10/1.99    inference(ennf_transformation,[],[f1])).
% 11.10/1.99  
% 11.10/1.99  fof(f45,plain,(
% 11.10/1.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.10/1.99    inference(cnf_transformation,[],[f19])).
% 11.10/1.99  
% 11.10/1.99  fof(f2,axiom,(
% 11.10/1.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f46,plain,(
% 11.10/1.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.10/1.99    inference(cnf_transformation,[],[f2])).
% 11.10/1.99  
% 11.10/1.99  fof(f3,axiom,(
% 11.10/1.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f48,plain,(
% 11.10/1.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.10/1.99    inference(cnf_transformation,[],[f3])).
% 11.10/1.99  
% 11.10/1.99  fof(f81,plain,(
% 11.10/1.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 11.10/1.99    inference(definition_unfolding,[],[f48,f67])).
% 11.10/1.99  
% 11.10/1.99  fof(f4,axiom,(
% 11.10/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f20,plain,(
% 11.10/1.99    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.10/1.99    inference(ennf_transformation,[],[f4])).
% 11.10/1.99  
% 11.10/1.99  fof(f21,plain,(
% 11.10/1.99    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.10/1.99    inference(flattening,[],[f20])).
% 11.10/1.99  
% 11.10/1.99  fof(f50,plain,(
% 11.10/1.99    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.10/1.99    inference(cnf_transformation,[],[f21])).
% 11.10/1.99  
% 11.10/1.99  fof(f6,axiom,(
% 11.10/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 11.10/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/1.99  
% 11.10/1.99  fof(f24,plain,(
% 11.10/1.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.10/1.99    inference(ennf_transformation,[],[f6])).
% 11.10/1.99  
% 11.10/1.99  fof(f25,plain,(
% 11.10/1.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.10/1.99    inference(flattening,[],[f24])).
% 11.10/1.99  
% 11.10/1.99  fof(f52,plain,(
% 11.10/1.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.10/1.99    inference(cnf_transformation,[],[f25])).
% 11.10/1.99  
% 11.10/1.99  fof(f80,plain,(
% 11.10/1.99    k2_funct_1(sK2) != sK3),
% 11.10/1.99    inference(cnf_transformation,[],[f44])).
% 11.10/1.99  
% 11.10/1.99  cnf(c_32,negated_conjecture,
% 11.10/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.10/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1175,plain,
% 11.10/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_29,negated_conjecture,
% 11.10/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.10/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1178,plain,
% 11.10/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_21,plain,
% 11.10/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.10/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.10/1.99      | ~ v1_funct_1(X0)
% 11.10/1.99      | ~ v1_funct_1(X3)
% 11.10/1.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.10/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1180,plain,
% 11.10/1.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.10/1.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.10/1.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.10/1.99      | v1_funct_1(X4) != iProver_top
% 11.10/1.99      | v1_funct_1(X5) != iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2556,plain,
% 11.10/1.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.10/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.10/1.99      | v1_funct_1(X2) != iProver_top
% 11.10/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.10/1.99      inference(superposition,[status(thm)],[c_1178,c_1180]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_31,negated_conjecture,
% 11.10/1.99      ( v1_funct_1(sK3) ),
% 11.10/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_38,plain,
% 11.10/1.99      ( v1_funct_1(sK3) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2856,plain,
% 11.10/1.99      ( v1_funct_1(X2) != iProver_top
% 11.10/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.10/1.99      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 11.10/1.99      inference(global_propositional_subsumption,
% 11.10/1.99                [status(thm)],
% 11.10/1.99                [c_2556,c_38]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2857,plain,
% 11.10/1.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.10/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.10/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.10/1.99      inference(renaming,[status(thm)],[c_2856]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2867,plain,
% 11.10/1.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 11.10/1.99      | v1_funct_1(sK2) != iProver_top ),
% 11.10/1.99      inference(superposition,[status(thm)],[c_1175,c_2857]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_34,negated_conjecture,
% 11.10/1.99      ( v1_funct_1(sK2) ),
% 11.10/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1670,plain,
% 11.10/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.10/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 11.10/1.99      | ~ v1_funct_1(X0)
% 11.10/1.99      | ~ v1_funct_1(sK3)
% 11.10/1.99      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 11.10/1.99      inference(instantiation,[status(thm)],[c_21]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1920,plain,
% 11.10/1.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.10/1.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.10/1.99      | ~ v1_funct_1(sK3)
% 11.10/1.99      | ~ v1_funct_1(sK2)
% 11.10/1.99      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.10/1.99      inference(instantiation,[status(thm)],[c_1670]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2165,plain,
% 11.10/1.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.10/1.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.10/1.99      | ~ v1_funct_1(sK3)
% 11.10/1.99      | ~ v1_funct_1(sK2)
% 11.10/1.99      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.10/1.99      inference(instantiation,[status(thm)],[c_1920]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2308,plain,
% 11.10/1.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.10/1.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.10/1.99      | ~ v1_funct_1(sK3)
% 11.10/1.99      | ~ v1_funct_1(sK2)
% 11.10/1.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.10/1.99      inference(instantiation,[status(thm)],[c_2165]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_3037,plain,
% 11.10/1.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.10/1.99      inference(global_propositional_subsumption,
% 11.10/1.99                [status(thm)],
% 11.10/1.99                [c_2867,c_34,c_32,c_31,c_29,c_2308]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_18,plain,
% 11.10/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.10/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.10/1.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.10/1.99      | ~ v1_funct_1(X0)
% 11.10/1.99      | ~ v1_funct_1(X3) ),
% 11.10/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1183,plain,
% 11.10/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.10/1.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 11.10/1.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 11.10/1.99      | v1_funct_1(X3) != iProver_top
% 11.10/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_4074,plain,
% 11.10/1.99      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 11.10/1.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.10/1.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.10/1.99      | v1_funct_1(sK3) != iProver_top
% 11.10/1.99      | v1_funct_1(sK2) != iProver_top ),
% 11.10/1.99      inference(superposition,[status(thm)],[c_3037,c_1183]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_35,plain,
% 11.10/1.99      ( v1_funct_1(sK2) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_37,plain,
% 11.10/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_40,plain,
% 11.10/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_5410,plain,
% 11.10/1.99      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.10/1.99      inference(global_propositional_subsumption,
% 11.10/1.99                [status(thm)],
% 11.10/1.99                [c_4074,c_35,c_37,c_38,c_40]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_11,plain,
% 11.10/1.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.10/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.10/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.10/1.99      | X3 = X2 ),
% 11.10/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_27,negated_conjecture,
% 11.10/1.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 11.10/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_381,plain,
% 11.10/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.10/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.10/1.99      | X3 = X0
% 11.10/1.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 11.10/1.99      | k6_partfun1(sK0) != X3
% 11.10/1.99      | sK0 != X2
% 11.10/1.99      | sK0 != X1 ),
% 11.10/1.99      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_382,plain,
% 11.10/1.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.10/1.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.10/1.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.10/1.99      inference(unflattening,[status(thm)],[c_381]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_20,plain,
% 11.10/1.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.10/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_390,plain,
% 11.10/1.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.10/1.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.10/1.99      inference(forward_subsumption_resolution,
% 11.10/1.99                [status(thm)],
% 11.10/1.99                [c_382,c_20]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1171,plain,
% 11.10/1.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.10/1.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_3040,plain,
% 11.10/1.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 11.10/1.99      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.10/1.99      inference(demodulation,[status(thm)],[c_3037,c_1171]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_5422,plain,
% 11.10/1.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 11.10/1.99      inference(superposition,[status(thm)],[c_5410,c_3040]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_6,plain,
% 11.10/1.99      ( ~ v1_funct_1(X0)
% 11.10/1.99      | ~ v1_funct_1(X1)
% 11.10/1.99      | ~ v2_funct_1(X1)
% 11.10/1.99      | ~ v1_relat_1(X1)
% 11.10/1.99      | ~ v1_relat_1(X0)
% 11.10/1.99      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 11.10/1.99      | k2_funct_1(X1) = X0
% 11.10/1.99      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 11.10/1.99      inference(cnf_transformation,[],[f83]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1193,plain,
% 11.10/1.99      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 11.10/1.99      | k2_funct_1(X1) = X0
% 11.10/1.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 11.10/1.99      | v1_funct_1(X0) != iProver_top
% 11.10/1.99      | v1_funct_1(X1) != iProver_top
% 11.10/1.99      | v2_funct_1(X1) != iProver_top
% 11.10/1.99      | v1_relat_1(X0) != iProver_top
% 11.10/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_33690,plain,
% 11.10/1.99      ( k2_funct_1(sK3) = sK2
% 11.10/1.99      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 11.10/1.99      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 11.10/1.99      | v1_funct_1(sK3) != iProver_top
% 11.10/1.99      | v1_funct_1(sK2) != iProver_top
% 11.10/1.99      | v2_funct_1(sK3) != iProver_top
% 11.10/1.99      | v1_relat_1(sK3) != iProver_top
% 11.10/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.10/1.99      inference(superposition,[status(thm)],[c_5422,c_1193]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_9,plain,
% 11.10/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.10/1.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.10/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1190,plain,
% 11.10/1.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.10/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2065,plain,
% 11.10/1.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 11.10/1.99      inference(superposition,[status(thm)],[c_1175,c_1190]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_28,negated_conjecture,
% 11.10/1.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 11.10/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2067,plain,
% 11.10/1.99      ( k2_relat_1(sK2) = sK1 ),
% 11.10/1.99      inference(light_normalisation,[status(thm)],[c_2065,c_28]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2064,plain,
% 11.10/1.99      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 11.10/1.99      inference(superposition,[status(thm)],[c_1178,c_1190]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_22,plain,
% 11.10/1.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.10/1.99      | ~ v1_funct_2(X3,X1,X0)
% 11.10/1.99      | ~ v1_funct_2(X2,X0,X1)
% 11.10/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.10/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.10/1.99      | ~ v1_funct_1(X2)
% 11.10/1.99      | ~ v1_funct_1(X3)
% 11.10/1.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 11.10/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_394,plain,
% 11.10/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.10/1.99      | ~ v1_funct_2(X3,X2,X1)
% 11.10/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.10/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.10/1.99      | ~ v1_funct_1(X0)
% 11.10/1.99      | ~ v1_funct_1(X3)
% 11.10/1.99      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.10/1.99      | k2_relset_1(X1,X2,X0) = X2
% 11.10/1.99      | k6_partfun1(X2) != k6_partfun1(sK0)
% 11.10/1.99      | sK0 != X2 ),
% 11.10/1.99      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_395,plain,
% 11.10/1.99      ( ~ v1_funct_2(X0,X1,sK0)
% 11.10/1.99      | ~ v1_funct_2(X2,sK0,X1)
% 11.10/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 11.10/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 11.10/1.99      | ~ v1_funct_1(X0)
% 11.10/1.99      | ~ v1_funct_1(X2)
% 11.10/1.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.10/1.99      | k2_relset_1(X1,sK0,X0) = sK0
% 11.10/1.99      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 11.10/1.99      inference(unflattening,[status(thm)],[c_394]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_479,plain,
% 11.10/1.99      ( ~ v1_funct_2(X0,X1,sK0)
% 11.10/1.99      | ~ v1_funct_2(X2,sK0,X1)
% 11.10/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 11.10/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 11.10/1.99      | ~ v1_funct_1(X0)
% 11.10/1.99      | ~ v1_funct_1(X2)
% 11.10/1.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.10/1.99      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 11.10/1.99      inference(equality_resolution_simp,[status(thm)],[c_395]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1170,plain,
% 11.10/1.99      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.10/1.99      | k2_relset_1(X0,sK0,X2) = sK0
% 11.10/1.99      | v1_funct_2(X2,X0,sK0) != iProver_top
% 11.10/1.99      | v1_funct_2(X1,sK0,X0) != iProver_top
% 11.10/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 11.10/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 11.10/1.99      | v1_funct_1(X1) != iProver_top
% 11.10/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1702,plain,
% 11.10/1.99      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 11.10/1.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.10/1.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.10/1.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.10/1.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.10/1.99      | v1_funct_1(sK3) != iProver_top
% 11.10/1.99      | v1_funct_1(sK2) != iProver_top ),
% 11.10/1.99      inference(equality_resolution,[status(thm)],[c_1170]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_33,negated_conjecture,
% 11.10/1.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 11.10/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_36,plain,
% 11.10/1.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_30,negated_conjecture,
% 11.10/1.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 11.10/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_39,plain,
% 11.10/1.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1966,plain,
% 11.10/1.99      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 11.10/1.99      inference(global_propositional_subsumption,
% 11.10/1.99                [status(thm)],
% 11.10/1.99                [c_1702,c_35,c_36,c_37,c_38,c_39,c_40]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2070,plain,
% 11.10/1.99      ( k2_relat_1(sK3) = sK0 ),
% 11.10/1.99      inference(light_normalisation,[status(thm)],[c_2064,c_1966]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_17,plain,
% 11.10/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.10/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.10/1.99      | k1_relset_1(X1,X2,X0) = X1
% 11.10/1.99      | k1_xboole_0 = X2 ),
% 11.10/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1184,plain,
% 11.10/1.99      ( k1_relset_1(X0,X1,X2) = X0
% 11.10/1.99      | k1_xboole_0 = X1
% 11.10/1.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.10/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2829,plain,
% 11.10/1.99      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 11.10/1.99      | sK0 = k1_xboole_0
% 11.10/1.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 11.10/1.99      inference(superposition,[status(thm)],[c_1178,c_1184]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_8,plain,
% 11.10/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.10/1.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.10/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1191,plain,
% 11.10/1.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.10/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2139,plain,
% 11.10/1.99      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 11.10/1.99      inference(superposition,[status(thm)],[c_1178,c_1191]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2841,plain,
% 11.10/1.99      ( k1_relat_1(sK3) = sK1
% 11.10/1.99      | sK0 = k1_xboole_0
% 11.10/1.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 11.10/1.99      inference(demodulation,[status(thm)],[c_2829,c_2139]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_25,negated_conjecture,
% 11.10/1.99      ( k1_xboole_0 != sK0 ),
% 11.10/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_651,plain,( X0 = X0 ),theory(equality) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_678,plain,
% 11.10/1.99      ( k1_xboole_0 = k1_xboole_0 ),
% 11.10/1.99      inference(instantiation,[status(thm)],[c_651]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_652,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1533,plain,
% 11.10/1.99      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 11.10/1.99      inference(instantiation,[status(thm)],[c_652]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1534,plain,
% 11.10/1.99      ( sK0 != k1_xboole_0
% 11.10/1.99      | k1_xboole_0 = sK0
% 11.10/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.10/1.99      inference(instantiation,[status(thm)],[c_1533]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_9589,plain,
% 11.10/1.99      ( k1_relat_1(sK3) = sK1 ),
% 11.10/1.99      inference(global_propositional_subsumption,
% 11.10/1.99                [status(thm)],
% 11.10/1.99                [c_2841,c_39,c_25,c_678,c_1534]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_33691,plain,
% 11.10/1.99      ( k2_funct_1(sK3) = sK2
% 11.10/1.99      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 11.10/1.99      | sK1 != sK1
% 11.10/1.99      | v1_funct_1(sK3) != iProver_top
% 11.10/1.99      | v1_funct_1(sK2) != iProver_top
% 11.10/1.99      | v2_funct_1(sK3) != iProver_top
% 11.10/1.99      | v1_relat_1(sK3) != iProver_top
% 11.10/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.10/1.99      inference(light_normalisation,
% 11.10/1.99                [status(thm)],
% 11.10/1.99                [c_33690,c_2067,c_2070,c_9589]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_33692,plain,
% 11.10/1.99      ( k2_funct_1(sK3) = sK2
% 11.10/1.99      | v1_funct_1(sK3) != iProver_top
% 11.10/1.99      | v1_funct_1(sK2) != iProver_top
% 11.10/1.99      | v2_funct_1(sK3) != iProver_top
% 11.10/1.99      | v1_relat_1(sK3) != iProver_top
% 11.10/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.10/1.99      inference(equality_resolution_simp,[status(thm)],[c_33691]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_0,plain,
% 11.10/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.10/1.99      | ~ v1_relat_1(X1)
% 11.10/1.99      | v1_relat_1(X0) ),
% 11.10/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1487,plain,
% 11.10/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.10/1.99      | v1_relat_1(X0)
% 11.10/1.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 11.10/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2009,plain,
% 11.10/1.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.10/1.99      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 11.10/1.99      | v1_relat_1(sK3) ),
% 11.10/1.99      inference(instantiation,[status(thm)],[c_1487]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2010,plain,
% 11.10/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.10/1.99      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 11.10/1.99      | v1_relat_1(sK3) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_2009]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2012,plain,
% 11.10/1.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.10/1.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 11.10/1.99      | v1_relat_1(sK2) ),
% 11.10/1.99      inference(instantiation,[status(thm)],[c_1487]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2013,plain,
% 11.10/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.10/1.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 11.10/1.99      | v1_relat_1(sK2) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_2012]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1,plain,
% 11.10/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.10/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2082,plain,
% 11.10/1.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 11.10/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2083,plain,
% 11.10/1.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_2082]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2101,plain,
% 11.10/1.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 11.10/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2102,plain,
% 11.10/1.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_2101]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2,plain,
% 11.10/1.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 11.10/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_19659,plain,
% 11.10/1.99      ( v2_funct_1(k6_partfun1(sK0)) ),
% 11.10/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_19660,plain,
% 11.10/1.99      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_19659]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_4,plain,
% 11.10/1.99      ( ~ v1_funct_1(X0)
% 11.10/1.99      | ~ v1_funct_1(X1)
% 11.10/1.99      | v2_funct_1(X1)
% 11.10/1.99      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 11.10/1.99      | ~ v1_relat_1(X1)
% 11.10/1.99      | ~ v1_relat_1(X0)
% 11.10/1.99      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 11.10/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1195,plain,
% 11.10/1.99      ( k1_relat_1(X0) != k2_relat_1(X1)
% 11.10/1.99      | v1_funct_1(X1) != iProver_top
% 11.10/1.99      | v1_funct_1(X0) != iProver_top
% 11.10/1.99      | v2_funct_1(X0) = iProver_top
% 11.10/1.99      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 11.10/1.99      | v1_relat_1(X1) != iProver_top
% 11.10/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_9593,plain,
% 11.10/1.99      ( k2_relat_1(X0) != sK1
% 11.10/1.99      | v1_funct_1(X0) != iProver_top
% 11.10/1.99      | v1_funct_1(sK3) != iProver_top
% 11.10/1.99      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 11.10/1.99      | v2_funct_1(sK3) = iProver_top
% 11.10/1.99      | v1_relat_1(X0) != iProver_top
% 11.10/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.10/1.99      inference(superposition,[status(thm)],[c_9589,c_1195]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_22652,plain,
% 11.10/1.99      ( v1_relat_1(X0) != iProver_top
% 11.10/1.99      | v2_funct_1(sK3) = iProver_top
% 11.10/1.99      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 11.10/1.99      | k2_relat_1(X0) != sK1
% 11.10/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.10/1.99      inference(global_propositional_subsumption,
% 11.10/1.99                [status(thm)],
% 11.10/1.99                [c_9593,c_38,c_40,c_2010,c_2083]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_22653,plain,
% 11.10/1.99      ( k2_relat_1(X0) != sK1
% 11.10/1.99      | v1_funct_1(X0) != iProver_top
% 11.10/1.99      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 11.10/1.99      | v2_funct_1(sK3) = iProver_top
% 11.10/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.10/1.99      inference(renaming,[status(thm)],[c_22652]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_22664,plain,
% 11.10/1.99      ( v1_funct_1(sK2) != iProver_top
% 11.10/1.99      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 11.10/1.99      | v2_funct_1(sK3) = iProver_top
% 11.10/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.10/1.99      inference(superposition,[status(thm)],[c_2067,c_22653]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_22736,plain,
% 11.10/1.99      ( v2_funct_1(sK3) = iProver_top
% 11.10/1.99      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
% 11.10/1.99      inference(global_propositional_subsumption,
% 11.10/1.99                [status(thm)],
% 11.10/1.99                [c_22664,c_35,c_37,c_2013,c_2102]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_22737,plain,
% 11.10/1.99      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 11.10/1.99      | v2_funct_1(sK3) = iProver_top ),
% 11.10/1.99      inference(renaming,[status(thm)],[c_22736]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_33481,plain,
% 11.10/1.99      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 11.10/1.99      | v2_funct_1(sK3) = iProver_top ),
% 11.10/1.99      inference(demodulation,[status(thm)],[c_5422,c_22737]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_34731,plain,
% 11.10/1.99      ( k2_funct_1(sK3) = sK2 ),
% 11.10/1.99      inference(global_propositional_subsumption,
% 11.10/1.99                [status(thm)],
% 11.10/1.99                [c_33692,c_35,c_37,c_38,c_40,c_2010,c_2013,c_2083,c_2102,
% 11.10/1.99                 c_19660,c_33481]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_34434,plain,
% 11.10/1.99      ( v2_funct_1(sK3) = iProver_top ),
% 11.10/1.99      inference(global_propositional_subsumption,
% 11.10/1.99                [status(thm)],
% 11.10/1.99                [c_33481,c_19660]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1176,plain,
% 11.10/1.99      ( v1_funct_1(sK3) = iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_7,plain,
% 11.10/1.99      ( ~ v1_funct_1(X0)
% 11.10/1.99      | ~ v2_funct_1(X0)
% 11.10/1.99      | ~ v1_relat_1(X0)
% 11.10/1.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 11.10/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_1192,plain,
% 11.10/1.99      ( k2_funct_1(k2_funct_1(X0)) = X0
% 11.10/1.99      | v1_funct_1(X0) != iProver_top
% 11.10/1.99      | v2_funct_1(X0) != iProver_top
% 11.10/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.10/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2216,plain,
% 11.10/1.99      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 11.10/1.99      | v2_funct_1(sK3) != iProver_top
% 11.10/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.10/1.99      inference(superposition,[status(thm)],[c_1176,c_1192]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2366,plain,
% 11.10/1.99      ( v2_funct_1(sK3) != iProver_top
% 11.10/1.99      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 11.10/1.99      inference(global_propositional_subsumption,
% 11.10/1.99                [status(thm)],
% 11.10/1.99                [c_2216,c_40,c_2010,c_2083]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_2367,plain,
% 11.10/1.99      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 11.10/1.99      | v2_funct_1(sK3) != iProver_top ),
% 11.10/1.99      inference(renaming,[status(thm)],[c_2366]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_34439,plain,
% 11.10/1.99      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 11.10/1.99      inference(superposition,[status(thm)],[c_34434,c_2367]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_34734,plain,
% 11.10/1.99      ( k2_funct_1(sK2) = sK3 ),
% 11.10/1.99      inference(demodulation,[status(thm)],[c_34731,c_34439]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(c_23,negated_conjecture,
% 11.10/1.99      ( k2_funct_1(sK2) != sK3 ),
% 11.10/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.10/1.99  
% 11.10/1.99  cnf(contradiction,plain,
% 11.10/1.99      ( $false ),
% 11.10/1.99      inference(minisat,[status(thm)],[c_34734,c_23]) ).
% 11.10/1.99  
% 11.10/1.99  
% 11.10/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.10/1.99  
% 11.10/1.99  ------                               Statistics
% 11.10/1.99  
% 11.10/1.99  ------ General
% 11.10/1.99  
% 11.10/1.99  abstr_ref_over_cycles:                  0
% 11.10/1.99  abstr_ref_under_cycles:                 0
% 11.10/1.99  gc_basic_clause_elim:                   0
% 11.10/1.99  forced_gc_time:                         0
% 11.10/1.99  parsing_time:                           0.012
% 11.10/1.99  unif_index_cands_time:                  0.
% 11.10/1.99  unif_index_add_time:                    0.
% 11.10/1.99  orderings_time:                         0.
% 11.10/1.99  out_proof_time:                         0.016
% 11.10/1.99  total_time:                             1.049
% 11.10/1.99  num_of_symbols:                         52
% 11.10/1.99  num_of_terms:                           34196
% 11.10/1.99  
% 11.10/1.99  ------ Preprocessing
% 11.10/1.99  
% 11.10/1.99  num_of_splits:                          0
% 11.10/1.99  num_of_split_atoms:                     0
% 11.10/1.99  num_of_reused_defs:                     0
% 11.10/1.99  num_eq_ax_congr_red:                    18
% 11.10/1.99  num_of_sem_filtered_clauses:            1
% 11.10/1.99  num_of_subtypes:                        0
% 11.10/1.99  monotx_restored_types:                  0
% 11.10/1.99  sat_num_of_epr_types:                   0
% 11.10/1.99  sat_num_of_non_cyclic_types:            0
% 11.10/1.99  sat_guarded_non_collapsed_types:        0
% 11.10/1.99  num_pure_diseq_elim:                    0
% 11.10/1.99  simp_replaced_by:                       0
% 11.10/1.99  res_preprocessed:                       166
% 11.10/1.99  prep_upred:                             0
% 11.10/1.99  prep_unflattend:                        12
% 11.10/1.99  smt_new_axioms:                         0
% 11.10/1.99  pred_elim_cands:                        5
% 11.10/1.99  pred_elim:                              1
% 11.10/1.99  pred_elim_cl:                           1
% 11.10/1.99  pred_elim_cycles:                       3
% 11.10/1.99  merged_defs:                            0
% 11.10/1.99  merged_defs_ncl:                        0
% 11.10/1.99  bin_hyper_res:                          0
% 11.10/1.99  prep_cycles:                            4
% 11.10/1.99  pred_elim_time:                         0.015
% 11.10/1.99  splitting_time:                         0.
% 11.10/1.99  sem_filter_time:                        0.
% 11.10/1.99  monotx_time:                            0.001
% 11.10/1.99  subtype_inf_time:                       0.
% 11.10/1.99  
% 11.10/1.99  ------ Problem properties
% 11.10/1.99  
% 11.10/1.99  clauses:                                34
% 11.10/1.99  conjectures:                            11
% 11.10/1.99  epr:                                    7
% 11.10/1.99  horn:                                   30
% 11.10/1.99  ground:                                 12
% 11.10/1.99  unary:                                  15
% 11.10/1.99  binary:                                 3
% 11.10/1.99  lits:                                   102
% 11.10/1.99  lits_eq:                                27
% 11.10/1.99  fd_pure:                                0
% 11.10/1.99  fd_pseudo:                              0
% 11.10/1.99  fd_cond:                                3
% 11.10/1.99  fd_pseudo_cond:                         1
% 11.10/1.99  ac_symbols:                             0
% 11.10/1.99  
% 11.10/1.99  ------ Propositional Solver
% 11.10/1.99  
% 11.10/1.99  prop_solver_calls:                      32
% 11.10/1.99  prop_fast_solver_calls:                 2506
% 11.10/1.99  smt_solver_calls:                       0
% 11.10/1.99  smt_fast_solver_calls:                  0
% 11.10/1.99  prop_num_of_clauses:                    11686
% 11.10/1.99  prop_preprocess_simplified:             16459
% 11.10/1.99  prop_fo_subsumed:                       386
% 11.10/1.99  prop_solver_time:                       0.
% 11.10/1.99  smt_solver_time:                        0.
% 11.10/1.99  smt_fast_solver_time:                   0.
% 11.10/1.99  prop_fast_solver_time:                  0.
% 11.10/1.99  prop_unsat_core_time:                   0.001
% 11.10/1.99  
% 11.10/1.99  ------ QBF
% 11.10/1.99  
% 11.10/1.99  qbf_q_res:                              0
% 11.10/1.99  qbf_num_tautologies:                    0
% 11.10/1.99  qbf_prep_cycles:                        0
% 11.10/1.99  
% 11.10/1.99  ------ BMC1
% 11.10/1.99  
% 11.10/1.99  bmc1_current_bound:                     -1
% 11.10/1.99  bmc1_last_solved_bound:                 -1
% 11.10/1.99  bmc1_unsat_core_size:                   -1
% 11.10/1.99  bmc1_unsat_core_parents_size:           -1
% 11.10/1.99  bmc1_merge_next_fun:                    0
% 11.10/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.10/1.99  
% 11.10/1.99  ------ Instantiation
% 11.10/1.99  
% 11.10/1.99  inst_num_of_clauses:                    3082
% 11.10/1.99  inst_num_in_passive:                    1115
% 11.10/1.99  inst_num_in_active:                     1735
% 11.10/1.99  inst_num_in_unprocessed:                235
% 11.10/1.99  inst_num_of_loops:                      1850
% 11.10/1.99  inst_num_of_learning_restarts:          0
% 11.10/1.99  inst_num_moves_active_passive:          110
% 11.10/1.99  inst_lit_activity:                      0
% 11.10/1.99  inst_lit_activity_moves:                1
% 11.10/1.99  inst_num_tautologies:                   0
% 11.10/1.99  inst_num_prop_implied:                  0
% 11.10/1.99  inst_num_existing_simplified:           0
% 11.10/1.99  inst_num_eq_res_simplified:             0
% 11.10/1.99  inst_num_child_elim:                    0
% 11.10/1.99  inst_num_of_dismatching_blockings:      742
% 11.10/1.99  inst_num_of_non_proper_insts:           2651
% 11.10/1.99  inst_num_of_duplicates:                 0
% 11.10/1.99  inst_inst_num_from_inst_to_res:         0
% 11.10/1.99  inst_dismatching_checking_time:         0.
% 11.10/1.99  
% 11.10/1.99  ------ Resolution
% 11.10/1.99  
% 11.10/1.99  res_num_of_clauses:                     0
% 11.10/1.99  res_num_in_passive:                     0
% 11.10/1.99  res_num_in_active:                      0
% 11.10/1.99  res_num_of_loops:                       170
% 11.10/1.99  res_forward_subset_subsumed:            307
% 11.10/1.99  res_backward_subset_subsumed:           8
% 11.10/1.99  res_forward_subsumed:                   0
% 11.10/1.99  res_backward_subsumed:                  0
% 11.10/1.99  res_forward_subsumption_resolution:     2
% 11.10/1.99  res_backward_subsumption_resolution:    0
% 11.10/1.99  res_clause_to_clause_subsumption:       2770
% 11.10/1.99  res_orphan_elimination:                 0
% 11.10/1.99  res_tautology_del:                      125
% 11.10/1.99  res_num_eq_res_simplified:              1
% 11.10/1.99  res_num_sel_changes:                    0
% 11.10/1.99  res_moves_from_active_to_pass:          0
% 11.10/1.99  
% 11.10/1.99  ------ Superposition
% 11.10/1.99  
% 11.10/1.99  sup_time_total:                         0.
% 11.10/1.99  sup_time_generating:                    0.
% 11.10/1.99  sup_time_sim_full:                      0.
% 11.10/1.99  sup_time_sim_immed:                     0.
% 11.10/1.99  
% 11.10/1.99  sup_num_of_clauses:                     1269
% 11.10/1.99  sup_num_in_active:                      301
% 11.10/1.99  sup_num_in_passive:                     968
% 11.10/1.99  sup_num_of_loops:                       368
% 11.10/1.99  sup_fw_superposition:                   426
% 11.10/1.99  sup_bw_superposition:                   931
% 11.10/1.99  sup_immediate_simplified:               531
% 11.10/1.99  sup_given_eliminated:                   1
% 11.10/1.99  comparisons_done:                       0
% 11.10/1.99  comparisons_avoided:                    1
% 11.10/1.99  
% 11.10/1.99  ------ Simplifications
% 11.10/1.99  
% 11.10/1.99  
% 11.10/1.99  sim_fw_subset_subsumed:                 66
% 11.10/1.99  sim_bw_subset_subsumed:                 20
% 11.10/1.99  sim_fw_subsumed:                        10
% 11.10/1.99  sim_bw_subsumed:                        0
% 11.10/1.99  sim_fw_subsumption_res:                 8
% 11.10/1.99  sim_bw_subsumption_res:                 66
% 11.10/1.99  sim_tautology_del:                      0
% 11.10/1.99  sim_eq_tautology_del:                   25
% 11.10/1.99  sim_eq_res_simp:                        1
% 11.10/1.99  sim_fw_demodulated:                     33
% 11.10/1.99  sim_bw_demodulated:                     65
% 11.10/1.99  sim_light_normalised:                   440
% 11.10/1.99  sim_joinable_taut:                      0
% 11.10/1.99  sim_joinable_simp:                      0
% 11.10/1.99  sim_ac_normalised:                      0
% 11.10/1.99  sim_smt_subsumption:                    0
% 11.10/1.99  
%------------------------------------------------------------------------------
