%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:01 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 574 expanded)
%              Number of clauses        :  111 ( 193 expanded)
%              Number of leaves         :   20 ( 123 expanded)
%              Depth                    :   18
%              Number of atoms          :  571 (3484 expanded)
%              Number of equality atoms :  239 (1360 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f20,plain,(
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
    inference(pure_predicate_removal,[],[f19])).

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
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f46,f45])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f84,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f88,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f60,f70,f70])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f54,f70])).

fof(f55,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f80,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_506,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_991,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_984,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_1524,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_984])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_504,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_993,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_1525,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_984])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_503,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_994,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_525,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | v1_relat_1(k2_funct_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_977,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(k2_funct_1(X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_528,plain,
    ( ~ v1_relat_1(X0_49)
    | ~ v1_relat_1(X1_49)
    | ~ v1_relat_1(X2_49)
    | k5_relat_1(k5_relat_1(X2_49,X0_49),X1_49) = k5_relat_1(X2_49,k5_relat_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_974,plain,
    ( k5_relat_1(k5_relat_1(X0_49,X1_49),X2_49) = k5_relat_1(X0_49,k5_relat_1(X1_49,X2_49))
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X2_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_3119,plain,
    ( k5_relat_1(k2_funct_1(X0_49),k5_relat_1(X1_49,X2_49)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_49),X1_49),X2_49)
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X2_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_977,c_974])).

cnf(c_6561,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49))
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_994,c_3119])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1192,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_1193,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1192])).

cnf(c_6924,plain,
    ( v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6561,c_33,c_1193])).

cnf(c_6925,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49))
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_6924])).

cnf(c_6933,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_49)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_49)
    | v1_relat_1(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_6925])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_508,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_990,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_521,plain,
    ( ~ v2_funct_1(X0_49)
    | ~ v1_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | k5_relat_1(k2_funct_1(X0_49),X0_49) = k6_partfun1(k2_relat_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_981,plain,
    ( k5_relat_1(k2_funct_1(X0_49),X0_49) = k6_partfun1(k2_relat_1(X0_49))
    | v2_funct_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_2243,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_981])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k2_relset_1(X0_51,X1_51,X0_49) = k2_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_985,plain,
    ( k2_relset_1(X0_51,X1_51,X0_49) = k2_relat_1(X0_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_1943,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_993,c_985])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_507,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1948,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1943,c_507])).

cnf(c_2256,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2243,c_1948])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2401,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2256,c_32,c_33,c_1193])).

cnf(c_6956,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_49)) = k5_relat_1(k6_partfun1(sK1),X0_49)
    | v1_relat_1(X0_49) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6933,c_2401])).

cnf(c_7003,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_1524,c_6956])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_49,X0_49) = k5_relat_1(X1_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_989,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_49,X1_49) = k5_relat_1(X0_49,X1_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | v1_funct_1(X1_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_3383,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_989])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3771,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3383,c_34])).

cnf(c_3772,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_3771])).

cnf(c_3781,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_3772])).

cnf(c_17,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_328,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_42,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_330,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_42])).

cnf(c_501,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_330])).

cnf(c_996,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1305,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | m1_subset_1(k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_515])).

cnf(c_1447,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1476,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_996,c_31,c_30,c_29,c_28,c_501,c_1447])).

cnf(c_3790,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3781,c_1476])).

cnf(c_4785,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3790,c_32])).

cnf(c_7017,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(light_normalisation,[status(thm)],[c_7003,c_4785])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_527,plain,
    ( ~ v1_relat_1(X0_49)
    | k5_relat_1(k6_partfun1(X0_51),X0_49) = k7_relat_1(X0_49,X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_975,plain,
    ( k5_relat_1(k6_partfun1(X0_51),X0_49) = k7_relat_1(X0_49,X0_51)
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_1584,plain,
    ( k5_relat_1(k6_partfun1(X0_51),sK3) = k7_relat_1(sK3,X0_51) ),
    inference(superposition,[status(thm)],[c_1524,c_975])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_0,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_0])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_305,c_14,c_13,c_0])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k7_relat_1(X0_49,X0_51) = X0_49 ),
    inference(subtyping,[status(esa)],[c_309])).

cnf(c_995,plain,
    ( k7_relat_1(X0_49,X0_51) = X0_49
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_2614,plain,
    ( k7_relat_1(sK3,sK1) = sK3 ),
    inference(superposition,[status(thm)],[c_991,c_995])).

cnf(c_2615,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_993,c_995])).

cnf(c_7,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_522,plain,
    ( v2_funct_1(k6_partfun1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_980,plain,
    ( v2_funct_1(k6_partfun1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_519,plain,
    ( ~ v2_funct_1(X0_49)
    | ~ v2_funct_1(X1_49)
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49)
    | ~ v1_relat_1(X1_49)
    | ~ v1_relat_1(X0_49)
    | k5_relat_1(k2_funct_1(X1_49),k2_funct_1(X0_49)) = k2_funct_1(k5_relat_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_983,plain,
    ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(X1_49)) = k2_funct_1(k5_relat_1(X1_49,X0_49))
    | v2_funct_1(X0_49) != iProver_top
    | v2_funct_1(X1_49) != iProver_top
    | v1_funct_1(X1_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_3532,plain,
    ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(k6_partfun1(X0_51))) = k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49))
    | v2_funct_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(k6_partfun1(X0_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_983])).

cnf(c_12,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_518,plain,
    ( k2_funct_1(k6_partfun1(X0_51)) = k6_partfun1(X0_51) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3539,plain,
    ( k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49)) = k5_relat_1(k2_funct_1(X0_49),k6_partfun1(X0_51))
    | v2_funct_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(k6_partfun1(X0_51)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3532,c_518])).

cnf(c_5,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_524,plain,
    ( v1_funct_1(k6_partfun1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_575,plain,
    ( v1_funct_1(k6_partfun1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_8,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_523,plain,
    ( v1_relat_1(k6_partfun1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_576,plain,
    ( v1_relat_1(k6_partfun1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_4641,plain,
    ( v1_relat_1(X0_49) != iProver_top
    | k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49)) = k5_relat_1(k2_funct_1(X0_49),k6_partfun1(X0_51))
    | v2_funct_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3539,c_575,c_576])).

cnf(c_4642,plain,
    ( k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49)) = k5_relat_1(k2_funct_1(X0_49),k6_partfun1(X0_51))
    | v2_funct_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_4641])).

cnf(c_4651,plain,
    ( k2_funct_1(k5_relat_1(k6_partfun1(X0_51),sK2)) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_51))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_4642])).

cnf(c_1588,plain,
    ( k5_relat_1(k6_partfun1(X0_51),sK2) = k7_relat_1(sK2,X0_51) ),
    inference(superposition,[status(thm)],[c_1525,c_975])).

cnf(c_4664,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_51)) = k2_funct_1(k7_relat_1(sK2,X0_51))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4651,c_1588])).

cnf(c_4805,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_51)) = k2_funct_1(k7_relat_1(sK2,X0_51)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4664,c_32,c_33,c_1193])).

cnf(c_7018,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_7017,c_1584,c_2614,c_2615,c_4805])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_511,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7018,c_511])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:14:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.20/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/0.96  
% 3.20/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/0.96  
% 3.20/0.96  ------  iProver source info
% 3.20/0.96  
% 3.20/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.20/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/0.96  git: non_committed_changes: false
% 3.20/0.96  git: last_make_outside_of_git: false
% 3.20/0.96  
% 3.20/0.96  ------ 
% 3.20/0.96  
% 3.20/0.96  ------ Input Options
% 3.20/0.96  
% 3.20/0.96  --out_options                           all
% 3.20/0.96  --tptp_safe_out                         true
% 3.20/0.96  --problem_path                          ""
% 3.20/0.96  --include_path                          ""
% 3.20/0.96  --clausifier                            res/vclausify_rel
% 3.20/0.96  --clausifier_options                    --mode clausify
% 3.20/0.96  --stdin                                 false
% 3.20/0.96  --stats_out                             all
% 3.20/0.96  
% 3.20/0.96  ------ General Options
% 3.20/0.96  
% 3.20/0.96  --fof                                   false
% 3.20/0.96  --time_out_real                         305.
% 3.20/0.96  --time_out_virtual                      -1.
% 3.20/0.96  --symbol_type_check                     false
% 3.20/0.96  --clausify_out                          false
% 3.20/0.96  --sig_cnt_out                           false
% 3.20/0.96  --trig_cnt_out                          false
% 3.20/0.96  --trig_cnt_out_tolerance                1.
% 3.20/0.96  --trig_cnt_out_sk_spl                   false
% 3.20/0.96  --abstr_cl_out                          false
% 3.20/0.96  
% 3.20/0.96  ------ Global Options
% 3.20/0.96  
% 3.20/0.96  --schedule                              default
% 3.20/0.96  --add_important_lit                     false
% 3.20/0.96  --prop_solver_per_cl                    1000
% 3.20/0.96  --min_unsat_core                        false
% 3.20/0.96  --soft_assumptions                      false
% 3.20/0.96  --soft_lemma_size                       3
% 3.20/0.96  --prop_impl_unit_size                   0
% 3.20/0.96  --prop_impl_unit                        []
% 3.20/0.96  --share_sel_clauses                     true
% 3.20/0.96  --reset_solvers                         false
% 3.20/0.96  --bc_imp_inh                            [conj_cone]
% 3.20/0.96  --conj_cone_tolerance                   3.
% 3.20/0.96  --extra_neg_conj                        none
% 3.20/0.96  --large_theory_mode                     true
% 3.20/0.96  --prolific_symb_bound                   200
% 3.20/0.96  --lt_threshold                          2000
% 3.20/0.96  --clause_weak_htbl                      true
% 3.20/0.96  --gc_record_bc_elim                     false
% 3.20/0.96  
% 3.20/0.96  ------ Preprocessing Options
% 3.20/0.96  
% 3.20/0.96  --preprocessing_flag                    true
% 3.20/0.96  --time_out_prep_mult                    0.1
% 3.20/0.96  --splitting_mode                        input
% 3.20/0.96  --splitting_grd                         true
% 3.20/0.96  --splitting_cvd                         false
% 3.20/0.96  --splitting_cvd_svl                     false
% 3.20/0.96  --splitting_nvd                         32
% 3.20/0.96  --sub_typing                            true
% 3.20/0.96  --prep_gs_sim                           true
% 3.20/0.96  --prep_unflatten                        true
% 3.20/0.96  --prep_res_sim                          true
% 3.20/0.96  --prep_upred                            true
% 3.20/0.96  --prep_sem_filter                       exhaustive
% 3.20/0.96  --prep_sem_filter_out                   false
% 3.20/0.96  --pred_elim                             true
% 3.20/0.96  --res_sim_input                         true
% 3.20/0.96  --eq_ax_congr_red                       true
% 3.20/0.96  --pure_diseq_elim                       true
% 3.20/0.96  --brand_transform                       false
% 3.20/0.96  --non_eq_to_eq                          false
% 3.20/0.96  --prep_def_merge                        true
% 3.20/0.96  --prep_def_merge_prop_impl              false
% 3.20/0.96  --prep_def_merge_mbd                    true
% 3.20/0.96  --prep_def_merge_tr_red                 false
% 3.20/0.96  --prep_def_merge_tr_cl                  false
% 3.20/0.96  --smt_preprocessing                     true
% 3.20/0.96  --smt_ac_axioms                         fast
% 3.20/0.96  --preprocessed_out                      false
% 3.20/0.96  --preprocessed_stats                    false
% 3.20/0.96  
% 3.20/0.96  ------ Abstraction refinement Options
% 3.20/0.96  
% 3.20/0.96  --abstr_ref                             []
% 3.20/0.96  --abstr_ref_prep                        false
% 3.20/0.96  --abstr_ref_until_sat                   false
% 3.20/0.96  --abstr_ref_sig_restrict                funpre
% 3.20/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.96  --abstr_ref_under                       []
% 3.20/0.96  
% 3.20/0.96  ------ SAT Options
% 3.20/0.96  
% 3.20/0.96  --sat_mode                              false
% 3.20/0.96  --sat_fm_restart_options                ""
% 3.20/0.96  --sat_gr_def                            false
% 3.20/0.96  --sat_epr_types                         true
% 3.20/0.96  --sat_non_cyclic_types                  false
% 3.20/0.96  --sat_finite_models                     false
% 3.20/0.96  --sat_fm_lemmas                         false
% 3.20/0.96  --sat_fm_prep                           false
% 3.20/0.96  --sat_fm_uc_incr                        true
% 3.20/0.96  --sat_out_model                         small
% 3.20/0.96  --sat_out_clauses                       false
% 3.20/0.96  
% 3.20/0.96  ------ QBF Options
% 3.20/0.96  
% 3.20/0.96  --qbf_mode                              false
% 3.20/0.96  --qbf_elim_univ                         false
% 3.20/0.96  --qbf_dom_inst                          none
% 3.20/0.96  --qbf_dom_pre_inst                      false
% 3.20/0.96  --qbf_sk_in                             false
% 3.20/0.96  --qbf_pred_elim                         true
% 3.20/0.96  --qbf_split                             512
% 3.20/0.96  
% 3.20/0.96  ------ BMC1 Options
% 3.20/0.96  
% 3.20/0.96  --bmc1_incremental                      false
% 3.20/0.96  --bmc1_axioms                           reachable_all
% 3.20/0.96  --bmc1_min_bound                        0
% 3.20/0.96  --bmc1_max_bound                        -1
% 3.20/0.96  --bmc1_max_bound_default                -1
% 3.20/0.96  --bmc1_symbol_reachability              true
% 3.20/0.96  --bmc1_property_lemmas                  false
% 3.20/0.96  --bmc1_k_induction                      false
% 3.20/0.96  --bmc1_non_equiv_states                 false
% 3.20/0.96  --bmc1_deadlock                         false
% 3.20/0.96  --bmc1_ucm                              false
% 3.20/0.96  --bmc1_add_unsat_core                   none
% 3.20/0.96  --bmc1_unsat_core_children              false
% 3.20/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.96  --bmc1_out_stat                         full
% 3.20/0.96  --bmc1_ground_init                      false
% 3.20/0.96  --bmc1_pre_inst_next_state              false
% 3.20/0.96  --bmc1_pre_inst_state                   false
% 3.20/0.96  --bmc1_pre_inst_reach_state             false
% 3.20/0.96  --bmc1_out_unsat_core                   false
% 3.20/0.96  --bmc1_aig_witness_out                  false
% 3.20/0.96  --bmc1_verbose                          false
% 3.20/0.96  --bmc1_dump_clauses_tptp                false
% 3.20/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.96  --bmc1_dump_file                        -
% 3.20/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.96  --bmc1_ucm_extend_mode                  1
% 3.20/0.96  --bmc1_ucm_init_mode                    2
% 3.20/0.96  --bmc1_ucm_cone_mode                    none
% 3.20/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.96  --bmc1_ucm_relax_model                  4
% 3.20/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.96  --bmc1_ucm_layered_model                none
% 3.20/0.96  --bmc1_ucm_max_lemma_size               10
% 3.20/0.96  
% 3.20/0.96  ------ AIG Options
% 3.20/0.96  
% 3.20/0.96  --aig_mode                              false
% 3.20/0.96  
% 3.20/0.96  ------ Instantiation Options
% 3.20/0.96  
% 3.20/0.96  --instantiation_flag                    true
% 3.20/0.96  --inst_sos_flag                         false
% 3.20/0.96  --inst_sos_phase                        true
% 3.20/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.96  --inst_lit_sel_side                     num_symb
% 3.20/0.96  --inst_solver_per_active                1400
% 3.20/0.96  --inst_solver_calls_frac                1.
% 3.20/0.96  --inst_passive_queue_type               priority_queues
% 3.20/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.96  --inst_passive_queues_freq              [25;2]
% 3.20/0.96  --inst_dismatching                      true
% 3.20/0.96  --inst_eager_unprocessed_to_passive     true
% 3.20/0.96  --inst_prop_sim_given                   true
% 3.20/0.96  --inst_prop_sim_new                     false
% 3.20/0.96  --inst_subs_new                         false
% 3.20/0.96  --inst_eq_res_simp                      false
% 3.20/0.96  --inst_subs_given                       false
% 3.20/0.96  --inst_orphan_elimination               true
% 3.20/0.96  --inst_learning_loop_flag               true
% 3.20/0.96  --inst_learning_start                   3000
% 3.20/0.96  --inst_learning_factor                  2
% 3.20/0.96  --inst_start_prop_sim_after_learn       3
% 3.20/0.96  --inst_sel_renew                        solver
% 3.20/0.96  --inst_lit_activity_flag                true
% 3.20/0.96  --inst_restr_to_given                   false
% 3.20/0.96  --inst_activity_threshold               500
% 3.20/0.96  --inst_out_proof                        true
% 3.20/0.96  
% 3.20/0.96  ------ Resolution Options
% 3.20/0.96  
% 3.20/0.96  --resolution_flag                       true
% 3.20/0.96  --res_lit_sel                           adaptive
% 3.20/0.96  --res_lit_sel_side                      none
% 3.20/0.96  --res_ordering                          kbo
% 3.20/0.96  --res_to_prop_solver                    active
% 3.20/0.96  --res_prop_simpl_new                    false
% 3.20/0.96  --res_prop_simpl_given                  true
% 3.20/0.96  --res_passive_queue_type                priority_queues
% 3.20/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.96  --res_passive_queues_freq               [15;5]
% 3.20/0.96  --res_forward_subs                      full
% 3.20/0.96  --res_backward_subs                     full
% 3.20/0.96  --res_forward_subs_resolution           true
% 3.20/0.96  --res_backward_subs_resolution          true
% 3.20/0.96  --res_orphan_elimination                true
% 3.20/0.96  --res_time_limit                        2.
% 3.20/0.96  --res_out_proof                         true
% 3.20/0.96  
% 3.20/0.96  ------ Superposition Options
% 3.20/0.96  
% 3.20/0.96  --superposition_flag                    true
% 3.20/0.96  --sup_passive_queue_type                priority_queues
% 3.20/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.96  --demod_completeness_check              fast
% 3.20/0.96  --demod_use_ground                      true
% 3.20/0.96  --sup_to_prop_solver                    passive
% 3.20/0.96  --sup_prop_simpl_new                    true
% 3.20/0.96  --sup_prop_simpl_given                  true
% 3.20/0.96  --sup_fun_splitting                     false
% 3.20/0.96  --sup_smt_interval                      50000
% 3.20/0.96  
% 3.20/0.96  ------ Superposition Simplification Setup
% 3.20/0.96  
% 3.20/0.96  --sup_indices_passive                   []
% 3.20/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.96  --sup_full_bw                           [BwDemod]
% 3.20/0.96  --sup_immed_triv                        [TrivRules]
% 3.20/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.96  --sup_immed_bw_main                     []
% 3.20/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.96  
% 3.20/0.96  ------ Combination Options
% 3.20/0.96  
% 3.20/0.96  --comb_res_mult                         3
% 3.20/0.96  --comb_sup_mult                         2
% 3.20/0.96  --comb_inst_mult                        10
% 3.20/0.96  
% 3.20/0.96  ------ Debug Options
% 3.20/0.96  
% 3.20/0.96  --dbg_backtrace                         false
% 3.20/0.96  --dbg_dump_prop_clauses                 false
% 3.20/0.96  --dbg_dump_prop_clauses_file            -
% 3.20/0.96  --dbg_out_stat                          false
% 3.20/0.96  ------ Parsing...
% 3.20/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/0.96  
% 3.20/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.20/0.96  
% 3.20/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/0.96  
% 3.20/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/0.96  ------ Proving...
% 3.20/0.96  ------ Problem Properties 
% 3.20/0.96  
% 3.20/0.96  
% 3.20/0.96  clauses                                 28
% 3.20/0.96  conjectures                             9
% 3.20/0.96  EPR                                     5
% 3.20/0.96  Horn                                    28
% 3.20/0.96  unary                                   14
% 3.20/0.96  binary                                  5
% 3.20/0.96  lits                                    64
% 3.20/0.96  lits eq                                 14
% 3.20/0.96  fd_pure                                 0
% 3.20/0.96  fd_pseudo                               0
% 3.20/0.96  fd_cond                                 0
% 3.20/0.96  fd_pseudo_cond                          0
% 3.20/0.96  AC symbols                              0
% 3.20/0.96  
% 3.20/0.96  ------ Schedule dynamic 5 is on 
% 3.20/0.96  
% 3.20/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/0.96  
% 3.20/0.96  
% 3.20/0.96  ------ 
% 3.20/0.96  Current options:
% 3.20/0.96  ------ 
% 3.20/0.96  
% 3.20/0.96  ------ Input Options
% 3.20/0.96  
% 3.20/0.96  --out_options                           all
% 3.20/0.96  --tptp_safe_out                         true
% 3.20/0.96  --problem_path                          ""
% 3.20/0.96  --include_path                          ""
% 3.20/0.96  --clausifier                            res/vclausify_rel
% 3.20/0.96  --clausifier_options                    --mode clausify
% 3.20/0.96  --stdin                                 false
% 3.20/0.96  --stats_out                             all
% 3.20/0.96  
% 3.20/0.96  ------ General Options
% 3.20/0.96  
% 3.20/0.96  --fof                                   false
% 3.20/0.96  --time_out_real                         305.
% 3.20/0.96  --time_out_virtual                      -1.
% 3.20/0.96  --symbol_type_check                     false
% 3.20/0.96  --clausify_out                          false
% 3.20/0.96  --sig_cnt_out                           false
% 3.20/0.96  --trig_cnt_out                          false
% 3.20/0.96  --trig_cnt_out_tolerance                1.
% 3.20/0.96  --trig_cnt_out_sk_spl                   false
% 3.20/0.96  --abstr_cl_out                          false
% 3.20/0.96  
% 3.20/0.96  ------ Global Options
% 3.20/0.96  
% 3.20/0.96  --schedule                              default
% 3.20/0.96  --add_important_lit                     false
% 3.20/0.96  --prop_solver_per_cl                    1000
% 3.20/0.96  --min_unsat_core                        false
% 3.20/0.96  --soft_assumptions                      false
% 3.20/0.96  --soft_lemma_size                       3
% 3.20/0.96  --prop_impl_unit_size                   0
% 3.20/0.96  --prop_impl_unit                        []
% 3.20/0.96  --share_sel_clauses                     true
% 3.20/0.96  --reset_solvers                         false
% 3.20/0.96  --bc_imp_inh                            [conj_cone]
% 3.20/0.96  --conj_cone_tolerance                   3.
% 3.20/0.96  --extra_neg_conj                        none
% 3.20/0.96  --large_theory_mode                     true
% 3.20/0.96  --prolific_symb_bound                   200
% 3.20/0.96  --lt_threshold                          2000
% 3.20/0.96  --clause_weak_htbl                      true
% 3.20/0.96  --gc_record_bc_elim                     false
% 3.20/0.96  
% 3.20/0.96  ------ Preprocessing Options
% 3.20/0.96  
% 3.20/0.96  --preprocessing_flag                    true
% 3.20/0.96  --time_out_prep_mult                    0.1
% 3.20/0.96  --splitting_mode                        input
% 3.20/0.96  --splitting_grd                         true
% 3.20/0.96  --splitting_cvd                         false
% 3.20/0.96  --splitting_cvd_svl                     false
% 3.20/0.96  --splitting_nvd                         32
% 3.20/0.96  --sub_typing                            true
% 3.20/0.96  --prep_gs_sim                           true
% 3.20/0.96  --prep_unflatten                        true
% 3.20/0.96  --prep_res_sim                          true
% 3.20/0.96  --prep_upred                            true
% 3.20/0.96  --prep_sem_filter                       exhaustive
% 3.20/0.96  --prep_sem_filter_out                   false
% 3.20/0.96  --pred_elim                             true
% 3.20/0.96  --res_sim_input                         true
% 3.20/0.96  --eq_ax_congr_red                       true
% 3.20/0.96  --pure_diseq_elim                       true
% 3.20/0.96  --brand_transform                       false
% 3.20/0.96  --non_eq_to_eq                          false
% 3.20/0.96  --prep_def_merge                        true
% 3.20/0.96  --prep_def_merge_prop_impl              false
% 3.20/0.96  --prep_def_merge_mbd                    true
% 3.20/0.96  --prep_def_merge_tr_red                 false
% 3.20/0.96  --prep_def_merge_tr_cl                  false
% 3.20/0.96  --smt_preprocessing                     true
% 3.20/0.96  --smt_ac_axioms                         fast
% 3.20/0.96  --preprocessed_out                      false
% 3.20/0.96  --preprocessed_stats                    false
% 3.20/0.96  
% 3.20/0.96  ------ Abstraction refinement Options
% 3.20/0.96  
% 3.20/0.96  --abstr_ref                             []
% 3.20/0.96  --abstr_ref_prep                        false
% 3.20/0.96  --abstr_ref_until_sat                   false
% 3.20/0.96  --abstr_ref_sig_restrict                funpre
% 3.20/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.96  --abstr_ref_under                       []
% 3.20/0.96  
% 3.20/0.96  ------ SAT Options
% 3.20/0.96  
% 3.20/0.96  --sat_mode                              false
% 3.20/0.96  --sat_fm_restart_options                ""
% 3.20/0.96  --sat_gr_def                            false
% 3.20/0.96  --sat_epr_types                         true
% 3.20/0.96  --sat_non_cyclic_types                  false
% 3.20/0.96  --sat_finite_models                     false
% 3.20/0.96  --sat_fm_lemmas                         false
% 3.20/0.96  --sat_fm_prep                           false
% 3.20/0.96  --sat_fm_uc_incr                        true
% 3.20/0.96  --sat_out_model                         small
% 3.20/0.96  --sat_out_clauses                       false
% 3.20/0.96  
% 3.20/0.96  ------ QBF Options
% 3.20/0.96  
% 3.20/0.96  --qbf_mode                              false
% 3.20/0.96  --qbf_elim_univ                         false
% 3.20/0.96  --qbf_dom_inst                          none
% 3.20/0.96  --qbf_dom_pre_inst                      false
% 3.20/0.96  --qbf_sk_in                             false
% 3.20/0.96  --qbf_pred_elim                         true
% 3.20/0.96  --qbf_split                             512
% 3.20/0.96  
% 3.20/0.96  ------ BMC1 Options
% 3.20/0.96  
% 3.20/0.96  --bmc1_incremental                      false
% 3.20/0.96  --bmc1_axioms                           reachable_all
% 3.20/0.96  --bmc1_min_bound                        0
% 3.20/0.96  --bmc1_max_bound                        -1
% 3.20/0.96  --bmc1_max_bound_default                -1
% 3.20/0.96  --bmc1_symbol_reachability              true
% 3.20/0.96  --bmc1_property_lemmas                  false
% 3.20/0.96  --bmc1_k_induction                      false
% 3.20/0.96  --bmc1_non_equiv_states                 false
% 3.20/0.96  --bmc1_deadlock                         false
% 3.20/0.96  --bmc1_ucm                              false
% 3.20/0.96  --bmc1_add_unsat_core                   none
% 3.20/0.96  --bmc1_unsat_core_children              false
% 3.20/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.96  --bmc1_out_stat                         full
% 3.20/0.96  --bmc1_ground_init                      false
% 3.20/0.96  --bmc1_pre_inst_next_state              false
% 3.20/0.96  --bmc1_pre_inst_state                   false
% 3.20/0.96  --bmc1_pre_inst_reach_state             false
% 3.20/0.96  --bmc1_out_unsat_core                   false
% 3.20/0.96  --bmc1_aig_witness_out                  false
% 3.20/0.96  --bmc1_verbose                          false
% 3.20/0.96  --bmc1_dump_clauses_tptp                false
% 3.20/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.96  --bmc1_dump_file                        -
% 3.20/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.96  --bmc1_ucm_extend_mode                  1
% 3.20/0.96  --bmc1_ucm_init_mode                    2
% 3.20/0.96  --bmc1_ucm_cone_mode                    none
% 3.20/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.96  --bmc1_ucm_relax_model                  4
% 3.20/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.96  --bmc1_ucm_layered_model                none
% 3.20/0.96  --bmc1_ucm_max_lemma_size               10
% 3.20/0.96  
% 3.20/0.96  ------ AIG Options
% 3.20/0.96  
% 3.20/0.96  --aig_mode                              false
% 3.20/0.96  
% 3.20/0.96  ------ Instantiation Options
% 3.20/0.96  
% 3.20/0.96  --instantiation_flag                    true
% 3.20/0.96  --inst_sos_flag                         false
% 3.20/0.96  --inst_sos_phase                        true
% 3.20/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.96  --inst_lit_sel_side                     none
% 3.20/0.96  --inst_solver_per_active                1400
% 3.20/0.96  --inst_solver_calls_frac                1.
% 3.20/0.96  --inst_passive_queue_type               priority_queues
% 3.20/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.96  --inst_passive_queues_freq              [25;2]
% 3.20/0.96  --inst_dismatching                      true
% 3.20/0.96  --inst_eager_unprocessed_to_passive     true
% 3.20/0.96  --inst_prop_sim_given                   true
% 3.20/0.96  --inst_prop_sim_new                     false
% 3.20/0.96  --inst_subs_new                         false
% 3.20/0.96  --inst_eq_res_simp                      false
% 3.20/0.96  --inst_subs_given                       false
% 3.20/0.96  --inst_orphan_elimination               true
% 3.20/0.96  --inst_learning_loop_flag               true
% 3.20/0.96  --inst_learning_start                   3000
% 3.20/0.96  --inst_learning_factor                  2
% 3.20/0.96  --inst_start_prop_sim_after_learn       3
% 3.20/0.96  --inst_sel_renew                        solver
% 3.20/0.96  --inst_lit_activity_flag                true
% 3.20/0.96  --inst_restr_to_given                   false
% 3.20/0.96  --inst_activity_threshold               500
% 3.20/0.96  --inst_out_proof                        true
% 3.20/0.96  
% 3.20/0.96  ------ Resolution Options
% 3.20/0.96  
% 3.20/0.96  --resolution_flag                       false
% 3.20/0.96  --res_lit_sel                           adaptive
% 3.20/0.96  --res_lit_sel_side                      none
% 3.20/0.96  --res_ordering                          kbo
% 3.20/0.96  --res_to_prop_solver                    active
% 3.20/0.96  --res_prop_simpl_new                    false
% 3.20/0.96  --res_prop_simpl_given                  true
% 3.20/0.96  --res_passive_queue_type                priority_queues
% 3.20/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.96  --res_passive_queues_freq               [15;5]
% 3.20/0.96  --res_forward_subs                      full
% 3.20/0.96  --res_backward_subs                     full
% 3.20/0.96  --res_forward_subs_resolution           true
% 3.20/0.96  --res_backward_subs_resolution          true
% 3.20/0.96  --res_orphan_elimination                true
% 3.20/0.96  --res_time_limit                        2.
% 3.20/0.96  --res_out_proof                         true
% 3.20/0.96  
% 3.20/0.96  ------ Superposition Options
% 3.20/0.96  
% 3.20/0.96  --superposition_flag                    true
% 3.20/0.96  --sup_passive_queue_type                priority_queues
% 3.20/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.96  --demod_completeness_check              fast
% 3.20/0.96  --demod_use_ground                      true
% 3.20/0.96  --sup_to_prop_solver                    passive
% 3.20/0.96  --sup_prop_simpl_new                    true
% 3.20/0.96  --sup_prop_simpl_given                  true
% 3.20/0.96  --sup_fun_splitting                     false
% 3.20/0.96  --sup_smt_interval                      50000
% 3.20/0.96  
% 3.20/0.96  ------ Superposition Simplification Setup
% 3.20/0.96  
% 3.20/0.96  --sup_indices_passive                   []
% 3.20/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.96  --sup_full_bw                           [BwDemod]
% 3.20/0.96  --sup_immed_triv                        [TrivRules]
% 3.20/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.96  --sup_immed_bw_main                     []
% 3.20/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.96  
% 3.20/0.96  ------ Combination Options
% 3.20/0.96  
% 3.20/0.96  --comb_res_mult                         3
% 3.20/0.96  --comb_sup_mult                         2
% 3.20/0.96  --comb_inst_mult                        10
% 3.20/0.96  
% 3.20/0.96  ------ Debug Options
% 3.20/0.96  
% 3.20/0.96  --dbg_backtrace                         false
% 3.20/0.96  --dbg_dump_prop_clauses                 false
% 3.20/0.96  --dbg_dump_prop_clauses_file            -
% 3.20/0.96  --dbg_out_stat                          false
% 3.20/0.96  
% 3.20/0.96  
% 3.20/0.96  
% 3.20/0.96  
% 3.20/0.96  ------ Proving...
% 3.20/0.96  
% 3.20/0.96  
% 3.20/0.96  % SZS status Theorem for theBenchmark.p
% 3.20/0.96  
% 3.20/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/0.96  
% 3.20/0.96  fof(f18,conjecture,(
% 3.20/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f19,negated_conjecture,(
% 3.20/0.96    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.20/0.96    inference(negated_conjecture,[],[f18])).
% 3.20/0.96  
% 3.20/0.96  fof(f20,plain,(
% 3.20/0.96    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.20/0.96    inference(pure_predicate_removal,[],[f19])).
% 3.20/0.96  
% 3.20/0.96  fof(f42,plain,(
% 3.20/0.96    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.20/0.96    inference(ennf_transformation,[],[f20])).
% 3.20/0.96  
% 3.20/0.96  fof(f43,plain,(
% 3.20/0.96    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.20/0.96    inference(flattening,[],[f42])).
% 3.20/0.96  
% 3.20/0.96  fof(f46,plain,(
% 3.20/0.96    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 3.20/0.96    introduced(choice_axiom,[])).
% 3.20/0.96  
% 3.20/0.96  fof(f45,plain,(
% 3.20/0.96    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 3.20/0.96    introduced(choice_axiom,[])).
% 3.20/0.96  
% 3.20/0.96  fof(f47,plain,(
% 3.20/0.96    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 3.20/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f46,f45])).
% 3.20/0.96  
% 3.20/0.96  fof(f74,plain,(
% 3.20/0.96    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.20/0.96    inference(cnf_transformation,[],[f47])).
% 3.20/0.96  
% 3.20/0.96  fof(f10,axiom,(
% 3.20/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f33,plain,(
% 3.20/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.96    inference(ennf_transformation,[],[f10])).
% 3.20/0.96  
% 3.20/0.96  fof(f61,plain,(
% 3.20/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.96    inference(cnf_transformation,[],[f33])).
% 3.20/0.96  
% 3.20/0.96  fof(f72,plain,(
% 3.20/0.96    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.20/0.96    inference(cnf_transformation,[],[f47])).
% 3.20/0.96  
% 3.20/0.96  fof(f71,plain,(
% 3.20/0.96    v1_funct_1(sK2)),
% 3.20/0.96    inference(cnf_transformation,[],[f47])).
% 3.20/0.96  
% 3.20/0.96  fof(f4,axiom,(
% 3.20/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f27,plain,(
% 3.20/0.96    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.20/0.96    inference(ennf_transformation,[],[f4])).
% 3.20/0.96  
% 3.20/0.96  fof(f28,plain,(
% 3.20/0.96    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.20/0.96    inference(flattening,[],[f27])).
% 3.20/0.96  
% 3.20/0.96  fof(f51,plain,(
% 3.20/0.96    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/0.96    inference(cnf_transformation,[],[f28])).
% 3.20/0.96  
% 3.20/0.96  fof(f2,axiom,(
% 3.20/0.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f25,plain,(
% 3.20/0.96    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.20/0.96    inference(ennf_transformation,[],[f2])).
% 3.20/0.96  
% 3.20/0.96  fof(f49,plain,(
% 3.20/0.96    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.20/0.96    inference(cnf_transformation,[],[f25])).
% 3.20/0.96  
% 3.20/0.96  fof(f77,plain,(
% 3.20/0.96    v2_funct_1(sK2)),
% 3.20/0.96    inference(cnf_transformation,[],[f47])).
% 3.20/0.96  
% 3.20/0.96  fof(f7,axiom,(
% 3.20/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f29,plain,(
% 3.20/0.96    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.20/0.96    inference(ennf_transformation,[],[f7])).
% 3.20/0.96  
% 3.20/0.96  fof(f30,plain,(
% 3.20/0.96    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.20/0.96    inference(flattening,[],[f29])).
% 3.20/0.96  
% 3.20/0.96  fof(f58,plain,(
% 3.20/0.96    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/0.96    inference(cnf_transformation,[],[f30])).
% 3.20/0.96  
% 3.20/0.96  fof(f17,axiom,(
% 3.20/0.96    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f70,plain,(
% 3.20/0.96    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.20/0.96    inference(cnf_transformation,[],[f17])).
% 3.20/0.96  
% 3.20/0.96  fof(f86,plain,(
% 3.20/0.96    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/0.96    inference(definition_unfolding,[],[f58,f70])).
% 3.20/0.96  
% 3.20/0.96  fof(f12,axiom,(
% 3.20/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f35,plain,(
% 3.20/0.96    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.96    inference(ennf_transformation,[],[f12])).
% 3.20/0.96  
% 3.20/0.96  fof(f63,plain,(
% 3.20/0.96    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.96    inference(cnf_transformation,[],[f35])).
% 3.20/0.96  
% 3.20/0.96  fof(f75,plain,(
% 3.20/0.96    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.20/0.96    inference(cnf_transformation,[],[f47])).
% 3.20/0.96  
% 3.20/0.96  fof(f16,axiom,(
% 3.20/0.96    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f40,plain,(
% 3.20/0.96    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.20/0.96    inference(ennf_transformation,[],[f16])).
% 3.20/0.96  
% 3.20/0.96  fof(f41,plain,(
% 3.20/0.96    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.20/0.96    inference(flattening,[],[f40])).
% 3.20/0.96  
% 3.20/0.96  fof(f69,plain,(
% 3.20/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.20/0.96    inference(cnf_transformation,[],[f41])).
% 3.20/0.96  
% 3.20/0.96  fof(f73,plain,(
% 3.20/0.96    v1_funct_1(sK3)),
% 3.20/0.96    inference(cnf_transformation,[],[f47])).
% 3.20/0.96  
% 3.20/0.96  fof(f13,axiom,(
% 3.20/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f36,plain,(
% 3.20/0.96    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.20/0.96    inference(ennf_transformation,[],[f13])).
% 3.20/0.96  
% 3.20/0.96  fof(f37,plain,(
% 3.20/0.96    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.96    inference(flattening,[],[f36])).
% 3.20/0.96  
% 3.20/0.96  fof(f44,plain,(
% 3.20/0.96    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.96    inference(nnf_transformation,[],[f37])).
% 3.20/0.96  
% 3.20/0.96  fof(f64,plain,(
% 3.20/0.96    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.96    inference(cnf_transformation,[],[f44])).
% 3.20/0.96  
% 3.20/0.96  fof(f76,plain,(
% 3.20/0.96    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.20/0.96    inference(cnf_transformation,[],[f47])).
% 3.20/0.96  
% 3.20/0.96  fof(f15,axiom,(
% 3.20/0.96    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f21,plain,(
% 3.20/0.96    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.20/0.96    inference(pure_predicate_removal,[],[f15])).
% 3.20/0.96  
% 3.20/0.96  fof(f68,plain,(
% 3.20/0.96    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.20/0.96    inference(cnf_transformation,[],[f21])).
% 3.20/0.96  
% 3.20/0.96  fof(f14,axiom,(
% 3.20/0.96    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f38,plain,(
% 3.20/0.96    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.20/0.96    inference(ennf_transformation,[],[f14])).
% 3.20/0.96  
% 3.20/0.96  fof(f39,plain,(
% 3.20/0.96    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.20/0.96    inference(flattening,[],[f38])).
% 3.20/0.96  
% 3.20/0.96  fof(f67,plain,(
% 3.20/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.20/0.96    inference(cnf_transformation,[],[f39])).
% 3.20/0.96  
% 3.20/0.96  fof(f3,axiom,(
% 3.20/0.96    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f26,plain,(
% 3.20/0.96    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.20/0.96    inference(ennf_transformation,[],[f3])).
% 3.20/0.96  
% 3.20/0.96  fof(f50,plain,(
% 3.20/0.96    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.20/0.96    inference(cnf_transformation,[],[f26])).
% 3.20/0.96  
% 3.20/0.96  fof(f81,plain,(
% 3.20/0.96    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.20/0.96    inference(definition_unfolding,[],[f50,f70])).
% 3.20/0.96  
% 3.20/0.96  fof(f11,axiom,(
% 3.20/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f22,plain,(
% 3.20/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.20/0.96    inference(pure_predicate_removal,[],[f11])).
% 3.20/0.96  
% 3.20/0.96  fof(f34,plain,(
% 3.20/0.96    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.96    inference(ennf_transformation,[],[f22])).
% 3.20/0.96  
% 3.20/0.96  fof(f62,plain,(
% 3.20/0.96    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.96    inference(cnf_transformation,[],[f34])).
% 3.20/0.96  
% 3.20/0.96  fof(f1,axiom,(
% 3.20/0.96    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f23,plain,(
% 3.20/0.96    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.20/0.96    inference(ennf_transformation,[],[f1])).
% 3.20/0.96  
% 3.20/0.96  fof(f24,plain,(
% 3.20/0.96    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.20/0.96    inference(flattening,[],[f23])).
% 3.20/0.96  
% 3.20/0.96  fof(f48,plain,(
% 3.20/0.96    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.20/0.96    inference(cnf_transformation,[],[f24])).
% 3.20/0.96  
% 3.20/0.96  fof(f6,axiom,(
% 3.20/0.96    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f56,plain,(
% 3.20/0.96    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.20/0.96    inference(cnf_transformation,[],[f6])).
% 3.20/0.96  
% 3.20/0.96  fof(f84,plain,(
% 3.20/0.96    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.20/0.96    inference(definition_unfolding,[],[f56,f70])).
% 3.20/0.96  
% 3.20/0.96  fof(f8,axiom,(
% 3.20/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)))))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f31,plain,(
% 3.20/0.96    ! [X0] : (! [X1] : ((k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.20/0.96    inference(ennf_transformation,[],[f8])).
% 3.20/0.96  
% 3.20/0.96  fof(f32,plain,(
% 3.20/0.96    ! [X0] : (! [X1] : (k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.20/0.96    inference(flattening,[],[f31])).
% 3.20/0.96  
% 3.20/0.96  fof(f59,plain,(
% 3.20/0.96    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/0.96    inference(cnf_transformation,[],[f32])).
% 3.20/0.96  
% 3.20/0.96  fof(f9,axiom,(
% 3.20/0.96    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f60,plain,(
% 3.20/0.96    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 3.20/0.96    inference(cnf_transformation,[],[f9])).
% 3.20/0.96  
% 3.20/0.96  fof(f88,plain,(
% 3.20/0.96    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 3.20/0.96    inference(definition_unfolding,[],[f60,f70,f70])).
% 3.20/0.96  
% 3.20/0.96  fof(f5,axiom,(
% 3.20/0.96    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.20/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.96  
% 3.20/0.96  fof(f54,plain,(
% 3.20/0.96    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.20/0.96    inference(cnf_transformation,[],[f5])).
% 3.20/0.96  
% 3.20/0.96  fof(f82,plain,(
% 3.20/0.96    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 3.20/0.96    inference(definition_unfolding,[],[f54,f70])).
% 3.20/0.96  
% 3.20/0.96  fof(f55,plain,(
% 3.20/0.96    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.20/0.96    inference(cnf_transformation,[],[f6])).
% 3.20/0.96  
% 3.20/0.96  fof(f85,plain,(
% 3.20/0.96    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.20/0.96    inference(definition_unfolding,[],[f55,f70])).
% 3.20/0.96  
% 3.20/0.96  fof(f80,plain,(
% 3.20/0.96    k2_funct_1(sK2) != sK3),
% 3.20/0.96    inference(cnf_transformation,[],[f47])).
% 3.20/0.96  
% 3.20/0.96  cnf(c_28,negated_conjecture,
% 3.20/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.20/0.96      inference(cnf_transformation,[],[f74]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_506,negated_conjecture,
% 3.20/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_28]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_991,plain,
% 3.20/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_13,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.96      | v1_relat_1(X0) ),
% 3.20/0.96      inference(cnf_transformation,[],[f61]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_517,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.20/0.96      | v1_relat_1(X0_49) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_13]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_984,plain,
% 3.20/0.96      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.20/0.96      | v1_relat_1(X0_49) = iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_1524,plain,
% 3.20/0.96      ( v1_relat_1(sK3) = iProver_top ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_991,c_984]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_30,negated_conjecture,
% 3.20/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.20/0.96      inference(cnf_transformation,[],[f72]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_504,negated_conjecture,
% 3.20/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_30]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_993,plain,
% 3.20/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_1525,plain,
% 3.20/0.96      ( v1_relat_1(sK2) = iProver_top ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_993,c_984]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_31,negated_conjecture,
% 3.20/0.96      ( v1_funct_1(sK2) ),
% 3.20/0.96      inference(cnf_transformation,[],[f71]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_503,negated_conjecture,
% 3.20/0.96      ( v1_funct_1(sK2) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_31]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_994,plain,
% 3.20/0.96      ( v1_funct_1(sK2) = iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_4,plain,
% 3.20/0.96      ( ~ v1_funct_1(X0)
% 3.20/0.96      | ~ v1_relat_1(X0)
% 3.20/0.96      | v1_relat_1(k2_funct_1(X0)) ),
% 3.20/0.96      inference(cnf_transformation,[],[f51]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_525,plain,
% 3.20/0.96      ( ~ v1_funct_1(X0_49)
% 3.20/0.96      | ~ v1_relat_1(X0_49)
% 3.20/0.96      | v1_relat_1(k2_funct_1(X0_49)) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_4]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_977,plain,
% 3.20/0.96      ( v1_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top
% 3.20/0.96      | v1_relat_1(k2_funct_1(X0_49)) = iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_1,plain,
% 3.20/0.96      ( ~ v1_relat_1(X0)
% 3.20/0.96      | ~ v1_relat_1(X1)
% 3.20/0.96      | ~ v1_relat_1(X2)
% 3.20/0.96      | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1)) ),
% 3.20/0.96      inference(cnf_transformation,[],[f49]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_528,plain,
% 3.20/0.96      ( ~ v1_relat_1(X0_49)
% 3.20/0.96      | ~ v1_relat_1(X1_49)
% 3.20/0.96      | ~ v1_relat_1(X2_49)
% 3.20/0.96      | k5_relat_1(k5_relat_1(X2_49,X0_49),X1_49) = k5_relat_1(X2_49,k5_relat_1(X0_49,X1_49)) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_1]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_974,plain,
% 3.20/0.96      ( k5_relat_1(k5_relat_1(X0_49,X1_49),X2_49) = k5_relat_1(X0_49,k5_relat_1(X1_49,X2_49))
% 3.20/0.96      | v1_relat_1(X1_49) != iProver_top
% 3.20/0.96      | v1_relat_1(X2_49) != iProver_top
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_3119,plain,
% 3.20/0.96      ( k5_relat_1(k2_funct_1(X0_49),k5_relat_1(X1_49,X2_49)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_49),X1_49),X2_49)
% 3.20/0.96      | v1_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top
% 3.20/0.96      | v1_relat_1(X1_49) != iProver_top
% 3.20/0.96      | v1_relat_1(X2_49) != iProver_top ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_977,c_974]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_6561,plain,
% 3.20/0.96      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49))
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top
% 3.20/0.96      | v1_relat_1(X1_49) != iProver_top
% 3.20/0.96      | v1_relat_1(sK2) != iProver_top ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_994,c_3119]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_33,plain,
% 3.20/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_1192,plain,
% 3.20/0.96      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.20/0.96      | v1_relat_1(sK2) ),
% 3.20/0.96      inference(instantiation,[status(thm)],[c_517]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_1193,plain,
% 3.20/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.20/0.96      | v1_relat_1(sK2) = iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_1192]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_6924,plain,
% 3.20/0.96      ( v1_relat_1(X1_49) != iProver_top
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top
% 3.20/0.96      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49)) ),
% 3.20/0.96      inference(global_propositional_subsumption,
% 3.20/0.96                [status(thm)],
% 3.20/0.96                [c_6561,c_33,c_1193]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_6925,plain,
% 3.20/0.96      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49))
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top
% 3.20/0.96      | v1_relat_1(X1_49) != iProver_top ),
% 3.20/0.96      inference(renaming,[status(thm)],[c_6924]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_6933,plain,
% 3.20/0.96      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_49)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_49)
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_1525,c_6925]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_25,negated_conjecture,
% 3.20/0.96      ( v2_funct_1(sK2) ),
% 3.20/0.96      inference(cnf_transformation,[],[f77]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_508,negated_conjecture,
% 3.20/0.96      ( v2_funct_1(sK2) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_25]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_990,plain,
% 3.20/0.96      ( v2_funct_1(sK2) = iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_9,plain,
% 3.20/0.96      ( ~ v2_funct_1(X0)
% 3.20/0.96      | ~ v1_funct_1(X0)
% 3.20/0.96      | ~ v1_relat_1(X0)
% 3.20/0.96      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.20/0.96      inference(cnf_transformation,[],[f86]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_521,plain,
% 3.20/0.96      ( ~ v2_funct_1(X0_49)
% 3.20/0.96      | ~ v1_funct_1(X0_49)
% 3.20/0.96      | ~ v1_relat_1(X0_49)
% 3.20/0.96      | k5_relat_1(k2_funct_1(X0_49),X0_49) = k6_partfun1(k2_relat_1(X0_49)) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_9]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_981,plain,
% 3.20/0.96      ( k5_relat_1(k2_funct_1(X0_49),X0_49) = k6_partfun1(k2_relat_1(X0_49))
% 3.20/0.96      | v2_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v1_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_2243,plain,
% 3.20/0.96      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.20/0.96      | v1_funct_1(sK2) != iProver_top
% 3.20/0.96      | v1_relat_1(sK2) != iProver_top ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_990,c_981]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_15,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.96      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.20/0.96      inference(cnf_transformation,[],[f63]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_516,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.20/0.96      | k2_relset_1(X0_51,X1_51,X0_49) = k2_relat_1(X0_49) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_15]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_985,plain,
% 3.20/0.96      ( k2_relset_1(X0_51,X1_51,X0_49) = k2_relat_1(X0_49)
% 3.20/0.96      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_1943,plain,
% 3.20/0.96      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_993,c_985]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_27,negated_conjecture,
% 3.20/0.96      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.20/0.96      inference(cnf_transformation,[],[f75]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_507,negated_conjecture,
% 3.20/0.96      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_27]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_1948,plain,
% 3.20/0.96      ( k2_relat_1(sK2) = sK1 ),
% 3.20/0.96      inference(light_normalisation,[status(thm)],[c_1943,c_507]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_2256,plain,
% 3.20/0.96      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.20/0.96      | v1_funct_1(sK2) != iProver_top
% 3.20/0.96      | v1_relat_1(sK2) != iProver_top ),
% 3.20/0.96      inference(light_normalisation,[status(thm)],[c_2243,c_1948]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_32,plain,
% 3.20/0.96      ( v1_funct_1(sK2) = iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_2401,plain,
% 3.20/0.96      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 3.20/0.96      inference(global_propositional_subsumption,
% 3.20/0.96                [status(thm)],
% 3.20/0.96                [c_2256,c_32,c_33,c_1193]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_6956,plain,
% 3.20/0.96      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_49)) = k5_relat_1(k6_partfun1(sK1),X0_49)
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top ),
% 3.20/0.96      inference(light_normalisation,[status(thm)],[c_6933,c_2401]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_7003,plain,
% 3.20/0.96      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_1524,c_6956]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_21,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.20/0.96      | ~ v1_funct_1(X0)
% 3.20/0.96      | ~ v1_funct_1(X3)
% 3.20/0.96      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.20/0.96      inference(cnf_transformation,[],[f69]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_512,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.20/0.96      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 3.20/0.96      | ~ v1_funct_1(X0_49)
% 3.20/0.96      | ~ v1_funct_1(X1_49)
% 3.20/0.96      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_49,X0_49) = k5_relat_1(X1_49,X0_49) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_21]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_989,plain,
% 3.20/0.96      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_49,X1_49) = k5_relat_1(X0_49,X1_49)
% 3.20/0.96      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.20/0.96      | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 3.20/0.96      | v1_funct_1(X1_49) != iProver_top
% 3.20/0.96      | v1_funct_1(X0_49) != iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_3383,plain,
% 3.20/0.96      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3)
% 3.20/0.96      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.20/0.96      | v1_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v1_funct_1(sK3) != iProver_top ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_991,c_989]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_29,negated_conjecture,
% 3.20/0.96      ( v1_funct_1(sK3) ),
% 3.20/0.96      inference(cnf_transformation,[],[f73]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_34,plain,
% 3.20/0.96      ( v1_funct_1(sK3) = iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_3771,plain,
% 3.20/0.96      ( v1_funct_1(X0_49) != iProver_top
% 3.20/0.96      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.20/0.96      | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3) ),
% 3.20/0.96      inference(global_propositional_subsumption,
% 3.20/0.96                [status(thm)],
% 3.20/0.96                [c_3383,c_34]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_3772,plain,
% 3.20/0.96      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3)
% 3.20/0.96      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.20/0.96      | v1_funct_1(X0_49) != iProver_top ),
% 3.20/0.96      inference(renaming,[status(thm)],[c_3771]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_3781,plain,
% 3.20/0.96      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.20/0.96      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_993,c_3772]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_17,plain,
% 3.20/0.96      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.20/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.20/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.20/0.96      | X3 = X2 ),
% 3.20/0.96      inference(cnf_transformation,[],[f64]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_26,negated_conjecture,
% 3.20/0.96      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.20/0.96      inference(cnf_transformation,[],[f76]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_327,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.96      | X3 = X0
% 3.20/0.96      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.20/0.96      | k6_partfun1(sK0) != X3
% 3.20/0.96      | sK0 != X2
% 3.20/0.96      | sK0 != X1 ),
% 3.20/0.96      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_328,plain,
% 3.20/0.96      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.96      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.96      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.20/0.96      inference(unflattening,[status(thm)],[c_327]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_20,plain,
% 3.20/0.96      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.20/0.96      inference(cnf_transformation,[],[f68]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_42,plain,
% 3.20/0.96      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.20/0.96      inference(instantiation,[status(thm)],[c_20]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_330,plain,
% 3.20/0.96      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.96      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.20/0.96      inference(global_propositional_subsumption,
% 3.20/0.96                [status(thm)],
% 3.20/0.96                [c_328,c_42]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_501,plain,
% 3.20/0.96      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.96      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_330]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_996,plain,
% 3.20/0.96      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.20/0.96      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_18,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.20/0.96      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.20/0.96      | ~ v1_funct_1(X0)
% 3.20/0.96      | ~ v1_funct_1(X3) ),
% 3.20/0.96      inference(cnf_transformation,[],[f67]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_515,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.20/0.96      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 3.20/0.96      | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 3.20/0.96      | ~ v1_funct_1(X0_49)
% 3.20/0.96      | ~ v1_funct_1(X1_49) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_18]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_1305,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.20/0.96      | m1_subset_1(k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
% 3.20/0.96      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.20/0.96      | ~ v1_funct_1(X0_49)
% 3.20/0.96      | ~ v1_funct_1(sK3) ),
% 3.20/0.96      inference(instantiation,[status(thm)],[c_515]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_1447,plain,
% 3.20/0.96      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.20/0.96      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.20/0.96      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.20/0.96      | ~ v1_funct_1(sK3)
% 3.20/0.96      | ~ v1_funct_1(sK2) ),
% 3.20/0.96      inference(instantiation,[status(thm)],[c_1305]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_1476,plain,
% 3.20/0.96      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.20/0.96      inference(global_propositional_subsumption,
% 3.20/0.96                [status(thm)],
% 3.20/0.96                [c_996,c_31,c_30,c_29,c_28,c_501,c_1447]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_3790,plain,
% 3.20/0.96      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.20/0.96      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.96      inference(light_normalisation,[status(thm)],[c_3781,c_1476]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_4785,plain,
% 3.20/0.96      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.20/0.96      inference(global_propositional_subsumption,
% 3.20/0.96                [status(thm)],
% 3.20/0.96                [c_3790,c_32]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_7017,plain,
% 3.20/0.96      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 3.20/0.96      inference(light_normalisation,[status(thm)],[c_7003,c_4785]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_2,plain,
% 3.20/0.96      ( ~ v1_relat_1(X0)
% 3.20/0.96      | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.20/0.96      inference(cnf_transformation,[],[f81]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_527,plain,
% 3.20/0.96      ( ~ v1_relat_1(X0_49)
% 3.20/0.96      | k5_relat_1(k6_partfun1(X0_51),X0_49) = k7_relat_1(X0_49,X0_51) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_2]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_975,plain,
% 3.20/0.96      ( k5_relat_1(k6_partfun1(X0_51),X0_49) = k7_relat_1(X0_49,X0_51)
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_1584,plain,
% 3.20/0.96      ( k5_relat_1(k6_partfun1(X0_51),sK3) = k7_relat_1(sK3,X0_51) ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_1524,c_975]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_14,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.96      | v4_relat_1(X0,X1) ),
% 3.20/0.96      inference(cnf_transformation,[],[f62]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_0,plain,
% 3.20/0.96      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.20/0.96      inference(cnf_transformation,[],[f48]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_305,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.96      | ~ v1_relat_1(X0)
% 3.20/0.96      | k7_relat_1(X0,X1) = X0 ),
% 3.20/0.96      inference(resolution,[status(thm)],[c_14,c_0]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_309,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.96      | k7_relat_1(X0,X1) = X0 ),
% 3.20/0.96      inference(global_propositional_subsumption,
% 3.20/0.96                [status(thm)],
% 3.20/0.96                [c_305,c_14,c_13,c_0]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_502,plain,
% 3.20/0.96      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.20/0.96      | k7_relat_1(X0_49,X0_51) = X0_49 ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_309]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_995,plain,
% 3.20/0.96      ( k7_relat_1(X0_49,X0_51) = X0_49
% 3.20/0.96      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_2614,plain,
% 3.20/0.96      ( k7_relat_1(sK3,sK1) = sK3 ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_991,c_995]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_2615,plain,
% 3.20/0.96      ( k7_relat_1(sK2,sK0) = sK2 ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_993,c_995]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_7,plain,
% 3.20/0.96      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.20/0.96      inference(cnf_transformation,[],[f84]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_522,plain,
% 3.20/0.96      ( v2_funct_1(k6_partfun1(X0_51)) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_7]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_980,plain,
% 3.20/0.96      ( v2_funct_1(k6_partfun1(X0_51)) = iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_11,plain,
% 3.20/0.96      ( ~ v2_funct_1(X0)
% 3.20/0.96      | ~ v2_funct_1(X1)
% 3.20/0.96      | ~ v1_funct_1(X0)
% 3.20/0.96      | ~ v1_funct_1(X1)
% 3.20/0.96      | ~ v1_relat_1(X1)
% 3.20/0.96      | ~ v1_relat_1(X0)
% 3.20/0.96      | k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ),
% 3.20/0.96      inference(cnf_transformation,[],[f59]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_519,plain,
% 3.20/0.96      ( ~ v2_funct_1(X0_49)
% 3.20/0.96      | ~ v2_funct_1(X1_49)
% 3.20/0.96      | ~ v1_funct_1(X0_49)
% 3.20/0.96      | ~ v1_funct_1(X1_49)
% 3.20/0.96      | ~ v1_relat_1(X1_49)
% 3.20/0.96      | ~ v1_relat_1(X0_49)
% 3.20/0.96      | k5_relat_1(k2_funct_1(X1_49),k2_funct_1(X0_49)) = k2_funct_1(k5_relat_1(X0_49,X1_49)) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_11]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_983,plain,
% 3.20/0.96      ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(X1_49)) = k2_funct_1(k5_relat_1(X1_49,X0_49))
% 3.20/0.96      | v2_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v2_funct_1(X1_49) != iProver_top
% 3.20/0.96      | v1_funct_1(X1_49) != iProver_top
% 3.20/0.96      | v1_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v1_relat_1(X1_49) != iProver_top
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_3532,plain,
% 3.20/0.96      ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(k6_partfun1(X0_51))) = k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49))
% 3.20/0.96      | v2_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v1_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top
% 3.20/0.96      | v1_relat_1(k6_partfun1(X0_51)) != iProver_top ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_980,c_983]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_12,plain,
% 3.20/0.96      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.20/0.96      inference(cnf_transformation,[],[f88]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_518,plain,
% 3.20/0.96      ( k2_funct_1(k6_partfun1(X0_51)) = k6_partfun1(X0_51) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_12]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_3539,plain,
% 3.20/0.96      ( k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49)) = k5_relat_1(k2_funct_1(X0_49),k6_partfun1(X0_51))
% 3.20/0.96      | v2_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v1_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top
% 3.20/0.96      | v1_relat_1(k6_partfun1(X0_51)) != iProver_top ),
% 3.20/0.96      inference(light_normalisation,[status(thm)],[c_3532,c_518]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_5,plain,
% 3.20/0.96      ( v1_funct_1(k6_partfun1(X0)) ),
% 3.20/0.96      inference(cnf_transformation,[],[f82]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_524,plain,
% 3.20/0.96      ( v1_funct_1(k6_partfun1(X0_51)) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_5]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_575,plain,
% 3.20/0.96      ( v1_funct_1(k6_partfun1(X0_51)) = iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_8,plain,
% 3.20/0.96      ( v1_relat_1(k6_partfun1(X0)) ),
% 3.20/0.96      inference(cnf_transformation,[],[f85]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_523,plain,
% 3.20/0.96      ( v1_relat_1(k6_partfun1(X0_51)) ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_8]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_576,plain,
% 3.20/0.96      ( v1_relat_1(k6_partfun1(X0_51)) = iProver_top ),
% 3.20/0.96      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_4641,plain,
% 3.20/0.96      ( v1_relat_1(X0_49) != iProver_top
% 3.20/0.96      | k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49)) = k5_relat_1(k2_funct_1(X0_49),k6_partfun1(X0_51))
% 3.20/0.96      | v2_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v1_funct_1(X0_49) != iProver_top ),
% 3.20/0.96      inference(global_propositional_subsumption,
% 3.20/0.96                [status(thm)],
% 3.20/0.96                [c_3539,c_575,c_576]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_4642,plain,
% 3.20/0.96      ( k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49)) = k5_relat_1(k2_funct_1(X0_49),k6_partfun1(X0_51))
% 3.20/0.96      | v2_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v1_funct_1(X0_49) != iProver_top
% 3.20/0.96      | v1_relat_1(X0_49) != iProver_top ),
% 3.20/0.96      inference(renaming,[status(thm)],[c_4641]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_4651,plain,
% 3.20/0.96      ( k2_funct_1(k5_relat_1(k6_partfun1(X0_51),sK2)) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_51))
% 3.20/0.96      | v1_funct_1(sK2) != iProver_top
% 3.20/0.96      | v1_relat_1(sK2) != iProver_top ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_990,c_4642]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_1588,plain,
% 3.20/0.96      ( k5_relat_1(k6_partfun1(X0_51),sK2) = k7_relat_1(sK2,X0_51) ),
% 3.20/0.96      inference(superposition,[status(thm)],[c_1525,c_975]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_4664,plain,
% 3.20/0.96      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_51)) = k2_funct_1(k7_relat_1(sK2,X0_51))
% 3.20/0.96      | v1_funct_1(sK2) != iProver_top
% 3.20/0.96      | v1_relat_1(sK2) != iProver_top ),
% 3.20/0.96      inference(light_normalisation,[status(thm)],[c_4651,c_1588]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_4805,plain,
% 3.20/0.96      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_51)) = k2_funct_1(k7_relat_1(sK2,X0_51)) ),
% 3.20/0.96      inference(global_propositional_subsumption,
% 3.20/0.96                [status(thm)],
% 3.20/0.96                [c_4664,c_32,c_33,c_1193]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_7018,plain,
% 3.20/0.96      ( k2_funct_1(sK2) = sK3 ),
% 3.20/0.96      inference(demodulation,
% 3.20/0.96                [status(thm)],
% 3.20/0.96                [c_7017,c_1584,c_2614,c_2615,c_4805]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_22,negated_conjecture,
% 3.20/0.96      ( k2_funct_1(sK2) != sK3 ),
% 3.20/0.96      inference(cnf_transformation,[],[f80]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(c_511,negated_conjecture,
% 3.20/0.96      ( k2_funct_1(sK2) != sK3 ),
% 3.20/0.96      inference(subtyping,[status(esa)],[c_22]) ).
% 3.20/0.96  
% 3.20/0.96  cnf(contradiction,plain,
% 3.20/0.96      ( $false ),
% 3.20/0.96      inference(minisat,[status(thm)],[c_7018,c_511]) ).
% 3.20/0.96  
% 3.20/0.96  
% 3.20/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/0.96  
% 3.20/0.96  ------                               Statistics
% 3.20/0.96  
% 3.20/0.96  ------ General
% 3.20/0.96  
% 3.20/0.96  abstr_ref_over_cycles:                  0
% 3.20/0.96  abstr_ref_under_cycles:                 0
% 3.20/0.96  gc_basic_clause_elim:                   0
% 3.20/0.96  forced_gc_time:                         0
% 3.20/0.96  parsing_time:                           0.01
% 3.20/0.96  unif_index_cands_time:                  0.
% 3.20/0.96  unif_index_add_time:                    0.
% 3.20/0.96  orderings_time:                         0.
% 3.20/0.96  out_proof_time:                         0.011
% 3.20/0.96  total_time:                             0.263
% 3.20/0.96  num_of_symbols:                         56
% 3.20/0.96  num_of_terms:                           7841
% 3.20/0.96  
% 3.20/0.96  ------ Preprocessing
% 3.20/0.96  
% 3.20/0.96  num_of_splits:                          0
% 3.20/0.96  num_of_split_atoms:                     0
% 3.20/0.96  num_of_reused_defs:                     0
% 3.20/0.96  num_eq_ax_congr_red:                    14
% 3.20/0.96  num_of_sem_filtered_clauses:            1
% 3.20/0.96  num_of_subtypes:                        4
% 3.20/0.96  monotx_restored_types:                  0
% 3.20/0.96  sat_num_of_epr_types:                   0
% 3.20/0.96  sat_num_of_non_cyclic_types:            0
% 3.20/0.96  sat_guarded_non_collapsed_types:        1
% 3.20/0.96  num_pure_diseq_elim:                    0
% 3.20/0.96  simp_replaced_by:                       0
% 3.20/0.96  res_preprocessed:                       150
% 3.20/0.96  prep_upred:                             0
% 3.20/0.96  prep_unflattend:                        8
% 3.20/0.96  smt_new_axioms:                         0
% 3.20/0.96  pred_elim_cands:                        4
% 3.20/0.96  pred_elim:                              2
% 3.20/0.96  pred_elim_cl:                           3
% 3.20/0.96  pred_elim_cycles:                       4
% 3.20/0.96  merged_defs:                            0
% 3.20/0.96  merged_defs_ncl:                        0
% 3.20/0.96  bin_hyper_res:                          0
% 3.20/0.96  prep_cycles:                            4
% 3.20/0.96  pred_elim_time:                         0.001
% 3.20/0.96  splitting_time:                         0.
% 3.20/0.96  sem_filter_time:                        0.
% 3.20/0.96  monotx_time:                            0.
% 3.20/0.96  subtype_inf_time:                       0.
% 3.20/0.96  
% 3.20/0.96  ------ Problem properties
% 3.20/0.96  
% 3.20/0.96  clauses:                                28
% 3.20/0.96  conjectures:                            9
% 3.20/0.96  epr:                                    5
% 3.20/0.96  horn:                                   28
% 3.20/0.96  ground:                                 10
% 3.20/0.96  unary:                                  14
% 3.20/0.96  binary:                                 5
% 3.20/0.96  lits:                                   64
% 3.20/0.96  lits_eq:                                14
% 3.20/0.96  fd_pure:                                0
% 3.20/0.96  fd_pseudo:                              0
% 3.20/0.96  fd_cond:                                0
% 3.20/0.96  fd_pseudo_cond:                         0
% 3.20/0.96  ac_symbols:                             0
% 3.20/0.96  
% 3.20/0.96  ------ Propositional Solver
% 3.20/0.96  
% 3.20/0.96  prop_solver_calls:                      29
% 3.20/0.96  prop_fast_solver_calls:                 1027
% 3.20/0.96  smt_solver_calls:                       0
% 3.20/0.96  smt_fast_solver_calls:                  0
% 3.20/0.96  prop_num_of_clauses:                    3100
% 3.20/0.96  prop_preprocess_simplified:             6908
% 3.20/0.96  prop_fo_subsumed:                       60
% 3.20/0.96  prop_solver_time:                       0.
% 3.20/0.96  smt_solver_time:                        0.
% 3.20/0.96  smt_fast_solver_time:                   0.
% 3.20/0.96  prop_fast_solver_time:                  0.
% 3.20/0.96  prop_unsat_core_time:                   0.
% 3.20/0.96  
% 3.20/0.96  ------ QBF
% 3.20/0.96  
% 3.20/0.96  qbf_q_res:                              0
% 3.20/0.96  qbf_num_tautologies:                    0
% 3.20/0.96  qbf_prep_cycles:                        0
% 3.20/0.96  
% 3.20/0.96  ------ BMC1
% 3.20/0.96  
% 3.20/0.96  bmc1_current_bound:                     -1
% 3.20/0.96  bmc1_last_solved_bound:                 -1
% 3.20/0.96  bmc1_unsat_core_size:                   -1
% 3.20/0.96  bmc1_unsat_core_parents_size:           -1
% 3.20/0.96  bmc1_merge_next_fun:                    0
% 3.20/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.20/0.96  
% 3.20/0.96  ------ Instantiation
% 3.20/0.96  
% 3.20/0.96  inst_num_of_clauses:                    822
% 3.20/0.96  inst_num_in_passive:                    284
% 3.20/0.96  inst_num_in_active:                     508
% 3.20/0.96  inst_num_in_unprocessed:                30
% 3.20/0.96  inst_num_of_loops:                      540
% 3.20/0.96  inst_num_of_learning_restarts:          0
% 3.20/0.96  inst_num_moves_active_passive:          29
% 3.20/0.96  inst_lit_activity:                      0
% 3.20/0.96  inst_lit_activity_moves:                1
% 3.20/0.96  inst_num_tautologies:                   0
% 3.20/0.96  inst_num_prop_implied:                  0
% 3.20/0.96  inst_num_existing_simplified:           0
% 3.20/0.96  inst_num_eq_res_simplified:             0
% 3.20/0.96  inst_num_child_elim:                    0
% 3.20/0.96  inst_num_of_dismatching_blockings:      197
% 3.20/0.96  inst_num_of_non_proper_insts:           389
% 3.20/0.96  inst_num_of_duplicates:                 0
% 3.20/0.96  inst_inst_num_from_inst_to_res:         0
% 3.20/0.96  inst_dismatching_checking_time:         0.
% 3.20/0.96  
% 3.20/0.96  ------ Resolution
% 3.20/0.96  
% 3.20/0.96  res_num_of_clauses:                     0
% 3.20/0.96  res_num_in_passive:                     0
% 3.20/0.96  res_num_in_active:                      0
% 3.20/0.96  res_num_of_loops:                       154
% 3.20/0.96  res_forward_subset_subsumed:            29
% 3.20/0.96  res_backward_subset_subsumed:           0
% 3.20/0.96  res_forward_subsumed:                   0
% 3.20/0.96  res_backward_subsumed:                  0
% 3.20/0.96  res_forward_subsumption_resolution:     0
% 3.20/0.96  res_backward_subsumption_resolution:    0
% 3.20/0.96  res_clause_to_clause_subsumption:       463
% 3.20/0.96  res_orphan_elimination:                 0
% 3.20/0.96  res_tautology_del:                      18
% 3.20/0.96  res_num_eq_res_simplified:              0
% 3.20/0.96  res_num_sel_changes:                    0
% 3.20/0.96  res_moves_from_active_to_pass:          0
% 3.20/0.96  
% 3.20/0.96  ------ Superposition
% 3.20/0.96  
% 3.20/0.96  sup_time_total:                         0.
% 3.20/0.96  sup_time_generating:                    0.
% 3.20/0.96  sup_time_sim_full:                      0.
% 3.20/0.96  sup_time_sim_immed:                     0.
% 3.20/0.96  
% 3.20/0.96  sup_num_of_clauses:                     250
% 3.20/0.96  sup_num_in_active:                      106
% 3.20/0.96  sup_num_in_passive:                     144
% 3.20/0.96  sup_num_of_loops:                       106
% 3.20/0.96  sup_fw_superposition:                   160
% 3.20/0.96  sup_bw_superposition:                   128
% 3.20/0.96  sup_immediate_simplified:               108
% 3.20/0.96  sup_given_eliminated:                   1
% 3.20/0.96  comparisons_done:                       0
% 3.20/0.96  comparisons_avoided:                    0
% 3.20/0.96  
% 3.20/0.96  ------ Simplifications
% 3.20/0.96  
% 3.20/0.96  
% 3.20/0.96  sim_fw_subset_subsumed:                 3
% 3.20/0.96  sim_bw_subset_subsumed:                 5
% 3.20/0.96  sim_fw_subsumed:                        14
% 3.20/0.96  sim_bw_subsumed:                        0
% 3.20/0.96  sim_fw_subsumption_res:                 1
% 3.20/0.96  sim_bw_subsumption_res:                 0
% 3.20/0.96  sim_tautology_del:                      3
% 3.20/0.96  sim_eq_tautology_del:                   8
% 3.20/0.96  sim_eq_res_simp:                        0
% 3.20/0.96  sim_fw_demodulated:                     12
% 3.20/0.96  sim_bw_demodulated:                     5
% 3.20/0.96  sim_light_normalised:                   90
% 3.20/0.96  sim_joinable_taut:                      0
% 3.20/0.96  sim_joinable_simp:                      0
% 3.20/0.96  sim_ac_normalised:                      0
% 3.20/0.96  sim_smt_subsumption:                    0
% 3.20/0.96  
%------------------------------------------------------------------------------
