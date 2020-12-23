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
% DateTime   : Thu Dec  3 12:03:16 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 999 expanded)
%              Number of clauses        :  115 ( 261 expanded)
%              Number of leaves         :   20 ( 266 expanded)
%              Depth                    :   18
%              Number of atoms          :  817 (8825 expanded)
%              Number of equality atoms :  380 (3215 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f64,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f44,f43])).

fof(f78,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f85,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f49,f63])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f67,plain,(
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

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f52,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f83,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f63])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f25])).

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
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f55,f63])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f82,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f51,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f84,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_17,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_394,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

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

cnf(c_478,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_395])).

cnf(c_1128,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_1670,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1128])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_40,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1839,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1670,c_36,c_37,c_38,c_39,c_40,c_41])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1139,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3716,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_1139])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_646,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_677,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_646])).

cnf(c_647,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1238,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_1239,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1238])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4858,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4859,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4858])).

cnf(c_12,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_382,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_390,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_382,c_15])).

cnf(c_1129,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1240,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1832,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1129,c_35,c_33,c_32,c_30,c_390,c_1240])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_1143,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4854,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_1143])).

cnf(c_5031,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4854,c_36,c_37,c_38])).

cnf(c_5032,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5031])).

cnf(c_5035,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1832,c_5032])).

cnf(c_10702,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3716,c_39,c_40,c_41,c_26,c_677,c_1239,c_4859,c_5035])).

cnf(c_5038,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5035,c_39,c_40,c_41,c_26,c_677,c_1239,c_4859])).

cnf(c_1135,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1153,plain,
    ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2114,plain,
    ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1135,c_1153])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1285,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1656,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1285])).

cnf(c_1657,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1656])).

cnf(c_2858,plain,
    ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2114,c_41,c_1657])).

cnf(c_5042,plain,
    ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5038,c_2858])).

cnf(c_10705,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_10702,c_5042])).

cnf(c_0,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_10706,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_10705,c_0])).

cnf(c_1134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1137,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1145,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2806,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_1145])).

cnf(c_2931,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2806,c_39])).

cnf(c_2932,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2931])).

cnf(c_2940,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1134,c_2932])).

cnf(c_2941,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2940,c_1832])).

cnf(c_3709,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2941,c_36])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v2_funct_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_191,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_4])).

cnf(c_192,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_1131,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_3712,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3709,c_1131])).

cnf(c_24,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1758,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1759,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1758])).

cnf(c_10242,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3712,c_36,c_38,c_39,c_41,c_24,c_1657,c_1759])).

cnf(c_3715,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_1139])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1203,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1331,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1203])).

cnf(c_1555,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_3842,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3715,c_35,c_34,c_33,c_29,c_27,c_25,c_1555])).

cnf(c_1132,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1152,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2110,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1152])).

cnf(c_43,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2668,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2110,c_38,c_43,c_1759])).

cnf(c_3845,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3842,c_2668])).

cnf(c_1,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3846,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_3845,c_1])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1140,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3987,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_1140])).

cnf(c_1202,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1301,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1202])).

cnf(c_1534,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1301])).

cnf(c_3992,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3987,c_35,c_34,c_33,c_29,c_27,c_25,c_1534])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1150,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2066,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1150])).

cnf(c_2299,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2066,c_38,c_43,c_1759])).

cnf(c_3995,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3992,c_2299])).

cnf(c_3996,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_3995,c_1])).

cnf(c_10244,plain,
    ( k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_10242,c_3846,c_3996])).

cnf(c_10245,plain,
    ( k1_relat_1(sK3) != sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_10244])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10706,c_10245])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:00:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 4.11/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.00  
% 4.11/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.11/1.00  
% 4.11/1.00  ------  iProver source info
% 4.11/1.00  
% 4.11/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.11/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.11/1.00  git: non_committed_changes: false
% 4.11/1.00  git: last_make_outside_of_git: false
% 4.11/1.00  
% 4.11/1.00  ------ 
% 4.11/1.00  
% 4.11/1.00  ------ Input Options
% 4.11/1.00  
% 4.11/1.00  --out_options                           all
% 4.11/1.00  --tptp_safe_out                         true
% 4.11/1.00  --problem_path                          ""
% 4.11/1.00  --include_path                          ""
% 4.11/1.00  --clausifier                            res/vclausify_rel
% 4.11/1.00  --clausifier_options                    ""
% 4.11/1.00  --stdin                                 false
% 4.11/1.00  --stats_out                             all
% 4.11/1.00  
% 4.11/1.00  ------ General Options
% 4.11/1.00  
% 4.11/1.00  --fof                                   false
% 4.11/1.00  --time_out_real                         305.
% 4.11/1.00  --time_out_virtual                      -1.
% 4.11/1.00  --symbol_type_check                     false
% 4.11/1.00  --clausify_out                          false
% 4.11/1.00  --sig_cnt_out                           false
% 4.11/1.00  --trig_cnt_out                          false
% 4.11/1.00  --trig_cnt_out_tolerance                1.
% 4.11/1.00  --trig_cnt_out_sk_spl                   false
% 4.11/1.00  --abstr_cl_out                          false
% 4.11/1.00  
% 4.11/1.00  ------ Global Options
% 4.11/1.00  
% 4.11/1.00  --schedule                              default
% 4.11/1.00  --add_important_lit                     false
% 4.11/1.00  --prop_solver_per_cl                    1000
% 4.11/1.00  --min_unsat_core                        false
% 4.11/1.00  --soft_assumptions                      false
% 4.11/1.00  --soft_lemma_size                       3
% 4.11/1.00  --prop_impl_unit_size                   0
% 4.11/1.00  --prop_impl_unit                        []
% 4.11/1.00  --share_sel_clauses                     true
% 4.11/1.00  --reset_solvers                         false
% 4.11/1.00  --bc_imp_inh                            [conj_cone]
% 4.11/1.00  --conj_cone_tolerance                   3.
% 4.11/1.00  --extra_neg_conj                        none
% 4.11/1.00  --large_theory_mode                     true
% 4.11/1.00  --prolific_symb_bound                   200
% 4.11/1.00  --lt_threshold                          2000
% 4.11/1.00  --clause_weak_htbl                      true
% 4.11/1.00  --gc_record_bc_elim                     false
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing Options
% 4.11/1.00  
% 4.11/1.00  --preprocessing_flag                    true
% 4.11/1.00  --time_out_prep_mult                    0.1
% 4.11/1.00  --splitting_mode                        input
% 4.11/1.00  --splitting_grd                         true
% 4.11/1.00  --splitting_cvd                         false
% 4.11/1.00  --splitting_cvd_svl                     false
% 4.11/1.00  --splitting_nvd                         32
% 4.11/1.00  --sub_typing                            true
% 4.11/1.00  --prep_gs_sim                           true
% 4.11/1.00  --prep_unflatten                        true
% 4.11/1.00  --prep_res_sim                          true
% 4.11/1.00  --prep_upred                            true
% 4.11/1.00  --prep_sem_filter                       exhaustive
% 4.11/1.00  --prep_sem_filter_out                   false
% 4.11/1.00  --pred_elim                             true
% 4.11/1.00  --res_sim_input                         true
% 4.11/1.00  --eq_ax_congr_red                       true
% 4.11/1.00  --pure_diseq_elim                       true
% 4.11/1.00  --brand_transform                       false
% 4.11/1.00  --non_eq_to_eq                          false
% 4.11/1.00  --prep_def_merge                        true
% 4.11/1.00  --prep_def_merge_prop_impl              false
% 4.11/1.00  --prep_def_merge_mbd                    true
% 4.11/1.00  --prep_def_merge_tr_red                 false
% 4.11/1.00  --prep_def_merge_tr_cl                  false
% 4.11/1.00  --smt_preprocessing                     true
% 4.11/1.00  --smt_ac_axioms                         fast
% 4.11/1.00  --preprocessed_out                      false
% 4.11/1.00  --preprocessed_stats                    false
% 4.11/1.00  
% 4.11/1.00  ------ Abstraction refinement Options
% 4.11/1.00  
% 4.11/1.00  --abstr_ref                             []
% 4.11/1.00  --abstr_ref_prep                        false
% 4.11/1.00  --abstr_ref_until_sat                   false
% 4.11/1.00  --abstr_ref_sig_restrict                funpre
% 4.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/1.00  --abstr_ref_under                       []
% 4.11/1.00  
% 4.11/1.00  ------ SAT Options
% 4.11/1.00  
% 4.11/1.00  --sat_mode                              false
% 4.11/1.00  --sat_fm_restart_options                ""
% 4.11/1.00  --sat_gr_def                            false
% 4.11/1.00  --sat_epr_types                         true
% 4.11/1.00  --sat_non_cyclic_types                  false
% 4.11/1.00  --sat_finite_models                     false
% 4.11/1.00  --sat_fm_lemmas                         false
% 4.11/1.00  --sat_fm_prep                           false
% 4.11/1.00  --sat_fm_uc_incr                        true
% 4.11/1.00  --sat_out_model                         small
% 4.11/1.00  --sat_out_clauses                       false
% 4.11/1.00  
% 4.11/1.00  ------ QBF Options
% 4.11/1.00  
% 4.11/1.00  --qbf_mode                              false
% 4.11/1.00  --qbf_elim_univ                         false
% 4.11/1.00  --qbf_dom_inst                          none
% 4.11/1.00  --qbf_dom_pre_inst                      false
% 4.11/1.00  --qbf_sk_in                             false
% 4.11/1.00  --qbf_pred_elim                         true
% 4.11/1.00  --qbf_split                             512
% 4.11/1.00  
% 4.11/1.00  ------ BMC1 Options
% 4.11/1.00  
% 4.11/1.00  --bmc1_incremental                      false
% 4.11/1.00  --bmc1_axioms                           reachable_all
% 4.11/1.00  --bmc1_min_bound                        0
% 4.11/1.00  --bmc1_max_bound                        -1
% 4.11/1.00  --bmc1_max_bound_default                -1
% 4.11/1.00  --bmc1_symbol_reachability              true
% 4.11/1.00  --bmc1_property_lemmas                  false
% 4.11/1.00  --bmc1_k_induction                      false
% 4.11/1.00  --bmc1_non_equiv_states                 false
% 4.11/1.00  --bmc1_deadlock                         false
% 4.11/1.00  --bmc1_ucm                              false
% 4.11/1.00  --bmc1_add_unsat_core                   none
% 4.11/1.00  --bmc1_unsat_core_children              false
% 4.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/1.00  --bmc1_out_stat                         full
% 4.11/1.00  --bmc1_ground_init                      false
% 4.11/1.00  --bmc1_pre_inst_next_state              false
% 4.11/1.00  --bmc1_pre_inst_state                   false
% 4.11/1.00  --bmc1_pre_inst_reach_state             false
% 4.11/1.00  --bmc1_out_unsat_core                   false
% 4.11/1.00  --bmc1_aig_witness_out                  false
% 4.11/1.00  --bmc1_verbose                          false
% 4.11/1.00  --bmc1_dump_clauses_tptp                false
% 4.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.11/1.00  --bmc1_dump_file                        -
% 4.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.11/1.00  --bmc1_ucm_extend_mode                  1
% 4.11/1.00  --bmc1_ucm_init_mode                    2
% 4.11/1.00  --bmc1_ucm_cone_mode                    none
% 4.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.11/1.00  --bmc1_ucm_relax_model                  4
% 4.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/1.00  --bmc1_ucm_layered_model                none
% 4.11/1.00  --bmc1_ucm_max_lemma_size               10
% 4.11/1.00  
% 4.11/1.00  ------ AIG Options
% 4.11/1.00  
% 4.11/1.00  --aig_mode                              false
% 4.11/1.00  
% 4.11/1.00  ------ Instantiation Options
% 4.11/1.00  
% 4.11/1.00  --instantiation_flag                    true
% 4.11/1.00  --inst_sos_flag                         true
% 4.11/1.00  --inst_sos_phase                        true
% 4.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/1.00  --inst_lit_sel_side                     num_symb
% 4.11/1.00  --inst_solver_per_active                1400
% 4.11/1.00  --inst_solver_calls_frac                1.
% 4.11/1.00  --inst_passive_queue_type               priority_queues
% 4.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/1.00  --inst_passive_queues_freq              [25;2]
% 4.11/1.00  --inst_dismatching                      true
% 4.11/1.00  --inst_eager_unprocessed_to_passive     true
% 4.11/1.00  --inst_prop_sim_given                   true
% 4.11/1.00  --inst_prop_sim_new                     false
% 4.11/1.00  --inst_subs_new                         false
% 4.11/1.00  --inst_eq_res_simp                      false
% 4.11/1.00  --inst_subs_given                       false
% 4.11/1.00  --inst_orphan_elimination               true
% 4.11/1.00  --inst_learning_loop_flag               true
% 4.11/1.00  --inst_learning_start                   3000
% 4.11/1.00  --inst_learning_factor                  2
% 4.11/1.00  --inst_start_prop_sim_after_learn       3
% 4.11/1.00  --inst_sel_renew                        solver
% 4.11/1.00  --inst_lit_activity_flag                true
% 4.11/1.00  --inst_restr_to_given                   false
% 4.11/1.00  --inst_activity_threshold               500
% 4.11/1.00  --inst_out_proof                        true
% 4.11/1.00  
% 4.11/1.00  ------ Resolution Options
% 4.11/1.00  
% 4.11/1.00  --resolution_flag                       true
% 4.11/1.00  --res_lit_sel                           adaptive
% 4.11/1.00  --res_lit_sel_side                      none
% 4.11/1.00  --res_ordering                          kbo
% 4.11/1.00  --res_to_prop_solver                    active
% 4.11/1.00  --res_prop_simpl_new                    false
% 4.11/1.00  --res_prop_simpl_given                  true
% 4.11/1.00  --res_passive_queue_type                priority_queues
% 4.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/1.00  --res_passive_queues_freq               [15;5]
% 4.11/1.00  --res_forward_subs                      full
% 4.11/1.00  --res_backward_subs                     full
% 4.11/1.00  --res_forward_subs_resolution           true
% 4.11/1.00  --res_backward_subs_resolution          true
% 4.11/1.00  --res_orphan_elimination                true
% 4.11/1.00  --res_time_limit                        2.
% 4.11/1.00  --res_out_proof                         true
% 4.11/1.00  
% 4.11/1.00  ------ Superposition Options
% 4.11/1.00  
% 4.11/1.00  --superposition_flag                    true
% 4.11/1.00  --sup_passive_queue_type                priority_queues
% 4.11/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.11/1.00  --demod_completeness_check              fast
% 4.11/1.00  --demod_use_ground                      true
% 4.11/1.00  --sup_to_prop_solver                    passive
% 4.11/1.00  --sup_prop_simpl_new                    true
% 4.11/1.00  --sup_prop_simpl_given                  true
% 4.11/1.00  --sup_fun_splitting                     true
% 4.11/1.00  --sup_smt_interval                      50000
% 4.11/1.00  
% 4.11/1.00  ------ Superposition Simplification Setup
% 4.11/1.00  
% 4.11/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.11/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.11/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.11/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.11/1.00  --sup_immed_triv                        [TrivRules]
% 4.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/1.00  --sup_immed_bw_main                     []
% 4.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/1.00  --sup_input_bw                          []
% 4.11/1.00  
% 4.11/1.00  ------ Combination Options
% 4.11/1.00  
% 4.11/1.00  --comb_res_mult                         3
% 4.11/1.00  --comb_sup_mult                         2
% 4.11/1.00  --comb_inst_mult                        10
% 4.11/1.00  
% 4.11/1.00  ------ Debug Options
% 4.11/1.00  
% 4.11/1.00  --dbg_backtrace                         false
% 4.11/1.00  --dbg_dump_prop_clauses                 false
% 4.11/1.00  --dbg_dump_prop_clauses_file            -
% 4.11/1.00  --dbg_out_stat                          false
% 4.11/1.00  ------ Parsing...
% 4.11/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.11/1.00  ------ Proving...
% 4.11/1.00  ------ Problem Properties 
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  clauses                                 35
% 4.11/1.00  conjectures                             11
% 4.11/1.00  EPR                                     7
% 4.11/1.00  Horn                                    31
% 4.11/1.00  unary                                   16
% 4.11/1.00  binary                                  2
% 4.11/1.00  lits                                    132
% 4.11/1.00  lits eq                                 32
% 4.11/1.00  fd_pure                                 0
% 4.11/1.00  fd_pseudo                               0
% 4.11/1.00  fd_cond                                 4
% 4.11/1.00  fd_pseudo_cond                          1
% 4.11/1.00  AC symbols                              0
% 4.11/1.00  
% 4.11/1.00  ------ Schedule dynamic 5 is on 
% 4.11/1.00  
% 4.11/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  ------ 
% 4.11/1.00  Current options:
% 4.11/1.00  ------ 
% 4.11/1.00  
% 4.11/1.00  ------ Input Options
% 4.11/1.00  
% 4.11/1.00  --out_options                           all
% 4.11/1.00  --tptp_safe_out                         true
% 4.11/1.00  --problem_path                          ""
% 4.11/1.00  --include_path                          ""
% 4.11/1.00  --clausifier                            res/vclausify_rel
% 4.11/1.00  --clausifier_options                    ""
% 4.11/1.00  --stdin                                 false
% 4.11/1.00  --stats_out                             all
% 4.11/1.00  
% 4.11/1.00  ------ General Options
% 4.11/1.00  
% 4.11/1.00  --fof                                   false
% 4.11/1.00  --time_out_real                         305.
% 4.11/1.00  --time_out_virtual                      -1.
% 4.11/1.00  --symbol_type_check                     false
% 4.11/1.00  --clausify_out                          false
% 4.11/1.00  --sig_cnt_out                           false
% 4.11/1.00  --trig_cnt_out                          false
% 4.11/1.00  --trig_cnt_out_tolerance                1.
% 4.11/1.00  --trig_cnt_out_sk_spl                   false
% 4.11/1.00  --abstr_cl_out                          false
% 4.11/1.00  
% 4.11/1.00  ------ Global Options
% 4.11/1.00  
% 4.11/1.00  --schedule                              default
% 4.11/1.00  --add_important_lit                     false
% 4.11/1.00  --prop_solver_per_cl                    1000
% 4.11/1.00  --min_unsat_core                        false
% 4.11/1.00  --soft_assumptions                      false
% 4.11/1.00  --soft_lemma_size                       3
% 4.11/1.00  --prop_impl_unit_size                   0
% 4.11/1.00  --prop_impl_unit                        []
% 4.11/1.00  --share_sel_clauses                     true
% 4.11/1.00  --reset_solvers                         false
% 4.11/1.00  --bc_imp_inh                            [conj_cone]
% 4.11/1.00  --conj_cone_tolerance                   3.
% 4.11/1.00  --extra_neg_conj                        none
% 4.11/1.00  --large_theory_mode                     true
% 4.11/1.00  --prolific_symb_bound                   200
% 4.11/1.00  --lt_threshold                          2000
% 4.11/1.00  --clause_weak_htbl                      true
% 4.11/1.00  --gc_record_bc_elim                     false
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing Options
% 4.11/1.00  
% 4.11/1.00  --preprocessing_flag                    true
% 4.11/1.00  --time_out_prep_mult                    0.1
% 4.11/1.00  --splitting_mode                        input
% 4.11/1.00  --splitting_grd                         true
% 4.11/1.00  --splitting_cvd                         false
% 4.11/1.00  --splitting_cvd_svl                     false
% 4.11/1.00  --splitting_nvd                         32
% 4.11/1.00  --sub_typing                            true
% 4.11/1.00  --prep_gs_sim                           true
% 4.11/1.00  --prep_unflatten                        true
% 4.11/1.00  --prep_res_sim                          true
% 4.11/1.00  --prep_upred                            true
% 4.11/1.00  --prep_sem_filter                       exhaustive
% 4.11/1.00  --prep_sem_filter_out                   false
% 4.11/1.00  --pred_elim                             true
% 4.11/1.00  --res_sim_input                         true
% 4.11/1.00  --eq_ax_congr_red                       true
% 4.11/1.00  --pure_diseq_elim                       true
% 4.11/1.00  --brand_transform                       false
% 4.11/1.00  --non_eq_to_eq                          false
% 4.11/1.00  --prep_def_merge                        true
% 4.11/1.00  --prep_def_merge_prop_impl              false
% 4.11/1.00  --prep_def_merge_mbd                    true
% 4.11/1.00  --prep_def_merge_tr_red                 false
% 4.11/1.00  --prep_def_merge_tr_cl                  false
% 4.11/1.00  --smt_preprocessing                     true
% 4.11/1.00  --smt_ac_axioms                         fast
% 4.11/1.00  --preprocessed_out                      false
% 4.11/1.00  --preprocessed_stats                    false
% 4.11/1.00  
% 4.11/1.00  ------ Abstraction refinement Options
% 4.11/1.00  
% 4.11/1.00  --abstr_ref                             []
% 4.11/1.00  --abstr_ref_prep                        false
% 4.11/1.00  --abstr_ref_until_sat                   false
% 4.11/1.00  --abstr_ref_sig_restrict                funpre
% 4.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/1.00  --abstr_ref_under                       []
% 4.11/1.00  
% 4.11/1.00  ------ SAT Options
% 4.11/1.00  
% 4.11/1.00  --sat_mode                              false
% 4.11/1.00  --sat_fm_restart_options                ""
% 4.11/1.00  --sat_gr_def                            false
% 4.11/1.00  --sat_epr_types                         true
% 4.11/1.00  --sat_non_cyclic_types                  false
% 4.11/1.00  --sat_finite_models                     false
% 4.11/1.00  --sat_fm_lemmas                         false
% 4.11/1.00  --sat_fm_prep                           false
% 4.11/1.00  --sat_fm_uc_incr                        true
% 4.11/1.00  --sat_out_model                         small
% 4.11/1.00  --sat_out_clauses                       false
% 4.11/1.00  
% 4.11/1.00  ------ QBF Options
% 4.11/1.00  
% 4.11/1.00  --qbf_mode                              false
% 4.11/1.00  --qbf_elim_univ                         false
% 4.11/1.00  --qbf_dom_inst                          none
% 4.11/1.00  --qbf_dom_pre_inst                      false
% 4.11/1.00  --qbf_sk_in                             false
% 4.11/1.00  --qbf_pred_elim                         true
% 4.11/1.00  --qbf_split                             512
% 4.11/1.00  
% 4.11/1.00  ------ BMC1 Options
% 4.11/1.00  
% 4.11/1.00  --bmc1_incremental                      false
% 4.11/1.00  --bmc1_axioms                           reachable_all
% 4.11/1.00  --bmc1_min_bound                        0
% 4.11/1.00  --bmc1_max_bound                        -1
% 4.11/1.00  --bmc1_max_bound_default                -1
% 4.11/1.00  --bmc1_symbol_reachability              true
% 4.11/1.00  --bmc1_property_lemmas                  false
% 4.11/1.00  --bmc1_k_induction                      false
% 4.11/1.00  --bmc1_non_equiv_states                 false
% 4.11/1.00  --bmc1_deadlock                         false
% 4.11/1.00  --bmc1_ucm                              false
% 4.11/1.00  --bmc1_add_unsat_core                   none
% 4.11/1.00  --bmc1_unsat_core_children              false
% 4.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/1.00  --bmc1_out_stat                         full
% 4.11/1.00  --bmc1_ground_init                      false
% 4.11/1.00  --bmc1_pre_inst_next_state              false
% 4.11/1.00  --bmc1_pre_inst_state                   false
% 4.11/1.00  --bmc1_pre_inst_reach_state             false
% 4.11/1.00  --bmc1_out_unsat_core                   false
% 4.11/1.00  --bmc1_aig_witness_out                  false
% 4.11/1.00  --bmc1_verbose                          false
% 4.11/1.00  --bmc1_dump_clauses_tptp                false
% 4.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.11/1.00  --bmc1_dump_file                        -
% 4.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.11/1.00  --bmc1_ucm_extend_mode                  1
% 4.11/1.00  --bmc1_ucm_init_mode                    2
% 4.11/1.00  --bmc1_ucm_cone_mode                    none
% 4.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.11/1.00  --bmc1_ucm_relax_model                  4
% 4.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/1.00  --bmc1_ucm_layered_model                none
% 4.11/1.00  --bmc1_ucm_max_lemma_size               10
% 4.11/1.00  
% 4.11/1.00  ------ AIG Options
% 4.11/1.00  
% 4.11/1.00  --aig_mode                              false
% 4.11/1.00  
% 4.11/1.00  ------ Instantiation Options
% 4.11/1.00  
% 4.11/1.00  --instantiation_flag                    true
% 4.11/1.00  --inst_sos_flag                         true
% 4.11/1.00  --inst_sos_phase                        true
% 4.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/1.00  --inst_lit_sel_side                     none
% 4.11/1.00  --inst_solver_per_active                1400
% 4.11/1.00  --inst_solver_calls_frac                1.
% 4.11/1.00  --inst_passive_queue_type               priority_queues
% 4.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/1.00  --inst_passive_queues_freq              [25;2]
% 4.11/1.00  --inst_dismatching                      true
% 4.11/1.00  --inst_eager_unprocessed_to_passive     true
% 4.11/1.00  --inst_prop_sim_given                   true
% 4.11/1.00  --inst_prop_sim_new                     false
% 4.11/1.00  --inst_subs_new                         false
% 4.11/1.00  --inst_eq_res_simp                      false
% 4.11/1.00  --inst_subs_given                       false
% 4.11/1.00  --inst_orphan_elimination               true
% 4.11/1.00  --inst_learning_loop_flag               true
% 4.11/1.00  --inst_learning_start                   3000
% 4.11/1.00  --inst_learning_factor                  2
% 4.11/1.00  --inst_start_prop_sim_after_learn       3
% 4.11/1.00  --inst_sel_renew                        solver
% 4.11/1.00  --inst_lit_activity_flag                true
% 4.11/1.00  --inst_restr_to_given                   false
% 4.11/1.00  --inst_activity_threshold               500
% 4.11/1.00  --inst_out_proof                        true
% 4.11/1.00  
% 4.11/1.00  ------ Resolution Options
% 4.11/1.00  
% 4.11/1.00  --resolution_flag                       false
% 4.11/1.00  --res_lit_sel                           adaptive
% 4.11/1.00  --res_lit_sel_side                      none
% 4.11/1.00  --res_ordering                          kbo
% 4.11/1.00  --res_to_prop_solver                    active
% 4.11/1.00  --res_prop_simpl_new                    false
% 4.11/1.00  --res_prop_simpl_given                  true
% 4.11/1.00  --res_passive_queue_type                priority_queues
% 4.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/1.00  --res_passive_queues_freq               [15;5]
% 4.11/1.00  --res_forward_subs                      full
% 4.11/1.00  --res_backward_subs                     full
% 4.11/1.00  --res_forward_subs_resolution           true
% 4.11/1.00  --res_backward_subs_resolution          true
% 4.11/1.00  --res_orphan_elimination                true
% 4.11/1.00  --res_time_limit                        2.
% 4.11/1.00  --res_out_proof                         true
% 4.11/1.00  
% 4.11/1.00  ------ Superposition Options
% 4.11/1.00  
% 4.11/1.00  --superposition_flag                    true
% 4.11/1.00  --sup_passive_queue_type                priority_queues
% 4.11/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.11/1.00  --demod_completeness_check              fast
% 4.11/1.00  --demod_use_ground                      true
% 4.11/1.00  --sup_to_prop_solver                    passive
% 4.11/1.00  --sup_prop_simpl_new                    true
% 4.11/1.00  --sup_prop_simpl_given                  true
% 4.11/1.00  --sup_fun_splitting                     true
% 4.11/1.00  --sup_smt_interval                      50000
% 4.11/1.00  
% 4.11/1.00  ------ Superposition Simplification Setup
% 4.11/1.00  
% 4.11/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.11/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.11/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.11/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.11/1.00  --sup_immed_triv                        [TrivRules]
% 4.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/1.00  --sup_immed_bw_main                     []
% 4.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/1.00  --sup_input_bw                          []
% 4.11/1.00  
% 4.11/1.00  ------ Combination Options
% 4.11/1.00  
% 4.11/1.00  --comb_res_mult                         3
% 4.11/1.00  --comb_sup_mult                         2
% 4.11/1.00  --comb_inst_mult                        10
% 4.11/1.00  
% 4.11/1.00  ------ Debug Options
% 4.11/1.00  
% 4.11/1.00  --dbg_backtrace                         false
% 4.11/1.00  --dbg_dump_prop_clauses                 false
% 4.11/1.00  --dbg_dump_prop_clauses_file            -
% 4.11/1.00  --dbg_out_stat                          false
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  ------ Proving...
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  % SZS status Theorem for theBenchmark.p
% 4.11/1.00  
% 4.11/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.11/1.00  
% 4.11/1.00  fof(f13,axiom,(
% 4.11/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f34,plain,(
% 4.11/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.11/1.00    inference(ennf_transformation,[],[f13])).
% 4.11/1.00  
% 4.11/1.00  fof(f35,plain,(
% 4.11/1.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.11/1.00    inference(flattening,[],[f34])).
% 4.11/1.00  
% 4.11/1.00  fof(f64,plain,(
% 4.11/1.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f35])).
% 4.11/1.00  
% 4.11/1.00  fof(f16,conjecture,(
% 4.11/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f17,negated_conjecture,(
% 4.11/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 4.11/1.00    inference(negated_conjecture,[],[f16])).
% 4.11/1.00  
% 4.11/1.00  fof(f40,plain,(
% 4.11/1.00    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 4.11/1.00    inference(ennf_transformation,[],[f17])).
% 4.11/1.00  
% 4.11/1.00  fof(f41,plain,(
% 4.11/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 4.11/1.00    inference(flattening,[],[f40])).
% 4.11/1.00  
% 4.11/1.00  fof(f44,plain,(
% 4.11/1.00    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f43,plain,(
% 4.11/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f45,plain,(
% 4.11/1.00    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 4.11/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f44,f43])).
% 4.11/1.00  
% 4.11/1.00  fof(f78,plain,(
% 4.11/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 4.11/1.00    inference(cnf_transformation,[],[f45])).
% 4.11/1.00  
% 4.11/1.00  fof(f71,plain,(
% 4.11/1.00    v1_funct_1(sK2)),
% 4.11/1.00    inference(cnf_transformation,[],[f45])).
% 4.11/1.00  
% 4.11/1.00  fof(f72,plain,(
% 4.11/1.00    v1_funct_2(sK2,sK0,sK1)),
% 4.11/1.00    inference(cnf_transformation,[],[f45])).
% 4.11/1.00  
% 4.11/1.00  fof(f73,plain,(
% 4.11/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 4.11/1.00    inference(cnf_transformation,[],[f45])).
% 4.11/1.00  
% 4.11/1.00  fof(f74,plain,(
% 4.11/1.00    v1_funct_1(sK3)),
% 4.11/1.00    inference(cnf_transformation,[],[f45])).
% 4.11/1.00  
% 4.11/1.00  fof(f75,plain,(
% 4.11/1.00    v1_funct_2(sK3,sK1,sK0)),
% 4.11/1.00    inference(cnf_transformation,[],[f45])).
% 4.11/1.00  
% 4.11/1.00  fof(f76,plain,(
% 4.11/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 4.11/1.00    inference(cnf_transformation,[],[f45])).
% 4.11/1.00  
% 4.11/1.00  fof(f15,axiom,(
% 4.11/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f38,plain,(
% 4.11/1.00    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.11/1.00    inference(ennf_transformation,[],[f15])).
% 4.11/1.00  
% 4.11/1.00  fof(f39,plain,(
% 4.11/1.00    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.11/1.00    inference(flattening,[],[f38])).
% 4.11/1.00  
% 4.11/1.00  fof(f69,plain,(
% 4.11/1.00    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f39])).
% 4.11/1.00  
% 4.11/1.00  fof(f80,plain,(
% 4.11/1.00    k1_xboole_0 != sK0),
% 4.11/1.00    inference(cnf_transformation,[],[f45])).
% 4.11/1.00  
% 4.11/1.00  fof(f2,axiom,(
% 4.11/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f49,plain,(
% 4.11/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 4.11/1.00    inference(cnf_transformation,[],[f2])).
% 4.11/1.00  
% 4.11/1.00  fof(f12,axiom,(
% 4.11/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f63,plain,(
% 4.11/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f12])).
% 4.11/1.00  
% 4.11/1.00  fof(f85,plain,(
% 4.11/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 4.11/1.00    inference(definition_unfolding,[],[f49,f63])).
% 4.11/1.00  
% 4.11/1.00  fof(f8,axiom,(
% 4.11/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f28,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.11/1.00    inference(ennf_transformation,[],[f8])).
% 4.11/1.00  
% 4.11/1.00  fof(f29,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.11/1.00    inference(flattening,[],[f28])).
% 4.11/1.00  
% 4.11/1.00  fof(f42,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.11/1.00    inference(nnf_transformation,[],[f29])).
% 4.11/1.00  
% 4.11/1.00  fof(f57,plain,(
% 4.11/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.11/1.00    inference(cnf_transformation,[],[f42])).
% 4.11/1.00  
% 4.11/1.00  fof(f10,axiom,(
% 4.11/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f18,plain,(
% 4.11/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 4.11/1.00    inference(pure_predicate_removal,[],[f10])).
% 4.11/1.00  
% 4.11/1.00  fof(f61,plain,(
% 4.11/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.11/1.00    inference(cnf_transformation,[],[f18])).
% 4.11/1.00  
% 4.11/1.00  fof(f9,axiom,(
% 4.11/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f30,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.11/1.00    inference(ennf_transformation,[],[f9])).
% 4.11/1.00  
% 4.11/1.00  fof(f31,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.11/1.00    inference(flattening,[],[f30])).
% 4.11/1.00  
% 4.11/1.00  fof(f60,plain,(
% 4.11/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f31])).
% 4.11/1.00  
% 4.11/1.00  fof(f77,plain,(
% 4.11/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 4.11/1.00    inference(cnf_transformation,[],[f45])).
% 4.11/1.00  
% 4.11/1.00  fof(f14,axiom,(
% 4.11/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f36,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 4.11/1.00    inference(ennf_transformation,[],[f14])).
% 4.11/1.00  
% 4.11/1.00  fof(f37,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 4.11/1.00    inference(flattening,[],[f36])).
% 4.11/1.00  
% 4.11/1.00  fof(f67,plain,(
% 4.11/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f37])).
% 4.11/1.00  
% 4.11/1.00  fof(f4,axiom,(
% 4.11/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f21,plain,(
% 4.11/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f4])).
% 4.11/1.00  
% 4.11/1.00  fof(f22,plain,(
% 4.11/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/1.00    inference(flattening,[],[f21])).
% 4.11/1.00  
% 4.11/1.00  fof(f52,plain,(
% 4.11/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f22])).
% 4.11/1.00  
% 4.11/1.00  fof(f7,axiom,(
% 4.11/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f27,plain,(
% 4.11/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.11/1.00    inference(ennf_transformation,[],[f7])).
% 4.11/1.00  
% 4.11/1.00  fof(f56,plain,(
% 4.11/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.11/1.00    inference(cnf_transformation,[],[f27])).
% 4.11/1.00  
% 4.11/1.00  fof(f1,axiom,(
% 4.11/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f47,plain,(
% 4.11/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.11/1.00    inference(cnf_transformation,[],[f1])).
% 4.11/1.00  
% 4.11/1.00  fof(f83,plain,(
% 4.11/1.00    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 4.11/1.00    inference(definition_unfolding,[],[f47,f63])).
% 4.11/1.00  
% 4.11/1.00  fof(f11,axiom,(
% 4.11/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f32,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.11/1.00    inference(ennf_transformation,[],[f11])).
% 4.11/1.00  
% 4.11/1.00  fof(f33,plain,(
% 4.11/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.11/1.00    inference(flattening,[],[f32])).
% 4.11/1.00  
% 4.11/1.00  fof(f62,plain,(
% 4.11/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f33])).
% 4.11/1.00  
% 4.11/1.00  fof(f6,axiom,(
% 4.11/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f25,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f6])).
% 4.11/1.00  
% 4.11/1.00  fof(f26,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/1.00    inference(flattening,[],[f25])).
% 4.11/1.00  
% 4.11/1.00  fof(f55,plain,(
% 4.11/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f26])).
% 4.11/1.00  
% 4.11/1.00  fof(f88,plain,(
% 4.11/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/1.00    inference(definition_unfolding,[],[f55,f63])).
% 4.11/1.00  
% 4.11/1.00  fof(f3,axiom,(
% 4.11/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f19,plain,(
% 4.11/1.00    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f3])).
% 4.11/1.00  
% 4.11/1.00  fof(f20,plain,(
% 4.11/1.00    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/1.00    inference(flattening,[],[f19])).
% 4.11/1.00  
% 4.11/1.00  fof(f50,plain,(
% 4.11/1.00    ( ! [X0,X1] : (v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f20])).
% 4.11/1.00  
% 4.11/1.00  fof(f87,plain,(
% 4.11/1.00    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/1.00    inference(definition_unfolding,[],[f50,f63])).
% 4.11/1.00  
% 4.11/1.00  fof(f82,plain,(
% 4.11/1.00    k2_funct_1(sK2) != sK3),
% 4.11/1.00    inference(cnf_transformation,[],[f45])).
% 4.11/1.00  
% 4.11/1.00  fof(f79,plain,(
% 4.11/1.00    v2_funct_1(sK2)),
% 4.11/1.00    inference(cnf_transformation,[],[f45])).
% 4.11/1.00  
% 4.11/1.00  fof(f81,plain,(
% 4.11/1.00    k1_xboole_0 != sK1),
% 4.11/1.00    inference(cnf_transformation,[],[f45])).
% 4.11/1.00  
% 4.11/1.00  fof(f51,plain,(
% 4.11/1.00    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f22])).
% 4.11/1.00  
% 4.11/1.00  fof(f46,plain,(
% 4.11/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.11/1.00    inference(cnf_transformation,[],[f1])).
% 4.11/1.00  
% 4.11/1.00  fof(f84,plain,(
% 4.11/1.00    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 4.11/1.00    inference(definition_unfolding,[],[f46,f63])).
% 4.11/1.00  
% 4.11/1.00  fof(f70,plain,(
% 4.11/1.00    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f39])).
% 4.11/1.00  
% 4.11/1.00  fof(f5,axiom,(
% 4.11/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 4.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f23,plain,(
% 4.11/1.00    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f5])).
% 4.11/1.00  
% 4.11/1.00  fof(f24,plain,(
% 4.11/1.00    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/1.00    inference(flattening,[],[f23])).
% 4.11/1.00  
% 4.11/1.00  fof(f53,plain,(
% 4.11/1.00    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f24])).
% 4.11/1.00  
% 4.11/1.00  cnf(c_17,plain,
% 4.11/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 4.11/1.00      | ~ v1_funct_2(X2,X0,X1)
% 4.11/1.00      | ~ v1_funct_2(X3,X1,X0)
% 4.11/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 4.11/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.11/1.00      | ~ v1_funct_1(X2)
% 4.11/1.00      | ~ v1_funct_1(X3)
% 4.11/1.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 4.11/1.00      inference(cnf_transformation,[],[f64]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_28,negated_conjecture,
% 4.11/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 4.11/1.00      inference(cnf_transformation,[],[f78]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_394,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.11/1.00      | ~ v1_funct_2(X3,X2,X1)
% 4.11/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v1_funct_1(X3)
% 4.11/1.00      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.11/1.00      | k2_relset_1(X1,X2,X0) = X2
% 4.11/1.00      | k6_partfun1(X2) != k6_partfun1(sK0)
% 4.11/1.00      | sK0 != X2 ),
% 4.11/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_395,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 4.11/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 4.11/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v1_funct_1(X2)
% 4.11/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.11/1.00      | k2_relset_1(X1,sK0,X0) = sK0
% 4.11/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 4.11/1.00      inference(unflattening,[status(thm)],[c_394]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_478,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 4.11/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 4.11/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v1_funct_1(X2)
% 4.11/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.11/1.00      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 4.11/1.00      inference(equality_resolution_simp,[status(thm)],[c_395]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1128,plain,
% 4.11/1.00      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.11/1.00      | k2_relset_1(X0,sK0,X2) = sK0
% 4.11/1.00      | v1_funct_2(X2,X0,sK0) != iProver_top
% 4.11/1.00      | v1_funct_2(X1,sK0,X0) != iProver_top
% 4.11/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 4.11/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 4.11/1.00      | v1_funct_1(X2) != iProver_top
% 4.11/1.00      | v1_funct_1(X1) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1670,plain,
% 4.11/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 4.11/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 4.11/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 4.11/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.11/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.11/1.00      | v1_funct_1(sK3) != iProver_top
% 4.11/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.11/1.00      inference(equality_resolution,[status(thm)],[c_1128]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_35,negated_conjecture,
% 4.11/1.00      ( v1_funct_1(sK2) ),
% 4.11/1.00      inference(cnf_transformation,[],[f71]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_36,plain,
% 4.11/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_34,negated_conjecture,
% 4.11/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f72]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_37,plain,
% 4.11/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_33,negated_conjecture,
% 4.11/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 4.11/1.00      inference(cnf_transformation,[],[f73]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_38,plain,
% 4.11/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_32,negated_conjecture,
% 4.11/1.00      ( v1_funct_1(sK3) ),
% 4.11/1.00      inference(cnf_transformation,[],[f74]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_39,plain,
% 4.11/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_31,negated_conjecture,
% 4.11/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f75]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_40,plain,
% 4.11/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_30,negated_conjecture,
% 4.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 4.11/1.00      inference(cnf_transformation,[],[f76]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_41,plain,
% 4.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1839,plain,
% 4.11/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_1670,c_36,c_37,c_38,c_39,c_40,c_41]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_23,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v2_funct_1(X0)
% 4.11/1.00      | k2_relset_1(X1,X2,X0) != X2
% 4.11/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 4.11/1.00      | k1_xboole_0 = X2 ),
% 4.11/1.00      inference(cnf_transformation,[],[f69]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1139,plain,
% 4.11/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 4.11/1.00      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 4.11/1.00      | k1_xboole_0 = X1
% 4.11/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.11/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.11/1.00      | v1_funct_1(X2) != iProver_top
% 4.11/1.00      | v2_funct_1(X2) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3716,plain,
% 4.11/1.00      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 4.11/1.00      | sK0 = k1_xboole_0
% 4.11/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 4.11/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.11/1.00      | v1_funct_1(sK3) != iProver_top
% 4.11/1.00      | v2_funct_1(sK3) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_1839,c_1139]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_26,negated_conjecture,
% 4.11/1.00      ( k1_xboole_0 != sK0 ),
% 4.11/1.00      inference(cnf_transformation,[],[f80]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_646,plain,( X0 = X0 ),theory(equality) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_677,plain,
% 4.11/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_646]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_647,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1238,plain,
% 4.11/1.00      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_647]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1239,plain,
% 4.11/1.00      ( sK0 != k1_xboole_0
% 4.11/1.00      | k1_xboole_0 = sK0
% 4.11/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_1238]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2,plain,
% 4.11/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 4.11/1.00      inference(cnf_transformation,[],[f85]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4858,plain,
% 4.11/1.00      ( v2_funct_1(k6_partfun1(sK0)) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4859,plain,
% 4.11/1.00      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_4858]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_12,plain,
% 4.11/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 4.11/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.11/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.11/1.00      | X3 = X2 ),
% 4.11/1.00      inference(cnf_transformation,[],[f57]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_381,plain,
% 4.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | X3 = X0
% 4.11/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 4.11/1.00      | k6_partfun1(sK0) != X3
% 4.11/1.00      | sK0 != X2
% 4.11/1.00      | sK0 != X1 ),
% 4.11/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_382,plain,
% 4.11/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.11/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.11/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.11/1.00      inference(unflattening,[status(thm)],[c_381]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_15,plain,
% 4.11/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 4.11/1.00      inference(cnf_transformation,[],[f61]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_390,plain,
% 4.11/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.11/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.11/1.00      inference(forward_subsumption_resolution,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_382,c_15]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1129,plain,
% 4.11/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.11/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_13,plain,
% 4.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.11/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v1_funct_1(X3) ),
% 4.11/1.00      inference(cnf_transformation,[],[f60]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1240,plain,
% 4.11/1.00      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.11/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 4.11/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.11/1.00      | ~ v1_funct_1(sK3)
% 4.11/1.00      | ~ v1_funct_1(sK2) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1832,plain,
% 4.11/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_1129,c_35,c_33,c_32,c_30,c_390,c_1240]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_29,negated_conjecture,
% 4.11/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 4.11/1.00      inference(cnf_transformation,[],[f77]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_19,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.11/1.00      | ~ v1_funct_2(X3,X4,X1)
% 4.11/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v1_funct_1(X3)
% 4.11/1.00      | v2_funct_1(X0)
% 4.11/1.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 4.11/1.00      | k2_relset_1(X4,X1,X3) != X1
% 4.11/1.00      | k1_xboole_0 = X2 ),
% 4.11/1.00      inference(cnf_transformation,[],[f67]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1143,plain,
% 4.11/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 4.11/1.00      | k1_xboole_0 = X3
% 4.11/1.00      | v1_funct_2(X4,X1,X3) != iProver_top
% 4.11/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.11/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 4.11/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.11/1.00      | v1_funct_1(X4) != iProver_top
% 4.11/1.00      | v1_funct_1(X2) != iProver_top
% 4.11/1.00      | v2_funct_1(X4) = iProver_top
% 4.11/1.00      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4854,plain,
% 4.11/1.00      ( k1_xboole_0 = X0
% 4.11/1.00      | v1_funct_2(X1,sK1,X0) != iProver_top
% 4.11/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 4.11/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 4.11/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.11/1.00      | v1_funct_1(X1) != iProver_top
% 4.11/1.00      | v1_funct_1(sK2) != iProver_top
% 4.11/1.00      | v2_funct_1(X1) = iProver_top
% 4.11/1.00      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_29,c_1143]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_5031,plain,
% 4.11/1.00      ( v1_funct_1(X1) != iProver_top
% 4.11/1.00      | v1_funct_2(X1,sK1,X0) != iProver_top
% 4.11/1.00      | k1_xboole_0 = X0
% 4.11/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 4.11/1.00      | v2_funct_1(X1) = iProver_top
% 4.11/1.00      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_4854,c_36,c_37,c_38]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_5032,plain,
% 4.11/1.00      ( k1_xboole_0 = X0
% 4.11/1.00      | v1_funct_2(X1,sK1,X0) != iProver_top
% 4.11/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 4.11/1.00      | v1_funct_1(X1) != iProver_top
% 4.11/1.00      | v2_funct_1(X1) = iProver_top
% 4.11/1.00      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 4.11/1.00      inference(renaming,[status(thm)],[c_5031]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_5035,plain,
% 4.11/1.00      ( sK0 = k1_xboole_0
% 4.11/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 4.11/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.11/1.00      | v1_funct_1(sK3) != iProver_top
% 4.11/1.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 4.11/1.00      | v2_funct_1(sK3) = iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_1832,c_5032]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_10702,plain,
% 4.11/1.00      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_3716,c_39,c_40,c_41,c_26,c_677,c_1239,c_4859,c_5035]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_5038,plain,
% 4.11/1.00      ( v2_funct_1(sK3) = iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_5035,c_39,c_40,c_41,c_26,c_677,c_1239,c_4859]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1135,plain,
% 4.11/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_5,plain,
% 4.11/1.00      ( ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v1_relat_1(X0)
% 4.11/1.00      | ~ v2_funct_1(X0)
% 4.11/1.00      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f52]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1153,plain,
% 4.11/1.00      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 4.11/1.00      | v1_funct_1(X0) != iProver_top
% 4.11/1.00      | v1_relat_1(X0) != iProver_top
% 4.11/1.00      | v2_funct_1(X0) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2114,plain,
% 4.11/1.00      ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 4.11/1.00      | v1_relat_1(sK3) != iProver_top
% 4.11/1.00      | v2_funct_1(sK3) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_1135,c_1153]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_10,plain,
% 4.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | v1_relat_1(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f56]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1285,plain,
% 4.11/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.11/1.00      | v1_relat_1(sK3) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1656,plain,
% 4.11/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 4.11/1.00      | v1_relat_1(sK3) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_1285]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1657,plain,
% 4.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.11/1.00      | v1_relat_1(sK3) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1656]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2858,plain,
% 4.11/1.00      ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 4.11/1.00      | v2_funct_1(sK3) != iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_2114,c_41,c_1657]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_5042,plain,
% 4.11/1.00      ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_5038,c_2858]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_10705,plain,
% 4.11/1.00      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_10702,c_5042]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_0,plain,
% 4.11/1.00      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 4.11/1.00      inference(cnf_transformation,[],[f83]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_10706,plain,
% 4.11/1.00      ( k1_relat_1(sK3) = sK1 ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_10705,c_0]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1134,plain,
% 4.11/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1137,plain,
% 4.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_16,plain,
% 4.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v1_funct_1(X3)
% 4.11/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f62]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1145,plain,
% 4.11/1.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 4.11/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 4.11/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.11/1.00      | v1_funct_1(X5) != iProver_top
% 4.11/1.00      | v1_funct_1(X4) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2806,plain,
% 4.11/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 4.11/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.11/1.00      | v1_funct_1(X2) != iProver_top
% 4.11/1.00      | v1_funct_1(sK3) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_1137,c_1145]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2931,plain,
% 4.11/1.00      ( v1_funct_1(X2) != iProver_top
% 4.11/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.11/1.00      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_2806,c_39]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2932,plain,
% 4.11/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 4.11/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.11/1.00      | v1_funct_1(X2) != iProver_top ),
% 4.11/1.00      inference(renaming,[status(thm)],[c_2931]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2940,plain,
% 4.11/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 4.11/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_1134,c_2932]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2941,plain,
% 4.11/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 4.11/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.11/1.00      inference(light_normalisation,[status(thm)],[c_2940,c_1832]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3709,plain,
% 4.11/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_2941,c_36]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_9,plain,
% 4.11/1.00      ( ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v1_funct_1(X1)
% 4.11/1.00      | ~ v1_relat_1(X0)
% 4.11/1.00      | ~ v1_relat_1(X1)
% 4.11/1.00      | ~ v2_funct_1(X1)
% 4.11/1.00      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 4.11/1.00      | k2_funct_1(X1) = X0
% 4.11/1.00      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f88]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4,plain,
% 4.11/1.00      ( ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v1_funct_1(X1)
% 4.11/1.00      | ~ v1_relat_1(X0)
% 4.11/1.00      | ~ v1_relat_1(X1)
% 4.11/1.00      | v2_funct_1(X1)
% 4.11/1.00      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1)) ),
% 4.11/1.00      inference(cnf_transformation,[],[f87]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_191,plain,
% 4.11/1.00      ( ~ v1_relat_1(X1)
% 4.11/1.00      | ~ v1_relat_1(X0)
% 4.11/1.00      | ~ v1_funct_1(X1)
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 4.11/1.00      | k2_funct_1(X1) = X0
% 4.11/1.00      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 4.11/1.00      inference(global_propositional_subsumption,[status(thm)],[c_9,c_4]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_192,plain,
% 4.11/1.00      ( ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v1_funct_1(X1)
% 4.11/1.00      | ~ v1_relat_1(X0)
% 4.11/1.00      | ~ v1_relat_1(X1)
% 4.11/1.00      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 4.11/1.00      | k2_funct_1(X0) = X1
% 4.11/1.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 4.11/1.00      inference(renaming,[status(thm)],[c_191]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1131,plain,
% 4.11/1.00      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 4.11/1.00      | k2_funct_1(X0) = X1
% 4.11/1.00      | k1_relat_1(X1) != k2_relat_1(X0)
% 4.11/1.00      | v1_funct_1(X0) != iProver_top
% 4.11/1.00      | v1_funct_1(X1) != iProver_top
% 4.11/1.00      | v1_relat_1(X0) != iProver_top
% 4.11/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3712,plain,
% 4.11/1.00      ( k2_funct_1(sK2) = sK3
% 4.11/1.00      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 4.11/1.00      | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
% 4.11/1.00      | v1_funct_1(sK3) != iProver_top
% 4.11/1.00      | v1_funct_1(sK2) != iProver_top
% 4.11/1.00      | v1_relat_1(sK3) != iProver_top
% 4.11/1.00      | v1_relat_1(sK2) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_3709,c_1131]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_24,negated_conjecture,
% 4.11/1.00      ( k2_funct_1(sK2) != sK3 ),
% 4.11/1.00      inference(cnf_transformation,[],[f82]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1758,plain,
% 4.11/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.11/1.00      | v1_relat_1(sK2) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1759,plain,
% 4.11/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.11/1.00      | v1_relat_1(sK2) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1758]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_10242,plain,
% 4.11/1.00      ( k1_relat_1(sK3) != k2_relat_1(sK2)
% 4.11/1.00      | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_3712,c_36,c_38,c_39,c_41,c_24,c_1657,c_1759]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3715,plain,
% 4.11/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 4.11/1.00      | sK1 = k1_xboole_0
% 4.11/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 4.11/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.11/1.00      | v1_funct_1(sK2) != iProver_top
% 4.11/1.00      | v2_funct_1(sK2) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_29,c_1139]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_27,negated_conjecture,
% 4.11/1.00      ( v2_funct_1(sK2) ),
% 4.11/1.00      inference(cnf_transformation,[],[f79]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_25,negated_conjecture,
% 4.11/1.00      ( k1_xboole_0 != sK1 ),
% 4.11/1.00      inference(cnf_transformation,[],[f81]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1203,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,X1,sK1)
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v2_funct_1(X0)
% 4.11/1.00      | k2_relset_1(X1,sK1,X0) != sK1
% 4.11/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 4.11/1.00      | k1_xboole_0 = sK1 ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1331,plain,
% 4.11/1.00      ( ~ v1_funct_2(sK2,X0,sK1)
% 4.11/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 4.11/1.00      | ~ v1_funct_1(sK2)
% 4.11/1.00      | ~ v2_funct_1(sK2)
% 4.11/1.00      | k2_relset_1(X0,sK1,sK2) != sK1
% 4.11/1.00      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 4.11/1.00      | k1_xboole_0 = sK1 ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_1203]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1555,plain,
% 4.11/1.00      ( ~ v1_funct_2(sK2,sK0,sK1)
% 4.11/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.11/1.00      | ~ v1_funct_1(sK2)
% 4.11/1.00      | ~ v2_funct_1(sK2)
% 4.11/1.00      | k2_relset_1(sK0,sK1,sK2) != sK1
% 4.11/1.00      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 4.11/1.00      | k1_xboole_0 = sK1 ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_1331]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3842,plain,
% 4.11/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_3715,c_35,c_34,c_33,c_29,c_27,c_25,c_1555]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1132,plain,
% 4.11/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_6,plain,
% 4.11/1.00      ( ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v1_relat_1(X0)
% 4.11/1.00      | ~ v2_funct_1(X0)
% 4.11/1.00      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f51]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1152,plain,
% 4.11/1.00      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 4.11/1.00      | v1_funct_1(X0) != iProver_top
% 4.11/1.00      | v1_relat_1(X0) != iProver_top
% 4.11/1.00      | v2_funct_1(X0) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2110,plain,
% 4.11/1.00      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 4.11/1.00      | v1_relat_1(sK2) != iProver_top
% 4.11/1.00      | v2_funct_1(sK2) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_1132,c_1152]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_43,plain,
% 4.11/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2668,plain,
% 4.11/1.00      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_2110,c_38,c_43,c_1759]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3845,plain,
% 4.11/1.00      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_3842,c_2668]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1,plain,
% 4.11/1.00      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 4.11/1.00      inference(cnf_transformation,[],[f84]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3846,plain,
% 4.11/1.00      ( k1_relat_1(sK2) = sK0 ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_3845,c_1]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_22,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v2_funct_1(X0)
% 4.11/1.00      | k2_relset_1(X1,X2,X0) != X2
% 4.11/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 4.11/1.00      | k1_xboole_0 = X2 ),
% 4.11/1.00      inference(cnf_transformation,[],[f70]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1140,plain,
% 4.11/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 4.11/1.00      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 4.11/1.00      | k1_xboole_0 = X1
% 4.11/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.11/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.11/1.00      | v1_funct_1(X2) != iProver_top
% 4.11/1.00      | v2_funct_1(X2) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3987,plain,
% 4.11/1.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 4.11/1.00      | sK1 = k1_xboole_0
% 4.11/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 4.11/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.11/1.00      | v1_funct_1(sK2) != iProver_top
% 4.11/1.00      | v2_funct_1(sK2) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_29,c_1140]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1202,plain,
% 4.11/1.00      ( ~ v1_funct_2(X0,X1,sK1)
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 4.11/1.00      | ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v2_funct_1(X0)
% 4.11/1.00      | k2_relset_1(X1,sK1,X0) != sK1
% 4.11/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 4.11/1.00      | k1_xboole_0 = sK1 ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1301,plain,
% 4.11/1.00      ( ~ v1_funct_2(sK2,X0,sK1)
% 4.11/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 4.11/1.00      | ~ v1_funct_1(sK2)
% 4.11/1.00      | ~ v2_funct_1(sK2)
% 4.11/1.00      | k2_relset_1(X0,sK1,sK2) != sK1
% 4.11/1.00      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 4.11/1.00      | k1_xboole_0 = sK1 ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_1202]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1534,plain,
% 4.11/1.00      ( ~ v1_funct_2(sK2,sK0,sK1)
% 4.11/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.11/1.00      | ~ v1_funct_1(sK2)
% 4.11/1.00      | ~ v2_funct_1(sK2)
% 4.11/1.00      | k2_relset_1(sK0,sK1,sK2) != sK1
% 4.11/1.00      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 4.11/1.00      | k1_xboole_0 = sK1 ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_1301]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3992,plain,
% 4.11/1.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_3987,c_35,c_34,c_33,c_29,c_27,c_25,c_1534]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_8,plain,
% 4.11/1.00      ( ~ v1_funct_1(X0)
% 4.11/1.00      | ~ v1_relat_1(X0)
% 4.11/1.00      | ~ v2_funct_1(X0)
% 4.11/1.00      | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f53]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1150,plain,
% 4.11/1.00      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
% 4.11/1.00      | v1_funct_1(X0) != iProver_top
% 4.11/1.00      | v1_relat_1(X0) != iProver_top
% 4.11/1.00      | v2_funct_1(X0) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2066,plain,
% 4.11/1.00      ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
% 4.11/1.00      | v1_relat_1(sK2) != iProver_top
% 4.11/1.00      | v2_funct_1(sK2) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_1132,c_1150]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2299,plain,
% 4.11/1.00      ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2) ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_2066,c_38,c_43,c_1759]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3995,plain,
% 4.11/1.00      ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2) ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_3992,c_2299]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3996,plain,
% 4.11/1.00      ( k2_relat_1(sK2) = sK1 ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_3995,c_1]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_10244,plain,
% 4.11/1.00      ( k1_relat_1(sK3) != sK1 | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 4.11/1.00      inference(light_normalisation,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_10242,c_3846,c_3996]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_10245,plain,
% 4.11/1.00      ( k1_relat_1(sK3) != sK1 ),
% 4.11/1.00      inference(equality_resolution_simp,[status(thm)],[c_10244]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(contradiction,plain,
% 4.11/1.00      ( $false ),
% 4.11/1.00      inference(minisat,[status(thm)],[c_10706,c_10245]) ).
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.11/1.00  
% 4.11/1.00  ------                               Statistics
% 4.11/1.00  
% 4.11/1.00  ------ General
% 4.11/1.00  
% 4.11/1.00  abstr_ref_over_cycles:                  0
% 4.11/1.00  abstr_ref_under_cycles:                 0
% 4.11/1.00  gc_basic_clause_elim:                   0
% 4.11/1.00  forced_gc_time:                         0
% 4.11/1.00  parsing_time:                           0.017
% 4.11/1.00  unif_index_cands_time:                  0.
% 4.11/1.00  unif_index_add_time:                    0.
% 4.11/1.00  orderings_time:                         0.
% 4.11/1.00  out_proof_time:                         0.016
% 4.11/1.00  total_time:                             0.468
% 4.11/1.00  num_of_symbols:                         51
% 4.11/1.00  num_of_terms:                           16190
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing
% 4.11/1.00  
% 4.11/1.00  num_of_splits:                          0
% 4.11/1.00  num_of_split_atoms:                     0
% 4.11/1.00  num_of_reused_defs:                     0
% 4.11/1.00  num_eq_ax_congr_red:                    0
% 4.11/1.00  num_of_sem_filtered_clauses:            1
% 4.11/1.00  num_of_subtypes:                        0
% 4.11/1.00  monotx_restored_types:                  0
% 4.11/1.00  sat_num_of_epr_types:                   0
% 4.11/1.00  sat_num_of_non_cyclic_types:            0
% 4.11/1.00  sat_guarded_non_collapsed_types:        0
% 4.11/1.00  num_pure_diseq_elim:                    0
% 4.11/1.00  simp_replaced_by:                       0
% 4.11/1.00  res_preprocessed:                       174
% 4.11/1.00  prep_upred:                             0
% 4.11/1.00  prep_unflattend:                        12
% 4.11/1.00  smt_new_axioms:                         0
% 4.11/1.00  pred_elim_cands:                        5
% 4.11/1.00  pred_elim:                              1
% 4.11/1.00  pred_elim_cl:                           1
% 4.11/1.00  pred_elim_cycles:                       3
% 4.11/1.00  merged_defs:                            0
% 4.11/1.00  merged_defs_ncl:                        0
% 4.11/1.00  bin_hyper_res:                          0
% 4.11/1.00  prep_cycles:                            4
% 4.11/1.00  pred_elim_time:                         0.005
% 4.11/1.00  splitting_time:                         0.
% 4.11/1.00  sem_filter_time:                        0.
% 4.11/1.00  monotx_time:                            0.001
% 4.11/1.00  subtype_inf_time:                       0.
% 4.11/1.00  
% 4.11/1.00  ------ Problem properties
% 4.11/1.00  
% 4.11/1.00  clauses:                                35
% 4.11/1.00  conjectures:                            11
% 4.11/1.00  epr:                                    7
% 4.11/1.00  horn:                                   31
% 4.11/1.00  ground:                                 12
% 4.11/1.00  unary:                                  16
% 4.11/1.00  binary:                                 2
% 4.11/1.00  lits:                                   132
% 4.11/1.00  lits_eq:                                32
% 4.11/1.00  fd_pure:                                0
% 4.11/1.00  fd_pseudo:                              0
% 4.11/1.00  fd_cond:                                4
% 4.11/1.00  fd_pseudo_cond:                         1
% 4.11/1.00  ac_symbols:                             0
% 4.11/1.00  
% 4.11/1.00  ------ Propositional Solver
% 4.11/1.00  
% 4.11/1.00  prop_solver_calls:                      31
% 4.11/1.00  prop_fast_solver_calls:                 2095
% 4.11/1.00  smt_solver_calls:                       0
% 4.11/1.00  smt_fast_solver_calls:                  0
% 4.11/1.00  prop_num_of_clauses:                    5680
% 4.11/1.00  prop_preprocess_simplified:             12716
% 4.11/1.00  prop_fo_subsumed:                       244
% 4.11/1.00  prop_solver_time:                       0.
% 4.11/1.00  smt_solver_time:                        0.
% 4.11/1.00  smt_fast_solver_time:                   0.
% 4.11/1.00  prop_fast_solver_time:                  0.
% 4.11/1.00  prop_unsat_core_time:                   0.
% 4.11/1.00  
% 4.11/1.00  ------ QBF
% 4.11/1.00  
% 4.11/1.00  qbf_q_res:                              0
% 4.11/1.00  qbf_num_tautologies:                    0
% 4.11/1.00  qbf_prep_cycles:                        0
% 4.11/1.00  
% 4.11/1.00  ------ BMC1
% 4.11/1.00  
% 4.11/1.00  bmc1_current_bound:                     -1
% 4.11/1.00  bmc1_last_solved_bound:                 -1
% 4.11/1.00  bmc1_unsat_core_size:                   -1
% 4.11/1.00  bmc1_unsat_core_parents_size:           -1
% 4.11/1.00  bmc1_merge_next_fun:                    0
% 4.11/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.11/1.00  
% 4.11/1.00  ------ Instantiation
% 4.11/1.00  
% 4.11/1.00  inst_num_of_clauses:                    1377
% 4.11/1.00  inst_num_in_passive:                    406
% 4.11/1.00  inst_num_in_active:                     721
% 4.11/1.00  inst_num_in_unprocessed:                250
% 4.11/1.00  inst_num_of_loops:                      850
% 4.11/1.00  inst_num_of_learning_restarts:          0
% 4.11/1.00  inst_num_moves_active_passive:          127
% 4.11/1.00  inst_lit_activity:                      0
% 4.11/1.00  inst_lit_activity_moves:                1
% 4.11/1.00  inst_num_tautologies:                   0
% 4.11/1.00  inst_num_prop_implied:                  0
% 4.11/1.00  inst_num_existing_simplified:           0
% 4.11/1.00  inst_num_eq_res_simplified:             0
% 4.11/1.00  inst_num_child_elim:                    0
% 4.11/1.00  inst_num_of_dismatching_blockings:      213
% 4.11/1.00  inst_num_of_non_proper_insts:           1334
% 4.11/1.00  inst_num_of_duplicates:                 0
% 4.11/1.00  inst_inst_num_from_inst_to_res:         0
% 4.11/1.00  inst_dismatching_checking_time:         0.
% 4.11/1.00  
% 4.11/1.00  ------ Resolution
% 4.11/1.00  
% 4.11/1.00  res_num_of_clauses:                     0
% 4.11/1.00  res_num_in_passive:                     0
% 4.11/1.00  res_num_in_active:                      0
% 4.11/1.00  res_num_of_loops:                       178
% 4.11/1.00  res_forward_subset_subsumed:            130
% 4.11/1.00  res_backward_subset_subsumed:           0
% 4.11/1.00  res_forward_subsumed:                   0
% 4.11/1.00  res_backward_subsumed:                  0
% 4.11/1.00  res_forward_subsumption_resolution:     2
% 4.11/1.00  res_backward_subsumption_resolution:    0
% 4.11/1.00  res_clause_to_clause_subsumption:       1024
% 4.11/1.00  res_orphan_elimination:                 0
% 4.11/1.00  res_tautology_del:                      68
% 4.11/1.00  res_num_eq_res_simplified:              1
% 4.11/1.00  res_num_sel_changes:                    0
% 4.11/1.00  res_moves_from_active_to_pass:          0
% 4.11/1.00  
% 4.11/1.00  ------ Superposition
% 4.11/1.00  
% 4.11/1.00  sup_time_total:                         0.
% 4.11/1.00  sup_time_generating:                    0.
% 4.11/1.00  sup_time_sim_full:                      0.
% 4.11/1.00  sup_time_sim_immed:                     0.
% 4.11/1.00  
% 4.11/1.00  sup_num_of_clauses:                     443
% 4.11/1.00  sup_num_in_active:                      155
% 4.11/1.00  sup_num_in_passive:                     288
% 4.11/1.00  sup_num_of_loops:                       169
% 4.11/1.00  sup_fw_superposition:                   196
% 4.11/1.00  sup_bw_superposition:                   280
% 4.11/1.00  sup_immediate_simplified:               208
% 4.11/1.00  sup_given_eliminated:                   0
% 4.11/1.00  comparisons_done:                       0
% 4.11/1.00  comparisons_avoided:                    0
% 4.11/1.00  
% 4.11/1.00  ------ Simplifications
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  sim_fw_subset_subsumed:                 15
% 4.11/1.00  sim_bw_subset_subsumed:                 10
% 4.11/1.00  sim_fw_subsumed:                        16
% 4.11/1.00  sim_bw_subsumed:                        0
% 4.11/1.00  sim_fw_subsumption_res:                 0
% 4.11/1.00  sim_bw_subsumption_res:                 0
% 4.11/1.00  sim_tautology_del:                      0
% 4.11/1.00  sim_eq_tautology_del:                   13
% 4.11/1.00  sim_eq_res_simp:                        1
% 4.11/1.00  sim_fw_demodulated:                     14
% 4.11/1.00  sim_bw_demodulated:                     7
% 4.11/1.00  sim_light_normalised:                   177
% 4.11/1.00  sim_joinable_taut:                      0
% 4.11/1.00  sim_joinable_simp:                      0
% 4.11/1.00  sim_ac_normalised:                      0
% 4.11/1.00  sim_smt_subsumption:                    0
% 4.11/1.00  
%------------------------------------------------------------------------------
