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
% DateTime   : Thu Dec  3 12:03:38 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 959 expanded)
%              Number of clauses        :  110 ( 262 expanded)
%              Number of leaves         :   21 ( 255 expanded)
%              Depth                    :   19
%              Number of atoms          :  763 (8316 expanded)
%              Number of equality atoms :  358 (3037 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f63,plain,(
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

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f77,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f50,f62])).

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

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
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

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f45])).

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

fof(f66,plain,(
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

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f82,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f49,f62])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f54,plain,(
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

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f54,f62])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f51,f62])).

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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f52,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f83,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f62])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_381,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_382,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_464,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_382])).

cnf(c_1096,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_1641,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1096])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1807,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1641,c_35,c_36,c_37,c_38,c_39,c_40])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1107,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3617,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1807,c_1107])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_627,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_658,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_628,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1204,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_1205,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1204])).

cnf(c_4,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1121,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_369,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_377,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_369,c_14])).

cnf(c_1097,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1206,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1734,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1097,c_34,c_32,c_31,c_29,c_377,c_1206])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f66])).

cnf(c_1111,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4799,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1111])).

cnf(c_4846,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4799,c_35,c_36,c_37])).

cnf(c_4847,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4846])).

cnf(c_4850,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_4847])).

cnf(c_4853,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4850,c_38,c_39,c_40,c_25,c_658,c_1205])).

cnf(c_4857,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1121,c_4853])).

cnf(c_7577,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3617,c_38,c_39,c_40,c_25,c_658,c_1205,c_4857])).

cnf(c_1103,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1119,plain,
    ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2673,plain,
    ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1103,c_1119])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1122,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1105,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1123,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2277,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_1123])).

cnf(c_2424,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_2277])).

cnf(c_2783,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2673,c_2424])).

cnf(c_2784,plain,
    ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2783])).

cnf(c_4894,plain,
    ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4857,c_2784])).

cnf(c_7580,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_7577,c_4894])).

cnf(c_2,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_7581,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_7580,c_2])).

cnf(c_1102,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1113,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2771,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_1113])).

cnf(c_2855,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2771,c_38])).

cnf(c_2856,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2855])).

cnf(c_2863,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1102,c_2856])).

cnf(c_2864,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2863,c_1734])).

cnf(c_3609,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2864,c_35])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_183,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_5])).

cnf(c_184,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_1099,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_184])).

cnf(c_3612,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3609,c_1099])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1117,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1906,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1102,c_1117])).

cnf(c_1907,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1906,c_28])).

cnf(c_3613,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3612,c_1907])).

cnf(c_23,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2278,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1102,c_1123])).

cnf(c_2427,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_2278])).

cnf(c_4438,plain,
    ( k1_relat_1(sK3) != sK1
    | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3613,c_35,c_38,c_23,c_2424,c_2427])).

cnf(c_3616,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1107])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1167,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1297,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_1528,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_3802,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3616,c_34,c_33,c_32,c_28,c_26,c_24,c_1528])).

cnf(c_1100,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1118,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2286,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1100,c_1118])).

cnf(c_42,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2447,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2286,c_42,c_2427])).

cnf(c_3805,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3802,c_2447])).

cnf(c_3,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3806,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_3805,c_3])).

cnf(c_4440,plain,
    ( k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_4438,c_3806])).

cnf(c_4441,plain,
    ( k1_relat_1(sK3) != sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_4440])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7581,c_4441])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:31:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.67/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/0.99  
% 3.67/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/0.99  
% 3.67/0.99  ------  iProver source info
% 3.67/0.99  
% 3.67/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.67/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/0.99  git: non_committed_changes: false
% 3.67/0.99  git: last_make_outside_of_git: false
% 3.67/0.99  
% 3.67/0.99  ------ 
% 3.67/0.99  
% 3.67/0.99  ------ Input Options
% 3.67/0.99  
% 3.67/0.99  --out_options                           all
% 3.67/0.99  --tptp_safe_out                         true
% 3.67/0.99  --problem_path                          ""
% 3.67/0.99  --include_path                          ""
% 3.67/0.99  --clausifier                            res/vclausify_rel
% 3.67/0.99  --clausifier_options                    ""
% 3.67/0.99  --stdin                                 false
% 3.67/0.99  --stats_out                             all
% 3.67/0.99  
% 3.67/0.99  ------ General Options
% 3.67/0.99  
% 3.67/0.99  --fof                                   false
% 3.67/0.99  --time_out_real                         305.
% 3.67/0.99  --time_out_virtual                      -1.
% 3.67/0.99  --symbol_type_check                     false
% 3.67/0.99  --clausify_out                          false
% 3.67/0.99  --sig_cnt_out                           false
% 3.67/0.99  --trig_cnt_out                          false
% 3.67/0.99  --trig_cnt_out_tolerance                1.
% 3.67/0.99  --trig_cnt_out_sk_spl                   false
% 3.67/0.99  --abstr_cl_out                          false
% 3.67/0.99  
% 3.67/0.99  ------ Global Options
% 3.67/0.99  
% 3.67/0.99  --schedule                              default
% 3.67/0.99  --add_important_lit                     false
% 3.67/0.99  --prop_solver_per_cl                    1000
% 3.67/0.99  --min_unsat_core                        false
% 3.67/0.99  --soft_assumptions                      false
% 3.67/0.99  --soft_lemma_size                       3
% 3.67/0.99  --prop_impl_unit_size                   0
% 3.67/0.99  --prop_impl_unit                        []
% 3.67/0.99  --share_sel_clauses                     true
% 3.67/0.99  --reset_solvers                         false
% 3.67/0.99  --bc_imp_inh                            [conj_cone]
% 3.67/0.99  --conj_cone_tolerance                   3.
% 3.67/0.99  --extra_neg_conj                        none
% 3.67/0.99  --large_theory_mode                     true
% 3.67/0.99  --prolific_symb_bound                   200
% 3.67/0.99  --lt_threshold                          2000
% 3.67/0.99  --clause_weak_htbl                      true
% 3.67/0.99  --gc_record_bc_elim                     false
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing Options
% 3.67/0.99  
% 3.67/0.99  --preprocessing_flag                    true
% 3.67/0.99  --time_out_prep_mult                    0.1
% 3.67/0.99  --splitting_mode                        input
% 3.67/0.99  --splitting_grd                         true
% 3.67/0.99  --splitting_cvd                         false
% 3.67/0.99  --splitting_cvd_svl                     false
% 3.67/0.99  --splitting_nvd                         32
% 3.67/0.99  --sub_typing                            true
% 3.67/0.99  --prep_gs_sim                           true
% 3.67/0.99  --prep_unflatten                        true
% 3.67/0.99  --prep_res_sim                          true
% 3.67/0.99  --prep_upred                            true
% 3.67/0.99  --prep_sem_filter                       exhaustive
% 3.67/0.99  --prep_sem_filter_out                   false
% 3.67/0.99  --pred_elim                             true
% 3.67/0.99  --res_sim_input                         true
% 3.67/0.99  --eq_ax_congr_red                       true
% 3.67/0.99  --pure_diseq_elim                       true
% 3.67/0.99  --brand_transform                       false
% 3.67/0.99  --non_eq_to_eq                          false
% 3.67/0.99  --prep_def_merge                        true
% 3.67/0.99  --prep_def_merge_prop_impl              false
% 3.67/0.99  --prep_def_merge_mbd                    true
% 3.67/0.99  --prep_def_merge_tr_red                 false
% 3.67/0.99  --prep_def_merge_tr_cl                  false
% 3.67/0.99  --smt_preprocessing                     true
% 3.67/0.99  --smt_ac_axioms                         fast
% 3.67/0.99  --preprocessed_out                      false
% 3.67/0.99  --preprocessed_stats                    false
% 3.67/0.99  
% 3.67/0.99  ------ Abstraction refinement Options
% 3.67/0.99  
% 3.67/0.99  --abstr_ref                             []
% 3.67/0.99  --abstr_ref_prep                        false
% 3.67/0.99  --abstr_ref_until_sat                   false
% 3.67/0.99  --abstr_ref_sig_restrict                funpre
% 3.67/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/0.99  --abstr_ref_under                       []
% 3.67/0.99  
% 3.67/0.99  ------ SAT Options
% 3.67/0.99  
% 3.67/0.99  --sat_mode                              false
% 3.67/0.99  --sat_fm_restart_options                ""
% 3.67/0.99  --sat_gr_def                            false
% 3.67/0.99  --sat_epr_types                         true
% 3.67/0.99  --sat_non_cyclic_types                  false
% 3.67/0.99  --sat_finite_models                     false
% 3.67/0.99  --sat_fm_lemmas                         false
% 3.67/0.99  --sat_fm_prep                           false
% 3.67/0.99  --sat_fm_uc_incr                        true
% 3.67/0.99  --sat_out_model                         small
% 3.67/0.99  --sat_out_clauses                       false
% 3.67/0.99  
% 3.67/0.99  ------ QBF Options
% 3.67/0.99  
% 3.67/0.99  --qbf_mode                              false
% 3.67/0.99  --qbf_elim_univ                         false
% 3.67/0.99  --qbf_dom_inst                          none
% 3.67/0.99  --qbf_dom_pre_inst                      false
% 3.67/0.99  --qbf_sk_in                             false
% 3.67/0.99  --qbf_pred_elim                         true
% 3.67/0.99  --qbf_split                             512
% 3.67/0.99  
% 3.67/0.99  ------ BMC1 Options
% 3.67/0.99  
% 3.67/0.99  --bmc1_incremental                      false
% 3.67/0.99  --bmc1_axioms                           reachable_all
% 3.67/0.99  --bmc1_min_bound                        0
% 3.67/0.99  --bmc1_max_bound                        -1
% 3.67/0.99  --bmc1_max_bound_default                -1
% 3.67/0.99  --bmc1_symbol_reachability              true
% 3.67/0.99  --bmc1_property_lemmas                  false
% 3.67/0.99  --bmc1_k_induction                      false
% 3.67/0.99  --bmc1_non_equiv_states                 false
% 3.67/0.99  --bmc1_deadlock                         false
% 3.67/0.99  --bmc1_ucm                              false
% 3.67/0.99  --bmc1_add_unsat_core                   none
% 3.67/0.99  --bmc1_unsat_core_children              false
% 3.67/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/0.99  --bmc1_out_stat                         full
% 3.67/0.99  --bmc1_ground_init                      false
% 3.67/0.99  --bmc1_pre_inst_next_state              false
% 3.67/0.99  --bmc1_pre_inst_state                   false
% 3.67/0.99  --bmc1_pre_inst_reach_state             false
% 3.67/0.99  --bmc1_out_unsat_core                   false
% 3.67/0.99  --bmc1_aig_witness_out                  false
% 3.67/0.99  --bmc1_verbose                          false
% 3.67/0.99  --bmc1_dump_clauses_tptp                false
% 3.67/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.67/0.99  --bmc1_dump_file                        -
% 3.67/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.67/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.67/0.99  --bmc1_ucm_extend_mode                  1
% 3.67/0.99  --bmc1_ucm_init_mode                    2
% 3.67/0.99  --bmc1_ucm_cone_mode                    none
% 3.67/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.67/0.99  --bmc1_ucm_relax_model                  4
% 3.67/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.67/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/0.99  --bmc1_ucm_layered_model                none
% 3.67/0.99  --bmc1_ucm_max_lemma_size               10
% 3.67/0.99  
% 3.67/0.99  ------ AIG Options
% 3.67/0.99  
% 3.67/0.99  --aig_mode                              false
% 3.67/0.99  
% 3.67/0.99  ------ Instantiation Options
% 3.67/0.99  
% 3.67/0.99  --instantiation_flag                    true
% 3.67/0.99  --inst_sos_flag                         true
% 3.67/0.99  --inst_sos_phase                        true
% 3.67/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/0.99  --inst_lit_sel_side                     num_symb
% 3.67/0.99  --inst_solver_per_active                1400
% 3.67/0.99  --inst_solver_calls_frac                1.
% 3.67/0.99  --inst_passive_queue_type               priority_queues
% 3.67/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/0.99  --inst_passive_queues_freq              [25;2]
% 3.67/0.99  --inst_dismatching                      true
% 3.67/0.99  --inst_eager_unprocessed_to_passive     true
% 3.67/0.99  --inst_prop_sim_given                   true
% 3.67/0.99  --inst_prop_sim_new                     false
% 3.67/0.99  --inst_subs_new                         false
% 3.67/0.99  --inst_eq_res_simp                      false
% 3.67/0.99  --inst_subs_given                       false
% 3.67/0.99  --inst_orphan_elimination               true
% 3.67/0.99  --inst_learning_loop_flag               true
% 3.67/0.99  --inst_learning_start                   3000
% 3.67/0.99  --inst_learning_factor                  2
% 3.67/0.99  --inst_start_prop_sim_after_learn       3
% 3.67/0.99  --inst_sel_renew                        solver
% 3.67/0.99  --inst_lit_activity_flag                true
% 3.67/0.99  --inst_restr_to_given                   false
% 3.67/0.99  --inst_activity_threshold               500
% 3.67/0.99  --inst_out_proof                        true
% 3.67/0.99  
% 3.67/0.99  ------ Resolution Options
% 3.67/0.99  
% 3.67/0.99  --resolution_flag                       true
% 3.67/0.99  --res_lit_sel                           adaptive
% 3.67/0.99  --res_lit_sel_side                      none
% 3.67/0.99  --res_ordering                          kbo
% 3.67/0.99  --res_to_prop_solver                    active
% 3.67/0.99  --res_prop_simpl_new                    false
% 3.67/0.99  --res_prop_simpl_given                  true
% 3.67/0.99  --res_passive_queue_type                priority_queues
% 3.67/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/0.99  --res_passive_queues_freq               [15;5]
% 3.67/0.99  --res_forward_subs                      full
% 3.67/0.99  --res_backward_subs                     full
% 3.67/0.99  --res_forward_subs_resolution           true
% 3.67/0.99  --res_backward_subs_resolution          true
% 3.67/0.99  --res_orphan_elimination                true
% 3.67/0.99  --res_time_limit                        2.
% 3.67/0.99  --res_out_proof                         true
% 3.67/0.99  
% 3.67/0.99  ------ Superposition Options
% 3.67/0.99  
% 3.67/0.99  --superposition_flag                    true
% 3.67/0.99  --sup_passive_queue_type                priority_queues
% 3.67/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.67/0.99  --demod_completeness_check              fast
% 3.67/0.99  --demod_use_ground                      true
% 3.67/0.99  --sup_to_prop_solver                    passive
% 3.67/0.99  --sup_prop_simpl_new                    true
% 3.67/0.99  --sup_prop_simpl_given                  true
% 3.67/0.99  --sup_fun_splitting                     true
% 3.67/0.99  --sup_smt_interval                      50000
% 3.67/0.99  
% 3.67/0.99  ------ Superposition Simplification Setup
% 3.67/0.99  
% 3.67/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.67/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.67/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.67/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.67/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.67/0.99  --sup_immed_triv                        [TrivRules]
% 3.67/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_immed_bw_main                     []
% 3.67/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.67/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_input_bw                          []
% 3.67/0.99  
% 3.67/0.99  ------ Combination Options
% 3.67/0.99  
% 3.67/0.99  --comb_res_mult                         3
% 3.67/0.99  --comb_sup_mult                         2
% 3.67/0.99  --comb_inst_mult                        10
% 3.67/0.99  
% 3.67/0.99  ------ Debug Options
% 3.67/0.99  
% 3.67/0.99  --dbg_backtrace                         false
% 3.67/0.99  --dbg_dump_prop_clauses                 false
% 3.67/0.99  --dbg_dump_prop_clauses_file            -
% 3.67/0.99  --dbg_out_stat                          false
% 3.67/0.99  ------ Parsing...
% 3.67/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.99  ------ Proving...
% 3.67/0.99  ------ Problem Properties 
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  clauses                                 34
% 3.67/0.99  conjectures                             11
% 3.67/0.99  EPR                                     7
% 3.67/0.99  Horn                                    30
% 3.67/0.99  unary                                   16
% 3.67/0.99  binary                                  2
% 3.67/0.99  lits                                    127
% 3.67/0.99  lits eq                                 31
% 3.67/0.99  fd_pure                                 0
% 3.67/0.99  fd_pseudo                               0
% 3.67/0.99  fd_cond                                 4
% 3.67/0.99  fd_pseudo_cond                          1
% 3.67/0.99  AC symbols                              0
% 3.67/0.99  
% 3.67/0.99  ------ Schedule dynamic 5 is on 
% 3.67/0.99  
% 3.67/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  ------ 
% 3.67/0.99  Current options:
% 3.67/0.99  ------ 
% 3.67/0.99  
% 3.67/0.99  ------ Input Options
% 3.67/0.99  
% 3.67/0.99  --out_options                           all
% 3.67/0.99  --tptp_safe_out                         true
% 3.67/0.99  --problem_path                          ""
% 3.67/0.99  --include_path                          ""
% 3.67/0.99  --clausifier                            res/vclausify_rel
% 3.67/0.99  --clausifier_options                    ""
% 3.67/0.99  --stdin                                 false
% 3.67/0.99  --stats_out                             all
% 3.67/0.99  
% 3.67/0.99  ------ General Options
% 3.67/0.99  
% 3.67/0.99  --fof                                   false
% 3.67/0.99  --time_out_real                         305.
% 3.67/0.99  --time_out_virtual                      -1.
% 3.67/0.99  --symbol_type_check                     false
% 3.67/0.99  --clausify_out                          false
% 3.67/0.99  --sig_cnt_out                           false
% 3.67/0.99  --trig_cnt_out                          false
% 3.67/0.99  --trig_cnt_out_tolerance                1.
% 3.67/0.99  --trig_cnt_out_sk_spl                   false
% 3.67/0.99  --abstr_cl_out                          false
% 3.67/0.99  
% 3.67/0.99  ------ Global Options
% 3.67/0.99  
% 3.67/0.99  --schedule                              default
% 3.67/0.99  --add_important_lit                     false
% 3.67/0.99  --prop_solver_per_cl                    1000
% 3.67/0.99  --min_unsat_core                        false
% 3.67/0.99  --soft_assumptions                      false
% 3.67/0.99  --soft_lemma_size                       3
% 3.67/0.99  --prop_impl_unit_size                   0
% 3.67/0.99  --prop_impl_unit                        []
% 3.67/0.99  --share_sel_clauses                     true
% 3.67/0.99  --reset_solvers                         false
% 3.67/0.99  --bc_imp_inh                            [conj_cone]
% 3.67/0.99  --conj_cone_tolerance                   3.
% 3.67/0.99  --extra_neg_conj                        none
% 3.67/0.99  --large_theory_mode                     true
% 3.67/0.99  --prolific_symb_bound                   200
% 3.67/0.99  --lt_threshold                          2000
% 3.67/0.99  --clause_weak_htbl                      true
% 3.67/0.99  --gc_record_bc_elim                     false
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing Options
% 3.67/0.99  
% 3.67/0.99  --preprocessing_flag                    true
% 3.67/0.99  --time_out_prep_mult                    0.1
% 3.67/0.99  --splitting_mode                        input
% 3.67/0.99  --splitting_grd                         true
% 3.67/0.99  --splitting_cvd                         false
% 3.67/0.99  --splitting_cvd_svl                     false
% 3.67/0.99  --splitting_nvd                         32
% 3.67/0.99  --sub_typing                            true
% 3.67/0.99  --prep_gs_sim                           true
% 3.67/0.99  --prep_unflatten                        true
% 3.67/0.99  --prep_res_sim                          true
% 3.67/0.99  --prep_upred                            true
% 3.67/0.99  --prep_sem_filter                       exhaustive
% 3.67/0.99  --prep_sem_filter_out                   false
% 3.67/0.99  --pred_elim                             true
% 3.67/0.99  --res_sim_input                         true
% 3.67/0.99  --eq_ax_congr_red                       true
% 3.67/0.99  --pure_diseq_elim                       true
% 3.67/0.99  --brand_transform                       false
% 3.67/0.99  --non_eq_to_eq                          false
% 3.67/0.99  --prep_def_merge                        true
% 3.67/0.99  --prep_def_merge_prop_impl              false
% 3.67/0.99  --prep_def_merge_mbd                    true
% 3.67/0.99  --prep_def_merge_tr_red                 false
% 3.67/0.99  --prep_def_merge_tr_cl                  false
% 3.67/0.99  --smt_preprocessing                     true
% 3.67/0.99  --smt_ac_axioms                         fast
% 3.67/0.99  --preprocessed_out                      false
% 3.67/0.99  --preprocessed_stats                    false
% 3.67/0.99  
% 3.67/0.99  ------ Abstraction refinement Options
% 3.67/0.99  
% 3.67/0.99  --abstr_ref                             []
% 3.67/0.99  --abstr_ref_prep                        false
% 3.67/0.99  --abstr_ref_until_sat                   false
% 3.67/0.99  --abstr_ref_sig_restrict                funpre
% 3.67/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/0.99  --abstr_ref_under                       []
% 3.67/0.99  
% 3.67/0.99  ------ SAT Options
% 3.67/0.99  
% 3.67/0.99  --sat_mode                              false
% 3.67/0.99  --sat_fm_restart_options                ""
% 3.67/0.99  --sat_gr_def                            false
% 3.67/0.99  --sat_epr_types                         true
% 3.67/0.99  --sat_non_cyclic_types                  false
% 3.67/0.99  --sat_finite_models                     false
% 3.67/0.99  --sat_fm_lemmas                         false
% 3.67/0.99  --sat_fm_prep                           false
% 3.67/0.99  --sat_fm_uc_incr                        true
% 3.67/0.99  --sat_out_model                         small
% 3.67/0.99  --sat_out_clauses                       false
% 3.67/0.99  
% 3.67/0.99  ------ QBF Options
% 3.67/0.99  
% 3.67/0.99  --qbf_mode                              false
% 3.67/0.99  --qbf_elim_univ                         false
% 3.67/0.99  --qbf_dom_inst                          none
% 3.67/0.99  --qbf_dom_pre_inst                      false
% 3.67/0.99  --qbf_sk_in                             false
% 3.67/0.99  --qbf_pred_elim                         true
% 3.67/0.99  --qbf_split                             512
% 3.67/0.99  
% 3.67/0.99  ------ BMC1 Options
% 3.67/0.99  
% 3.67/0.99  --bmc1_incremental                      false
% 3.67/0.99  --bmc1_axioms                           reachable_all
% 3.67/0.99  --bmc1_min_bound                        0
% 3.67/0.99  --bmc1_max_bound                        -1
% 3.67/0.99  --bmc1_max_bound_default                -1
% 3.67/0.99  --bmc1_symbol_reachability              true
% 3.67/0.99  --bmc1_property_lemmas                  false
% 3.67/0.99  --bmc1_k_induction                      false
% 3.67/0.99  --bmc1_non_equiv_states                 false
% 3.67/0.99  --bmc1_deadlock                         false
% 3.67/0.99  --bmc1_ucm                              false
% 3.67/0.99  --bmc1_add_unsat_core                   none
% 3.67/0.99  --bmc1_unsat_core_children              false
% 3.67/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/0.99  --bmc1_out_stat                         full
% 3.67/0.99  --bmc1_ground_init                      false
% 3.67/0.99  --bmc1_pre_inst_next_state              false
% 3.67/0.99  --bmc1_pre_inst_state                   false
% 3.67/0.99  --bmc1_pre_inst_reach_state             false
% 3.67/0.99  --bmc1_out_unsat_core                   false
% 3.67/0.99  --bmc1_aig_witness_out                  false
% 3.67/0.99  --bmc1_verbose                          false
% 3.67/0.99  --bmc1_dump_clauses_tptp                false
% 3.67/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.67/0.99  --bmc1_dump_file                        -
% 3.67/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.67/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.67/0.99  --bmc1_ucm_extend_mode                  1
% 3.67/0.99  --bmc1_ucm_init_mode                    2
% 3.67/0.99  --bmc1_ucm_cone_mode                    none
% 3.67/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.67/0.99  --bmc1_ucm_relax_model                  4
% 3.67/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.67/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/0.99  --bmc1_ucm_layered_model                none
% 3.67/0.99  --bmc1_ucm_max_lemma_size               10
% 3.67/0.99  
% 3.67/0.99  ------ AIG Options
% 3.67/0.99  
% 3.67/0.99  --aig_mode                              false
% 3.67/0.99  
% 3.67/0.99  ------ Instantiation Options
% 3.67/0.99  
% 3.67/0.99  --instantiation_flag                    true
% 3.67/0.99  --inst_sos_flag                         true
% 3.67/0.99  --inst_sos_phase                        true
% 3.67/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/0.99  --inst_lit_sel_side                     none
% 3.67/0.99  --inst_solver_per_active                1400
% 3.67/0.99  --inst_solver_calls_frac                1.
% 3.67/0.99  --inst_passive_queue_type               priority_queues
% 3.67/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/0.99  --inst_passive_queues_freq              [25;2]
% 3.67/0.99  --inst_dismatching                      true
% 3.67/0.99  --inst_eager_unprocessed_to_passive     true
% 3.67/0.99  --inst_prop_sim_given                   true
% 3.67/0.99  --inst_prop_sim_new                     false
% 3.67/0.99  --inst_subs_new                         false
% 3.67/0.99  --inst_eq_res_simp                      false
% 3.67/0.99  --inst_subs_given                       false
% 3.67/0.99  --inst_orphan_elimination               true
% 3.67/0.99  --inst_learning_loop_flag               true
% 3.67/0.99  --inst_learning_start                   3000
% 3.67/0.99  --inst_learning_factor                  2
% 3.67/0.99  --inst_start_prop_sim_after_learn       3
% 3.67/0.99  --inst_sel_renew                        solver
% 3.67/0.99  --inst_lit_activity_flag                true
% 3.67/0.99  --inst_restr_to_given                   false
% 3.67/0.99  --inst_activity_threshold               500
% 3.67/0.99  --inst_out_proof                        true
% 3.67/0.99  
% 3.67/0.99  ------ Resolution Options
% 3.67/0.99  
% 3.67/0.99  --resolution_flag                       false
% 3.67/0.99  --res_lit_sel                           adaptive
% 3.67/0.99  --res_lit_sel_side                      none
% 3.67/0.99  --res_ordering                          kbo
% 3.67/0.99  --res_to_prop_solver                    active
% 3.67/0.99  --res_prop_simpl_new                    false
% 3.67/0.99  --res_prop_simpl_given                  true
% 3.67/0.99  --res_passive_queue_type                priority_queues
% 3.67/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/0.99  --res_passive_queues_freq               [15;5]
% 3.67/0.99  --res_forward_subs                      full
% 3.67/0.99  --res_backward_subs                     full
% 3.67/0.99  --res_forward_subs_resolution           true
% 3.67/0.99  --res_backward_subs_resolution          true
% 3.67/0.99  --res_orphan_elimination                true
% 3.67/0.99  --res_time_limit                        2.
% 3.67/0.99  --res_out_proof                         true
% 3.67/0.99  
% 3.67/0.99  ------ Superposition Options
% 3.67/0.99  
% 3.67/0.99  --superposition_flag                    true
% 3.67/0.99  --sup_passive_queue_type                priority_queues
% 3.67/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.67/0.99  --demod_completeness_check              fast
% 3.67/0.99  --demod_use_ground                      true
% 3.67/0.99  --sup_to_prop_solver                    passive
% 3.67/0.99  --sup_prop_simpl_new                    true
% 3.67/0.99  --sup_prop_simpl_given                  true
% 3.67/0.99  --sup_fun_splitting                     true
% 3.67/0.99  --sup_smt_interval                      50000
% 3.67/0.99  
% 3.67/0.99  ------ Superposition Simplification Setup
% 3.67/0.99  
% 3.67/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.67/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.67/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.67/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.67/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.67/0.99  --sup_immed_triv                        [TrivRules]
% 3.67/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_immed_bw_main                     []
% 3.67/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.67/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.99  --sup_input_bw                          []
% 3.67/0.99  
% 3.67/0.99  ------ Combination Options
% 3.67/0.99  
% 3.67/0.99  --comb_res_mult                         3
% 3.67/0.99  --comb_sup_mult                         2
% 3.67/0.99  --comb_inst_mult                        10
% 3.67/0.99  
% 3.67/0.99  ------ Debug Options
% 3.67/0.99  
% 3.67/0.99  --dbg_backtrace                         false
% 3.67/0.99  --dbg_dump_prop_clauses                 false
% 3.67/0.99  --dbg_dump_prop_clauses_file            -
% 3.67/0.99  --dbg_out_stat                          false
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  ------ Proving...
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  % SZS status Theorem for theBenchmark.p
% 3.67/0.99  
% 3.67/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/0.99  
% 3.67/0.99  fof(f14,axiom,(
% 3.67/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f34,plain,(
% 3.67/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.67/0.99    inference(ennf_transformation,[],[f14])).
% 3.67/0.99  
% 3.67/0.99  fof(f35,plain,(
% 3.67/0.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.67/0.99    inference(flattening,[],[f34])).
% 3.67/0.99  
% 3.67/0.99  fof(f63,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f35])).
% 3.67/0.99  
% 3.67/0.99  fof(f17,conjecture,(
% 3.67/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f18,negated_conjecture,(
% 3.67/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.67/0.99    inference(negated_conjecture,[],[f17])).
% 3.67/0.99  
% 3.67/0.99  fof(f40,plain,(
% 3.67/0.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.67/0.99    inference(ennf_transformation,[],[f18])).
% 3.67/0.99  
% 3.67/0.99  fof(f41,plain,(
% 3.67/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.67/0.99    inference(flattening,[],[f40])).
% 3.67/0.99  
% 3.67/0.99  fof(f44,plain,(
% 3.67/0.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.67/0.99    introduced(choice_axiom,[])).
% 3.67/0.99  
% 3.67/0.99  fof(f43,plain,(
% 3.67/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.67/0.99    introduced(choice_axiom,[])).
% 3.67/0.99  
% 3.67/0.99  fof(f45,plain,(
% 3.67/0.99    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.67/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f44,f43])).
% 3.67/0.99  
% 3.67/0.99  fof(f77,plain,(
% 3.67/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f70,plain,(
% 3.67/0.99    v1_funct_1(sK2)),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f71,plain,(
% 3.67/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f72,plain,(
% 3.67/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f73,plain,(
% 3.67/0.99    v1_funct_1(sK3)),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f74,plain,(
% 3.67/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f75,plain,(
% 3.67/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f16,axiom,(
% 3.67/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f38,plain,(
% 3.67/0.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.67/0.99    inference(ennf_transformation,[],[f16])).
% 3.67/0.99  
% 3.67/0.99  fof(f39,plain,(
% 3.67/0.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.67/0.99    inference(flattening,[],[f38])).
% 3.67/0.99  
% 3.67/0.99  fof(f68,plain,(
% 3.67/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f39])).
% 3.67/0.99  
% 3.67/0.99  fof(f79,plain,(
% 3.67/0.99    k1_xboole_0 != sK0),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f4,axiom,(
% 3.67/0.99    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f50,plain,(
% 3.67/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.67/0.99    inference(cnf_transformation,[],[f4])).
% 3.67/0.99  
% 3.67/0.99  fof(f13,axiom,(
% 3.67/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f62,plain,(
% 3.67/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f13])).
% 3.67/0.99  
% 3.67/0.99  fof(f84,plain,(
% 3.67/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.67/0.99    inference(definition_unfolding,[],[f50,f62])).
% 3.67/0.99  
% 3.67/0.99  fof(f9,axiom,(
% 3.67/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f28,plain,(
% 3.67/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.67/0.99    inference(ennf_transformation,[],[f9])).
% 3.67/0.99  
% 3.67/0.99  fof(f29,plain,(
% 3.67/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/0.99    inference(flattening,[],[f28])).
% 3.67/0.99  
% 3.67/0.99  fof(f42,plain,(
% 3.67/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/0.99    inference(nnf_transformation,[],[f29])).
% 3.67/0.99  
% 3.67/0.99  fof(f56,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/0.99    inference(cnf_transformation,[],[f42])).
% 3.67/0.99  
% 3.67/0.99  fof(f11,axiom,(
% 3.67/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f19,plain,(
% 3.67/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.67/0.99    inference(pure_predicate_removal,[],[f11])).
% 3.67/0.99  
% 3.67/0.99  fof(f60,plain,(
% 3.67/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.67/0.99    inference(cnf_transformation,[],[f19])).
% 3.67/0.99  
% 3.67/0.99  fof(f10,axiom,(
% 3.67/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f30,plain,(
% 3.67/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.67/0.99    inference(ennf_transformation,[],[f10])).
% 3.67/0.99  
% 3.67/0.99  fof(f31,plain,(
% 3.67/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.67/0.99    inference(flattening,[],[f30])).
% 3.67/0.99  
% 3.67/0.99  fof(f59,plain,(
% 3.67/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f31])).
% 3.67/0.99  
% 3.67/0.99  fof(f76,plain,(
% 3.67/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f15,axiom,(
% 3.67/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f36,plain,(
% 3.67/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.67/0.99    inference(ennf_transformation,[],[f15])).
% 3.67/0.99  
% 3.67/0.99  fof(f37,plain,(
% 3.67/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.67/0.99    inference(flattening,[],[f36])).
% 3.67/0.99  
% 3.67/0.99  fof(f66,plain,(
% 3.67/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f37])).
% 3.67/0.99  
% 3.67/0.99  fof(f6,axiom,(
% 3.67/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f23,plain,(
% 3.67/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.67/0.99    inference(ennf_transformation,[],[f6])).
% 3.67/0.99  
% 3.67/0.99  fof(f24,plain,(
% 3.67/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.67/0.99    inference(flattening,[],[f23])).
% 3.67/0.99  
% 3.67/0.99  fof(f53,plain,(
% 3.67/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f24])).
% 3.67/0.99  
% 3.67/0.99  fof(f2,axiom,(
% 3.67/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f47,plain,(
% 3.67/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.67/0.99    inference(cnf_transformation,[],[f2])).
% 3.67/0.99  
% 3.67/0.99  fof(f1,axiom,(
% 3.67/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f20,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.67/0.99    inference(ennf_transformation,[],[f1])).
% 3.67/0.99  
% 3.67/0.99  fof(f46,plain,(
% 3.67/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f20])).
% 3.67/0.99  
% 3.67/0.99  fof(f3,axiom,(
% 3.67/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f49,plain,(
% 3.67/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.67/0.99    inference(cnf_transformation,[],[f3])).
% 3.67/0.99  
% 3.67/0.99  fof(f82,plain,(
% 3.67/0.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.67/0.99    inference(definition_unfolding,[],[f49,f62])).
% 3.67/0.99  
% 3.67/0.99  fof(f12,axiom,(
% 3.67/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f32,plain,(
% 3.67/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.67/0.99    inference(ennf_transformation,[],[f12])).
% 3.67/0.99  
% 3.67/0.99  fof(f33,plain,(
% 3.67/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.67/0.99    inference(flattening,[],[f32])).
% 3.67/0.99  
% 3.67/0.99  fof(f61,plain,(
% 3.67/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f33])).
% 3.67/0.99  
% 3.67/0.99  fof(f7,axiom,(
% 3.67/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f25,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.67/0.99    inference(ennf_transformation,[],[f7])).
% 3.67/0.99  
% 3.67/0.99  fof(f26,plain,(
% 3.67/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.67/0.99    inference(flattening,[],[f25])).
% 3.67/0.99  
% 3.67/0.99  fof(f54,plain,(
% 3.67/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f26])).
% 3.67/0.99  
% 3.67/0.99  fof(f86,plain,(
% 3.67/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/0.99    inference(definition_unfolding,[],[f54,f62])).
% 3.67/0.99  
% 3.67/0.99  fof(f5,axiom,(
% 3.67/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f21,plain,(
% 3.67/0.99    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.67/0.99    inference(ennf_transformation,[],[f5])).
% 3.67/0.99  
% 3.67/0.99  fof(f22,plain,(
% 3.67/0.99    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.67/0.99    inference(flattening,[],[f21])).
% 3.67/0.99  
% 3.67/0.99  fof(f51,plain,(
% 3.67/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f22])).
% 3.67/0.99  
% 3.67/0.99  fof(f85,plain,(
% 3.67/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/0.99    inference(definition_unfolding,[],[f51,f62])).
% 3.67/0.99  
% 3.67/0.99  fof(f8,axiom,(
% 3.67/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f27,plain,(
% 3.67/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/0.99    inference(ennf_transformation,[],[f8])).
% 3.67/0.99  
% 3.67/0.99  fof(f55,plain,(
% 3.67/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/0.99    inference(cnf_transformation,[],[f27])).
% 3.67/0.99  
% 3.67/0.99  fof(f81,plain,(
% 3.67/0.99    k2_funct_1(sK2) != sK3),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f78,plain,(
% 3.67/0.99    v2_funct_1(sK2)),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f80,plain,(
% 3.67/0.99    k1_xboole_0 != sK1),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f52,plain,(
% 3.67/0.99    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f24])).
% 3.67/0.99  
% 3.67/0.99  fof(f48,plain,(
% 3.67/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.67/0.99    inference(cnf_transformation,[],[f3])).
% 3.67/0.99  
% 3.67/0.99  fof(f83,plain,(
% 3.67/0.99    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.67/0.99    inference(definition_unfolding,[],[f48,f62])).
% 3.67/0.99  
% 3.67/0.99  cnf(c_16,plain,
% 3.67/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.67/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.67/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.67/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.67/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.67/0.99      | ~ v1_funct_1(X2)
% 3.67/0.99      | ~ v1_funct_1(X3)
% 3.67/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.67/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_27,negated_conjecture,
% 3.67/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.67/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_381,plain,
% 3.67/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/0.99      | ~ v1_funct_2(X3,X2,X1)
% 3.67/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.99      | ~ v1_funct_1(X3)
% 3.67/0.99      | ~ v1_funct_1(X0)
% 3.67/0.99      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.67/0.99      | k2_relset_1(X2,X1,X3) = X1
% 3.67/0.99      | k6_partfun1(X1) != k6_partfun1(sK0)
% 3.67/0.99      | sK0 != X1 ),
% 3.67/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_382,plain,
% 3.67/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 3.67/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 3.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.67/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.67/0.99      | ~ v1_funct_1(X2)
% 3.67/0.99      | ~ v1_funct_1(X0)
% 3.67/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.67/0.99      | k2_relset_1(X1,sK0,X0) = sK0
% 3.67/0.99      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.67/0.99      inference(unflattening,[status(thm)],[c_381]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_464,plain,
% 3.67/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 3.67/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 3.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.67/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.67/0.99      | ~ v1_funct_1(X0)
% 3.67/0.99      | ~ v1_funct_1(X2)
% 3.67/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.67/0.99      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.67/0.99      inference(equality_resolution_simp,[status(thm)],[c_382]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1096,plain,
% 3.67/0.99      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.67/0.99      | k2_relset_1(X0,sK0,X2) = sK0
% 3.67/0.99      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.67/0.99      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.67/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.67/0.99      | v1_funct_1(X2) != iProver_top
% 3.67/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1641,plain,
% 3.67/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.67/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.67/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.67/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.67/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.67/0.99      | v1_funct_1(sK3) != iProver_top
% 3.67/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.67/0.99      inference(equality_resolution,[status(thm)],[c_1096]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_34,negated_conjecture,
% 3.67/0.99      ( v1_funct_1(sK2) ),
% 3.67/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_35,plain,
% 3.67/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_33,negated_conjecture,
% 3.67/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.67/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_36,plain,
% 3.67/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_32,negated_conjecture,
% 3.67/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.67/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_37,plain,
% 3.67/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_31,negated_conjecture,
% 3.67/0.99      ( v1_funct_1(sK3) ),
% 3.67/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_38,plain,
% 3.67/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_30,negated_conjecture,
% 3.67/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_39,plain,
% 3.67/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_29,negated_conjecture,
% 3.67/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.67/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_40,plain,
% 3.67/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1807,plain,
% 3.67/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_1641,c_35,c_36,c_37,c_38,c_39,c_40]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_22,plain,
% 3.67/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.99      | ~ v1_funct_1(X0)
% 3.67/0.99      | ~ v2_funct_1(X0)
% 3.67/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.67/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.67/0.99      | k1_xboole_0 = X2 ),
% 3.67/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1107,plain,
% 3.67/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.67/0.99      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 3.67/0.99      | k1_xboole_0 = X1
% 3.67/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.67/0.99      | v1_funct_1(X2) != iProver_top
% 3.67/0.99      | v2_funct_1(X2) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3617,plain,
% 3.67/0.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 3.67/0.99      | sK0 = k1_xboole_0
% 3.67/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.67/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.67/0.99      | v1_funct_1(sK3) != iProver_top
% 3.67/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1807,c_1107]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_25,negated_conjecture,
% 3.67/0.99      ( k1_xboole_0 != sK0 ),
% 3.67/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_627,plain,( X0 = X0 ),theory(equality) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_658,plain,
% 3.67/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_627]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_628,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1204,plain,
% 3.67/0.99      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_628]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1205,plain,
% 3.67/0.99      ( sK0 != k1_xboole_0
% 3.67/0.99      | k1_xboole_0 = sK0
% 3.67/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_1204]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4,plain,
% 3.67/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.67/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1121,plain,
% 3.67/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_11,plain,
% 3.67/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.67/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.67/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.67/0.99      | X3 = X2 ),
% 3.67/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_368,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.99      | X3 = X0
% 3.67/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.67/0.99      | k6_partfun1(sK0) != X3
% 3.67/0.99      | sK0 != X2
% 3.67/0.99      | sK0 != X1 ),
% 3.67/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_369,plain,
% 3.67/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.67/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.67/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.67/0.99      inference(unflattening,[status(thm)],[c_368]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_14,plain,
% 3.67/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.67/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_377,plain,
% 3.67/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.67/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.67/0.99      inference(forward_subsumption_resolution,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_369,c_14]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1097,plain,
% 3.67/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.67/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_12,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.67/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.67/0.99      | ~ v1_funct_1(X0)
% 3.67/0.99      | ~ v1_funct_1(X3) ),
% 3.67/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1206,plain,
% 3.67/0.99      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.67/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.67/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.67/0.99      | ~ v1_funct_1(sK3)
% 3.67/0.99      | ~ v1_funct_1(sK2) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1734,plain,
% 3.67/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_1097,c_34,c_32,c_31,c_29,c_377,c_1206]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_28,negated_conjecture,
% 3.67/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.67/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_18,plain,
% 3.67/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/0.99      | ~ v1_funct_2(X3,X2,X4)
% 3.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.67/0.99      | ~ v1_funct_1(X3)
% 3.67/0.99      | ~ v1_funct_1(X0)
% 3.67/0.99      | v2_funct_1(X3)
% 3.67/0.99      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 3.67/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.67/0.99      | k1_xboole_0 = X4 ),
% 3.67/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1111,plain,
% 3.67/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.67/0.99      | k1_xboole_0 = X3
% 3.67/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.67/0.99      | v1_funct_2(X4,X1,X3) != iProver_top
% 3.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.67/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 3.67/0.99      | v1_funct_1(X2) != iProver_top
% 3.67/0.99      | v1_funct_1(X4) != iProver_top
% 3.67/0.99      | v2_funct_1(X4) = iProver_top
% 3.67/0.99      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4799,plain,
% 3.67/0.99      ( k1_xboole_0 = X0
% 3.67/0.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.67/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.67/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.67/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.67/0.99      | v1_funct_1(X1) != iProver_top
% 3.67/0.99      | v1_funct_1(sK2) != iProver_top
% 3.67/0.99      | v2_funct_1(X1) = iProver_top
% 3.67/0.99      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_28,c_1111]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4846,plain,
% 3.67/0.99      ( v1_funct_1(X1) != iProver_top
% 3.67/0.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.67/0.99      | k1_xboole_0 = X0
% 3.67/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.67/0.99      | v2_funct_1(X1) = iProver_top
% 3.67/0.99      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_4799,c_35,c_36,c_37]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4847,plain,
% 3.67/0.99      ( k1_xboole_0 = X0
% 3.67/0.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.67/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.67/0.99      | v1_funct_1(X1) != iProver_top
% 3.67/0.99      | v2_funct_1(X1) = iProver_top
% 3.67/0.99      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.67/0.99      inference(renaming,[status(thm)],[c_4846]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4850,plain,
% 3.67/0.99      ( sK0 = k1_xboole_0
% 3.67/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.67/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.67/0.99      | v1_funct_1(sK3) != iProver_top
% 3.67/0.99      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.67/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1734,c_4847]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4853,plain,
% 3.67/0.99      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.67/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_4850,c_38,c_39,c_40,c_25,c_658,c_1205]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4857,plain,
% 3.67/0.99      ( v2_funct_1(sK3) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1121,c_4853]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7577,plain,
% 3.67/0.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_3617,c_38,c_39,c_40,c_25,c_658,c_1205,c_4857]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1103,plain,
% 3.67/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_6,plain,
% 3.67/0.99      ( ~ v1_funct_1(X0)
% 3.67/0.99      | ~ v2_funct_1(X0)
% 3.67/0.99      | ~ v1_relat_1(X0)
% 3.67/0.99      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1119,plain,
% 3.67/0.99      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 3.67/0.99      | v1_funct_1(X0) != iProver_top
% 3.67/0.99      | v2_funct_1(X0) != iProver_top
% 3.67/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2673,plain,
% 3.67/0.99      ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 3.67/0.99      | v2_funct_1(sK3) != iProver_top
% 3.67/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1103,c_1119]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1,plain,
% 3.67/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.67/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1122,plain,
% 3.67/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1105,plain,
% 3.67/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_0,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.67/0.99      | ~ v1_relat_1(X1)
% 3.67/0.99      | v1_relat_1(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1123,plain,
% 3.67/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.67/0.99      | v1_relat_1(X1) != iProver_top
% 3.67/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2277,plain,
% 3.67/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.67/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1105,c_1123]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2424,plain,
% 3.67/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1122,c_2277]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2783,plain,
% 3.67/0.99      ( v2_funct_1(sK3) != iProver_top
% 3.67/0.99      | k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_2673,c_2424]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2784,plain,
% 3.67/0.99      ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 3.67/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.67/0.99      inference(renaming,[status(thm)],[c_2783]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4894,plain,
% 3.67/0.99      ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_4857,c_2784]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7580,plain,
% 3.67/0.99      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 3.67/0.99      inference(demodulation,[status(thm)],[c_7577,c_4894]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2,plain,
% 3.67/0.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.67/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7581,plain,
% 3.67/0.99      ( k1_relat_1(sK3) = sK1 ),
% 3.67/0.99      inference(demodulation,[status(thm)],[c_7580,c_2]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1102,plain,
% 3.67/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_15,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.67/0.99      | ~ v1_funct_1(X0)
% 3.67/0.99      | ~ v1_funct_1(X3)
% 3.67/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1113,plain,
% 3.67/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.67/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.67/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.67/0.99      | v1_funct_1(X5) != iProver_top
% 3.67/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2771,plain,
% 3.67/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.67/0.99      | v1_funct_1(X2) != iProver_top
% 3.67/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1105,c_1113]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2855,plain,
% 3.67/0.99      ( v1_funct_1(X2) != iProver_top
% 3.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.67/0.99      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_2771,c_38]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2856,plain,
% 3.67/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.67/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.67/0.99      inference(renaming,[status(thm)],[c_2855]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2863,plain,
% 3.67/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.67/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1102,c_2856]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2864,plain,
% 3.67/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.67/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.67/0.99      inference(light_normalisation,[status(thm)],[c_2863,c_1734]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3609,plain,
% 3.67/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_2864,c_35]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_8,plain,
% 3.67/0.99      ( ~ v1_funct_1(X0)
% 3.67/0.99      | ~ v1_funct_1(X1)
% 3.67/0.99      | ~ v2_funct_1(X1)
% 3.67/0.99      | ~ v1_relat_1(X1)
% 3.67/0.99      | ~ v1_relat_1(X0)
% 3.67/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.67/0.99      | k2_funct_1(X1) = X0
% 3.67/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.67/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_5,plain,
% 3.67/0.99      ( ~ v1_funct_1(X0)
% 3.67/0.99      | ~ v1_funct_1(X1)
% 3.67/0.99      | v2_funct_1(X1)
% 3.67/0.99      | ~ v1_relat_1(X1)
% 3.67/0.99      | ~ v1_relat_1(X0)
% 3.67/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1)) ),
% 3.67/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_183,plain,
% 3.67/0.99      ( ~ v1_funct_1(X1)
% 3.67/0.99      | ~ v1_funct_1(X0)
% 3.67/0.99      | ~ v1_relat_1(X1)
% 3.67/0.99      | ~ v1_relat_1(X0)
% 3.67/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.67/0.99      | k2_funct_1(X1) = X0
% 3.67/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.67/0.99      inference(global_propositional_subsumption,[status(thm)],[c_8,c_5]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_184,plain,
% 3.67/0.99      ( ~ v1_funct_1(X0)
% 3.67/0.99      | ~ v1_funct_1(X1)
% 3.67/0.99      | ~ v1_relat_1(X1)
% 3.67/0.99      | ~ v1_relat_1(X0)
% 3.67/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.67/0.99      | k2_funct_1(X1) = X0
% 3.67/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.67/0.99      inference(renaming,[status(thm)],[c_183]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1099,plain,
% 3.67/0.99      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 3.67/0.99      | k2_funct_1(X0) = X1
% 3.67/0.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.67/0.99      | v1_funct_1(X1) != iProver_top
% 3.67/0.99      | v1_funct_1(X0) != iProver_top
% 3.67/0.99      | v1_relat_1(X0) != iProver_top
% 3.67/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_184]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3612,plain,
% 3.67/0.99      ( k2_funct_1(sK2) = sK3
% 3.67/0.99      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 3.67/0.99      | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
% 3.67/0.99      | v1_funct_1(sK3) != iProver_top
% 3.67/0.99      | v1_funct_1(sK2) != iProver_top
% 3.67/0.99      | v1_relat_1(sK3) != iProver_top
% 3.67/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_3609,c_1099]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_9,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1117,plain,
% 3.67/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1906,plain,
% 3.67/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1102,c_1117]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1907,plain,
% 3.67/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.67/0.99      inference(light_normalisation,[status(thm)],[c_1906,c_28]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3613,plain,
% 3.67/0.99      ( k2_funct_1(sK2) = sK3
% 3.67/0.99      | k1_relat_1(sK3) != sK1
% 3.67/0.99      | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
% 3.67/0.99      | v1_funct_1(sK3) != iProver_top
% 3.67/0.99      | v1_funct_1(sK2) != iProver_top
% 3.67/0.99      | v1_relat_1(sK3) != iProver_top
% 3.67/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.67/0.99      inference(light_normalisation,[status(thm)],[c_3612,c_1907]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_23,negated_conjecture,
% 3.67/0.99      ( k2_funct_1(sK2) != sK3 ),
% 3.67/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2278,plain,
% 3.67/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.67/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1102,c_1123]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2427,plain,
% 3.67/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1122,c_2278]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4438,plain,
% 3.67/0.99      ( k1_relat_1(sK3) != sK1
% 3.67/0.99      | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_3613,c_35,c_38,c_23,c_2424,c_2427]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3616,plain,
% 3.67/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.67/0.99      | sK1 = k1_xboole_0
% 3.67/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.67/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.67/0.99      | v1_funct_1(sK2) != iProver_top
% 3.67/0.99      | v2_funct_1(sK2) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_28,c_1107]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_26,negated_conjecture,
% 3.67/0.99      ( v2_funct_1(sK2) ),
% 3.67/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_24,negated_conjecture,
% 3.67/0.99      ( k1_xboole_0 != sK1 ),
% 3.67/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1167,plain,
% 3.67/0.99      ( ~ v1_funct_2(X0,X1,sK1)
% 3.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.67/0.99      | ~ v1_funct_1(X0)
% 3.67/0.99      | ~ v2_funct_1(X0)
% 3.67/0.99      | k2_relset_1(X1,sK1,X0) != sK1
% 3.67/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.67/0.99      | k1_xboole_0 = sK1 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1297,plain,
% 3.67/0.99      ( ~ v1_funct_2(sK2,X0,sK1)
% 3.67/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 3.67/0.99      | ~ v1_funct_1(sK2)
% 3.67/0.99      | ~ v2_funct_1(sK2)
% 3.67/0.99      | k2_relset_1(X0,sK1,sK2) != sK1
% 3.67/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.67/0.99      | k1_xboole_0 = sK1 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_1167]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1528,plain,
% 3.67/0.99      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.67/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.67/0.99      | ~ v1_funct_1(sK2)
% 3.67/0.99      | ~ v2_funct_1(sK2)
% 3.67/0.99      | k2_relset_1(sK0,sK1,sK2) != sK1
% 3.67/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.67/0.99      | k1_xboole_0 = sK1 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_1297]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3802,plain,
% 3.67/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_3616,c_34,c_33,c_32,c_28,c_26,c_24,c_1528]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1100,plain,
% 3.67/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7,plain,
% 3.67/0.99      ( ~ v1_funct_1(X0)
% 3.67/0.99      | ~ v2_funct_1(X0)
% 3.67/0.99      | ~ v1_relat_1(X0)
% 3.67/0.99      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1118,plain,
% 3.67/0.99      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 3.67/0.99      | v1_funct_1(X0) != iProver_top
% 3.67/0.99      | v2_funct_1(X0) != iProver_top
% 3.67/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2286,plain,
% 3.67/0.99      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 3.67/0.99      | v2_funct_1(sK2) != iProver_top
% 3.67/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1100,c_1118]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_42,plain,
% 3.67/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2447,plain,
% 3.67/0.99      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_2286,c_42,c_2427]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3805,plain,
% 3.67/0.99      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 3.67/0.99      inference(demodulation,[status(thm)],[c_3802,c_2447]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3,plain,
% 3.67/0.99      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.67/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3806,plain,
% 3.67/0.99      ( k1_relat_1(sK2) = sK0 ),
% 3.67/0.99      inference(demodulation,[status(thm)],[c_3805,c_3]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4440,plain,
% 3.67/0.99      ( k1_relat_1(sK3) != sK1 | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.67/0.99      inference(light_normalisation,[status(thm)],[c_4438,c_3806]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4441,plain,
% 3.67/0.99      ( k1_relat_1(sK3) != sK1 ),
% 3.67/0.99      inference(equality_resolution_simp,[status(thm)],[c_4440]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(contradiction,plain,
% 3.67/0.99      ( $false ),
% 3.67/0.99      inference(minisat,[status(thm)],[c_7581,c_4441]) ).
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/0.99  
% 3.67/0.99  ------                               Statistics
% 3.67/0.99  
% 3.67/0.99  ------ General
% 3.67/0.99  
% 3.67/0.99  abstr_ref_over_cycles:                  0
% 3.67/0.99  abstr_ref_under_cycles:                 0
% 3.67/0.99  gc_basic_clause_elim:                   0
% 3.67/0.99  forced_gc_time:                         0
% 3.67/0.99  parsing_time:                           0.01
% 3.67/0.99  unif_index_cands_time:                  0.
% 3.67/0.99  unif_index_add_time:                    0.
% 3.67/0.99  orderings_time:                         0.
% 3.67/0.99  out_proof_time:                         0.015
% 3.67/0.99  total_time:                             0.379
% 3.67/0.99  num_of_symbols:                         51
% 3.67/0.99  num_of_terms:                           12778
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing
% 3.67/0.99  
% 3.67/0.99  num_of_splits:                          0
% 3.67/0.99  num_of_split_atoms:                     0
% 3.67/0.99  num_of_reused_defs:                     0
% 3.67/0.99  num_eq_ax_congr_red:                    0
% 3.67/0.99  num_of_sem_filtered_clauses:            1
% 3.67/0.99  num_of_subtypes:                        0
% 3.67/0.99  monotx_restored_types:                  0
% 3.67/0.99  sat_num_of_epr_types:                   0
% 3.67/0.99  sat_num_of_non_cyclic_types:            0
% 3.67/0.99  sat_guarded_non_collapsed_types:        0
% 3.67/0.99  num_pure_diseq_elim:                    0
% 3.67/0.99  simp_replaced_by:                       0
% 3.67/0.99  res_preprocessed:                       170
% 3.67/0.99  prep_upred:                             0
% 3.67/0.99  prep_unflattend:                        12
% 3.67/0.99  smt_new_axioms:                         0
% 3.67/0.99  pred_elim_cands:                        5
% 3.67/0.99  pred_elim:                              1
% 3.67/0.99  pred_elim_cl:                           1
% 3.67/0.99  pred_elim_cycles:                       3
% 3.67/0.99  merged_defs:                            0
% 3.67/0.99  merged_defs_ncl:                        0
% 3.67/0.99  bin_hyper_res:                          0
% 3.67/0.99  prep_cycles:                            4
% 3.67/0.99  pred_elim_time:                         0.004
% 3.67/0.99  splitting_time:                         0.
% 3.67/0.99  sem_filter_time:                        0.
% 3.67/0.99  monotx_time:                            0.001
% 3.67/0.99  subtype_inf_time:                       0.
% 3.67/0.99  
% 3.67/0.99  ------ Problem properties
% 3.67/0.99  
% 3.67/0.99  clauses:                                34
% 3.67/0.99  conjectures:                            11
% 3.67/0.99  epr:                                    7
% 3.67/0.99  horn:                                   30
% 3.67/0.99  ground:                                 12
% 3.67/0.99  unary:                                  16
% 3.67/0.99  binary:                                 2
% 3.67/0.99  lits:                                   127
% 3.67/0.99  lits_eq:                                31
% 3.67/0.99  fd_pure:                                0
% 3.67/0.99  fd_pseudo:                              0
% 3.67/0.99  fd_cond:                                4
% 3.67/0.99  fd_pseudo_cond:                         1
% 3.67/0.99  ac_symbols:                             0
% 3.67/0.99  
% 3.67/0.99  ------ Propositional Solver
% 3.67/0.99  
% 3.67/0.99  prop_solver_calls:                      30
% 3.67/0.99  prop_fast_solver_calls:                 1744
% 3.67/0.99  smt_solver_calls:                       0
% 3.67/0.99  smt_fast_solver_calls:                  0
% 3.67/0.99  prop_num_of_clauses:                    4305
% 3.67/0.99  prop_preprocess_simplified:             9290
% 3.67/0.99  prop_fo_subsumed:                       115
% 3.67/0.99  prop_solver_time:                       0.
% 3.67/0.99  smt_solver_time:                        0.
% 3.67/0.99  smt_fast_solver_time:                   0.
% 3.67/0.99  prop_fast_solver_time:                  0.
% 3.67/0.99  prop_unsat_core_time:                   0.
% 3.67/0.99  
% 3.67/0.99  ------ QBF
% 3.67/0.99  
% 3.67/0.99  qbf_q_res:                              0
% 3.67/0.99  qbf_num_tautologies:                    0
% 3.67/0.99  qbf_prep_cycles:                        0
% 3.67/0.99  
% 3.67/0.99  ------ BMC1
% 3.67/0.99  
% 3.67/0.99  bmc1_current_bound:                     -1
% 3.67/0.99  bmc1_last_solved_bound:                 -1
% 3.67/0.99  bmc1_unsat_core_size:                   -1
% 3.67/0.99  bmc1_unsat_core_parents_size:           -1
% 3.67/0.99  bmc1_merge_next_fun:                    0
% 3.67/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.67/0.99  
% 3.67/0.99  ------ Instantiation
% 3.67/0.99  
% 3.67/0.99  inst_num_of_clauses:                    1067
% 3.67/0.99  inst_num_in_passive:                    465
% 3.67/0.99  inst_num_in_active:                     484
% 3.67/0.99  inst_num_in_unprocessed:                118
% 3.67/0.99  inst_num_of_loops:                      630
% 3.67/0.99  inst_num_of_learning_restarts:          0
% 3.67/0.99  inst_num_moves_active_passive:          143
% 3.67/0.99  inst_lit_activity:                      0
% 3.67/0.99  inst_lit_activity_moves:                1
% 3.67/0.99  inst_num_tautologies:                   0
% 3.67/0.99  inst_num_prop_implied:                  0
% 3.67/0.99  inst_num_existing_simplified:           0
% 3.67/0.99  inst_num_eq_res_simplified:             0
% 3.67/0.99  inst_num_child_elim:                    0
% 3.67/0.99  inst_num_of_dismatching_blockings:      107
% 3.67/0.99  inst_num_of_non_proper_insts:           1038
% 3.67/0.99  inst_num_of_duplicates:                 0
% 3.67/0.99  inst_inst_num_from_inst_to_res:         0
% 3.67/0.99  inst_dismatching_checking_time:         0.
% 3.67/0.99  
% 3.67/0.99  ------ Resolution
% 3.67/0.99  
% 3.67/0.99  res_num_of_clauses:                     0
% 3.67/0.99  res_num_in_passive:                     0
% 3.67/0.99  res_num_in_active:                      0
% 3.67/0.99  res_num_of_loops:                       174
% 3.67/0.99  res_forward_subset_subsumed:            83
% 3.67/0.99  res_backward_subset_subsumed:           0
% 3.67/0.99  res_forward_subsumed:                   0
% 3.67/0.99  res_backward_subsumed:                  0
% 3.67/0.99  res_forward_subsumption_resolution:     2
% 3.67/0.99  res_backward_subsumption_resolution:    0
% 3.67/0.99  res_clause_to_clause_subsumption:       465
% 3.67/0.99  res_orphan_elimination:                 0
% 3.67/0.99  res_tautology_del:                      31
% 3.67/0.99  res_num_eq_res_simplified:              1
% 3.67/0.99  res_num_sel_changes:                    0
% 3.67/0.99  res_moves_from_active_to_pass:          0
% 3.67/0.99  
% 3.67/0.99  ------ Superposition
% 3.67/0.99  
% 3.67/0.99  sup_time_total:                         0.
% 3.67/0.99  sup_time_generating:                    0.
% 3.67/0.99  sup_time_sim_full:                      0.
% 3.67/0.99  sup_time_sim_immed:                     0.
% 3.67/0.99  
% 3.67/0.99  sup_num_of_clauses:                     231
% 3.67/0.99  sup_num_in_active:                      107
% 3.67/0.99  sup_num_in_passive:                     124
% 3.67/0.99  sup_num_of_loops:                       125
% 3.67/0.99  sup_fw_superposition:                   119
% 3.67/0.99  sup_bw_superposition:                   123
% 3.67/0.99  sup_immediate_simplified:               87
% 3.67/0.99  sup_given_eliminated:                   0
% 3.67/0.99  comparisons_done:                       0
% 3.67/0.99  comparisons_avoided:                    0
% 3.67/0.99  
% 3.67/0.99  ------ Simplifications
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  sim_fw_subset_subsumed:                 7
% 3.67/0.99  sim_bw_subset_subsumed:                 12
% 3.67/0.99  sim_fw_subsumed:                        14
% 3.67/0.99  sim_bw_subsumed:                        6
% 3.67/0.99  sim_fw_subsumption_res:                 0
% 3.67/0.99  sim_bw_subsumption_res:                 0
% 3.67/0.99  sim_tautology_del:                      0
% 3.67/0.99  sim_eq_tautology_del:                   8
% 3.67/0.99  sim_eq_res_simp:                        1
% 3.67/0.99  sim_fw_demodulated:                     9
% 3.67/0.99  sim_bw_demodulated:                     5
% 3.67/0.99  sim_light_normalised:                   65
% 3.67/0.99  sim_joinable_taut:                      0
% 3.67/0.99  sim_joinable_simp:                      0
% 3.67/0.99  sim_ac_normalised:                      0
% 3.67/0.99  sim_smt_subsumption:                    0
% 3.67/0.99  
%------------------------------------------------------------------------------
