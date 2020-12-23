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
% DateTime   : Thu Dec  3 12:02:56 EST 2020

% Result     : Theorem 19.68s
% Output     : CNFRefutation 19.68s
% Verified   : 
% Statistics : Number of formulae       :  234 (6865 expanded)
%              Number of clauses        :  145 (1884 expanded)
%              Number of leaves         :   23 (1814 expanded)
%              Depth                    :   30
%              Number of atoms          :  921 (60836 expanded)
%              Number of equality atoms :  459 (21894 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f51,f55,f54])).

fof(f96,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f20,axiom,(
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

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f98,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f56])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f65,f78])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f56])).

fof(f18,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f101,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f63,f78])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f62,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f102,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f62,f78])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f56])).

fof(f97,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_513,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_514,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_602,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_514])).

cnf(c_1387,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_1932,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1387])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_43,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_44,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_46,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_47,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_48,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2139,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1932,c_43,c_44,c_45,c_46,c_47,c_48])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1398,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3219,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2139,c_1398])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_822,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_855,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_823,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1507,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_1508,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_7,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_5059,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5060,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5059])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_35])).

cnf(c_501,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_19,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_509,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_501,c_19])).

cnf(c_1388,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1509,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2132,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1388,c_42,c_40,c_39,c_37,c_509,c_1509])).

cnf(c_36,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f82])).

cnf(c_1405,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6509,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_36,c_1405])).

cnf(c_6518,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6509,c_43,c_44,c_45])).

cnf(c_6519,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6518])).

cnf(c_6522,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2132,c_6519])).

cnf(c_7182,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3219,c_46,c_47,c_48,c_33,c_855,c_1508,c_5060,c_6522])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1413,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7184,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
    | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7182,c_1413])).

cnf(c_1396,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1411,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2372,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1396,c_1411])).

cnf(c_2375,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2372,c_2139])).

cnf(c_6633,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6522,c_46,c_47,c_48,c_33,c_855,c_1508,c_5060])).

cnf(c_1394,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1414,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3225,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1394,c_1414])).

cnf(c_3228,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK0
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3225,c_2375])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1561,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1916,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1561])).

cnf(c_1917,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1916])).

cnf(c_4159,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k1_relat_1(k2_funct_1(sK3)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3228,c_48,c_1917])).

cnf(c_4160,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK0
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4159])).

cnf(c_6637,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK0 ),
    inference(superposition,[status(thm)],[c_6633,c_4160])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1415,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3272,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1394,c_1415])).

cnf(c_3409,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3272,c_48,c_1917])).

cnf(c_3410,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3409])).

cnf(c_6638,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6633,c_3410])).

cnf(c_7185,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
    | sK0 != sK0
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7184,c_2375,c_6637,c_6638])).

cnf(c_7186,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7185])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1400,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(X2)) = iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5140,plain,
    ( v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2139,c_1400])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1402,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5688,plain,
    ( v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2139,c_1402])).

cnf(c_2054,plain,
    ( ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_15495,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2054])).

cnf(c_15496,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15495])).

cnf(c_58002,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7186,c_46,c_47,c_48,c_33,c_855,c_1508,c_1917,c_5060,c_5140,c_5688,c_6522,c_15496])).

cnf(c_4,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1418,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6667,plain,
    ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k2_relat_1(k2_funct_1(sK3))
    | r1_tarski(sK0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6637,c_1418])).

cnf(c_6668,plain,
    ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | r1_tarski(sK0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6667,c_6638])).

cnf(c_18631,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(sK0,k2_relat_1(X0)) != iProver_top
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6668,c_46,c_47,c_48,c_33,c_855,c_1508,c_5060,c_5688,c_6522,c_15496])).

cnf(c_18632,plain,
    ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | r1_tarski(sK0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_18631])).

cnf(c_18639,plain,
    ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | r1_tarski(sK0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_18632])).

cnf(c_18671,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
    | r1_tarski(sK0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18639,c_7182])).

cnf(c_5,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_18672,plain,
    ( k1_relat_1(sK3) = sK1
    | r1_tarski(sK0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18671,c_5])).

cnf(c_5691,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5688])).

cnf(c_6524,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6522])).

cnf(c_1408,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_416,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_2])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_13,c_12,c_2])).

cnf(c_421,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(renaming,[status(thm)],[c_420])).

cnf(c_1390,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_2575,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_1390])).

cnf(c_6,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2578,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2575,c_6])).

cnf(c_3280,plain,
    ( k2_relat_1(k5_relat_1(sK3,X0)) = k2_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),sK0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_1418])).

cnf(c_9206,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK0) != iProver_top
    | k2_relat_1(k5_relat_1(sK3,X0)) = k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3280,c_48,c_1917])).

cnf(c_9207,plain,
    ( k2_relat_1(k5_relat_1(sK3,X0)) = k2_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),sK0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9206])).

cnf(c_9214,plain,
    ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k2_relat_1(k2_funct_1(sK3))
    | r1_tarski(sK0,sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6637,c_9207])).

cnf(c_9217,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
    | r1_tarski(sK0,sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9214,c_6638,c_7182])).

cnf(c_9218,plain,
    ( k1_relat_1(sK3) = sK1
    | r1_tarski(sK0,sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9217,c_5])).

cnf(c_9227,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2578,c_9218])).

cnf(c_9228,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(sK3) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9227])).

cnf(c_19104,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18672,c_39,c_38,c_37,c_33,c_855,c_1508,c_5059,c_5691,c_6524,c_9228,c_15495])).

cnf(c_1393,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1407,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5317,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1396,c_1407])).

cnf(c_5457,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5317,c_46])).

cnf(c_5458,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5457])).

cnf(c_5465,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_5458])).

cnf(c_5466,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5465,c_2132])).

cnf(c_5596,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5466,c_43])).

cnf(c_5832,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5596,c_1413])).

cnf(c_2373,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1393,c_1411])).

cnf(c_2374,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2373,c_36])).

cnf(c_5833,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5832,c_2374,c_2375])).

cnf(c_5834,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5833])).

cnf(c_2040,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2041,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2040])).

cnf(c_11053,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5834,c_43,c_45,c_46,c_47,c_48,c_33,c_855,c_1508,c_1917,c_2041,c_5060,c_6522])).

cnf(c_11054,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1 ),
    inference(renaming,[status(thm)],[c_11053])).

cnf(c_19128,plain,
    ( k2_funct_1(sK3) = sK2
    | sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_19104,c_11054])).

cnf(c_19136,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_19128])).

cnf(c_58006,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_58002,c_19104,c_19136])).

cnf(c_58007,plain,
    ( k2_funct_1(sK2) = sK3
    | v2_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_58006])).

cnf(c_31,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_50,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58007,c_31,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:46:50 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 19.68/3.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.68/3.01  
% 19.68/3.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.68/3.01  
% 19.68/3.01  ------  iProver source info
% 19.68/3.01  
% 19.68/3.01  git: date: 2020-06-30 10:37:57 +0100
% 19.68/3.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.68/3.01  git: non_committed_changes: false
% 19.68/3.01  git: last_make_outside_of_git: false
% 19.68/3.01  
% 19.68/3.01  ------ 
% 19.68/3.01  
% 19.68/3.01  ------ Input Options
% 19.68/3.01  
% 19.68/3.01  --out_options                           all
% 19.68/3.01  --tptp_safe_out                         true
% 19.68/3.01  --problem_path                          ""
% 19.68/3.01  --include_path                          ""
% 19.68/3.01  --clausifier                            res/vclausify_rel
% 19.68/3.01  --clausifier_options                    ""
% 19.68/3.01  --stdin                                 false
% 19.68/3.01  --stats_out                             all
% 19.68/3.01  
% 19.68/3.01  ------ General Options
% 19.68/3.01  
% 19.68/3.01  --fof                                   false
% 19.68/3.01  --time_out_real                         305.
% 19.68/3.01  --time_out_virtual                      -1.
% 19.68/3.01  --symbol_type_check                     false
% 19.68/3.01  --clausify_out                          false
% 19.68/3.01  --sig_cnt_out                           false
% 19.68/3.01  --trig_cnt_out                          false
% 19.68/3.01  --trig_cnt_out_tolerance                1.
% 19.68/3.01  --trig_cnt_out_sk_spl                   false
% 19.68/3.01  --abstr_cl_out                          false
% 19.68/3.01  
% 19.68/3.01  ------ Global Options
% 19.68/3.01  
% 19.68/3.01  --schedule                              default
% 19.68/3.01  --add_important_lit                     false
% 19.68/3.01  --prop_solver_per_cl                    1000
% 19.68/3.01  --min_unsat_core                        false
% 19.68/3.01  --soft_assumptions                      false
% 19.68/3.01  --soft_lemma_size                       3
% 19.68/3.01  --prop_impl_unit_size                   0
% 19.68/3.01  --prop_impl_unit                        []
% 19.68/3.01  --share_sel_clauses                     true
% 19.68/3.01  --reset_solvers                         false
% 19.68/3.01  --bc_imp_inh                            [conj_cone]
% 19.68/3.01  --conj_cone_tolerance                   3.
% 19.68/3.01  --extra_neg_conj                        none
% 19.68/3.01  --large_theory_mode                     true
% 19.68/3.01  --prolific_symb_bound                   200
% 19.68/3.01  --lt_threshold                          2000
% 19.68/3.01  --clause_weak_htbl                      true
% 19.68/3.01  --gc_record_bc_elim                     false
% 19.68/3.01  
% 19.68/3.01  ------ Preprocessing Options
% 19.68/3.01  
% 19.68/3.01  --preprocessing_flag                    true
% 19.68/3.01  --time_out_prep_mult                    0.1
% 19.68/3.01  --splitting_mode                        input
% 19.68/3.01  --splitting_grd                         true
% 19.68/3.01  --splitting_cvd                         false
% 19.68/3.01  --splitting_cvd_svl                     false
% 19.68/3.01  --splitting_nvd                         32
% 19.68/3.01  --sub_typing                            true
% 19.68/3.01  --prep_gs_sim                           true
% 19.68/3.01  --prep_unflatten                        true
% 19.68/3.01  --prep_res_sim                          true
% 19.68/3.01  --prep_upred                            true
% 19.68/3.01  --prep_sem_filter                       exhaustive
% 19.68/3.01  --prep_sem_filter_out                   false
% 19.68/3.01  --pred_elim                             true
% 19.68/3.01  --res_sim_input                         true
% 19.68/3.01  --eq_ax_congr_red                       true
% 19.68/3.01  --pure_diseq_elim                       true
% 19.68/3.01  --brand_transform                       false
% 19.68/3.01  --non_eq_to_eq                          false
% 19.68/3.01  --prep_def_merge                        true
% 19.68/3.01  --prep_def_merge_prop_impl              false
% 19.68/3.01  --prep_def_merge_mbd                    true
% 19.68/3.01  --prep_def_merge_tr_red                 false
% 19.68/3.01  --prep_def_merge_tr_cl                  false
% 19.68/3.01  --smt_preprocessing                     true
% 19.68/3.01  --smt_ac_axioms                         fast
% 19.68/3.01  --preprocessed_out                      false
% 19.68/3.01  --preprocessed_stats                    false
% 19.68/3.01  
% 19.68/3.01  ------ Abstraction refinement Options
% 19.68/3.01  
% 19.68/3.01  --abstr_ref                             []
% 19.68/3.01  --abstr_ref_prep                        false
% 19.68/3.01  --abstr_ref_until_sat                   false
% 19.68/3.01  --abstr_ref_sig_restrict                funpre
% 19.68/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.68/3.01  --abstr_ref_under                       []
% 19.68/3.01  
% 19.68/3.01  ------ SAT Options
% 19.68/3.01  
% 19.68/3.01  --sat_mode                              false
% 19.68/3.01  --sat_fm_restart_options                ""
% 19.68/3.01  --sat_gr_def                            false
% 19.68/3.01  --sat_epr_types                         true
% 19.68/3.01  --sat_non_cyclic_types                  false
% 19.68/3.01  --sat_finite_models                     false
% 19.68/3.01  --sat_fm_lemmas                         false
% 19.68/3.01  --sat_fm_prep                           false
% 19.68/3.01  --sat_fm_uc_incr                        true
% 19.68/3.01  --sat_out_model                         small
% 19.68/3.01  --sat_out_clauses                       false
% 19.68/3.01  
% 19.68/3.01  ------ QBF Options
% 19.68/3.01  
% 19.68/3.01  --qbf_mode                              false
% 19.68/3.01  --qbf_elim_univ                         false
% 19.68/3.01  --qbf_dom_inst                          none
% 19.68/3.01  --qbf_dom_pre_inst                      false
% 19.68/3.01  --qbf_sk_in                             false
% 19.68/3.01  --qbf_pred_elim                         true
% 19.68/3.01  --qbf_split                             512
% 19.68/3.01  
% 19.68/3.01  ------ BMC1 Options
% 19.68/3.01  
% 19.68/3.01  --bmc1_incremental                      false
% 19.68/3.01  --bmc1_axioms                           reachable_all
% 19.68/3.01  --bmc1_min_bound                        0
% 19.68/3.01  --bmc1_max_bound                        -1
% 19.68/3.01  --bmc1_max_bound_default                -1
% 19.68/3.01  --bmc1_symbol_reachability              true
% 19.68/3.01  --bmc1_property_lemmas                  false
% 19.68/3.01  --bmc1_k_induction                      false
% 19.68/3.01  --bmc1_non_equiv_states                 false
% 19.68/3.01  --bmc1_deadlock                         false
% 19.68/3.01  --bmc1_ucm                              false
% 19.68/3.01  --bmc1_add_unsat_core                   none
% 19.68/3.01  --bmc1_unsat_core_children              false
% 19.68/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.68/3.01  --bmc1_out_stat                         full
% 19.68/3.01  --bmc1_ground_init                      false
% 19.68/3.01  --bmc1_pre_inst_next_state              false
% 19.68/3.01  --bmc1_pre_inst_state                   false
% 19.68/3.01  --bmc1_pre_inst_reach_state             false
% 19.68/3.01  --bmc1_out_unsat_core                   false
% 19.68/3.01  --bmc1_aig_witness_out                  false
% 19.68/3.01  --bmc1_verbose                          false
% 19.68/3.01  --bmc1_dump_clauses_tptp                false
% 19.68/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.68/3.01  --bmc1_dump_file                        -
% 19.68/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.68/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.68/3.01  --bmc1_ucm_extend_mode                  1
% 19.68/3.01  --bmc1_ucm_init_mode                    2
% 19.68/3.01  --bmc1_ucm_cone_mode                    none
% 19.68/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.68/3.01  --bmc1_ucm_relax_model                  4
% 19.68/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.68/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.68/3.01  --bmc1_ucm_layered_model                none
% 19.68/3.01  --bmc1_ucm_max_lemma_size               10
% 19.68/3.01  
% 19.68/3.01  ------ AIG Options
% 19.68/3.01  
% 19.68/3.01  --aig_mode                              false
% 19.68/3.01  
% 19.68/3.01  ------ Instantiation Options
% 19.68/3.01  
% 19.68/3.01  --instantiation_flag                    true
% 19.68/3.01  --inst_sos_flag                         true
% 19.68/3.01  --inst_sos_phase                        true
% 19.68/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.68/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.68/3.01  --inst_lit_sel_side                     num_symb
% 19.68/3.01  --inst_solver_per_active                1400
% 19.68/3.01  --inst_solver_calls_frac                1.
% 19.68/3.01  --inst_passive_queue_type               priority_queues
% 19.68/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.68/3.01  --inst_passive_queues_freq              [25;2]
% 19.68/3.01  --inst_dismatching                      true
% 19.68/3.01  --inst_eager_unprocessed_to_passive     true
% 19.68/3.01  --inst_prop_sim_given                   true
% 19.68/3.01  --inst_prop_sim_new                     false
% 19.68/3.01  --inst_subs_new                         false
% 19.68/3.01  --inst_eq_res_simp                      false
% 19.68/3.01  --inst_subs_given                       false
% 19.68/3.01  --inst_orphan_elimination               true
% 19.68/3.01  --inst_learning_loop_flag               true
% 19.68/3.01  --inst_learning_start                   3000
% 19.68/3.01  --inst_learning_factor                  2
% 19.68/3.01  --inst_start_prop_sim_after_learn       3
% 19.68/3.01  --inst_sel_renew                        solver
% 19.68/3.01  --inst_lit_activity_flag                true
% 19.68/3.01  --inst_restr_to_given                   false
% 19.68/3.01  --inst_activity_threshold               500
% 19.68/3.01  --inst_out_proof                        true
% 19.68/3.01  
% 19.68/3.01  ------ Resolution Options
% 19.68/3.01  
% 19.68/3.01  --resolution_flag                       true
% 19.68/3.01  --res_lit_sel                           adaptive
% 19.68/3.01  --res_lit_sel_side                      none
% 19.68/3.01  --res_ordering                          kbo
% 19.68/3.01  --res_to_prop_solver                    active
% 19.68/3.01  --res_prop_simpl_new                    false
% 19.68/3.01  --res_prop_simpl_given                  true
% 19.68/3.01  --res_passive_queue_type                priority_queues
% 19.68/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.68/3.01  --res_passive_queues_freq               [15;5]
% 19.68/3.01  --res_forward_subs                      full
% 19.68/3.01  --res_backward_subs                     full
% 19.68/3.01  --res_forward_subs_resolution           true
% 19.68/3.01  --res_backward_subs_resolution          true
% 19.68/3.01  --res_orphan_elimination                true
% 19.68/3.01  --res_time_limit                        2.
% 19.68/3.01  --res_out_proof                         true
% 19.68/3.01  
% 19.68/3.01  ------ Superposition Options
% 19.68/3.01  
% 19.68/3.01  --superposition_flag                    true
% 19.68/3.01  --sup_passive_queue_type                priority_queues
% 19.68/3.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.68/3.01  --sup_passive_queues_freq               [8;1;4]
% 19.68/3.01  --demod_completeness_check              fast
% 19.68/3.01  --demod_use_ground                      true
% 19.68/3.01  --sup_to_prop_solver                    passive
% 19.68/3.01  --sup_prop_simpl_new                    true
% 19.68/3.01  --sup_prop_simpl_given                  true
% 19.68/3.01  --sup_fun_splitting                     true
% 19.68/3.01  --sup_smt_interval                      50000
% 19.68/3.01  
% 19.68/3.01  ------ Superposition Simplification Setup
% 19.68/3.01  
% 19.68/3.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.68/3.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.68/3.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.68/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.68/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.68/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.68/3.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.68/3.01  --sup_immed_triv                        [TrivRules]
% 19.68/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/3.01  --sup_immed_bw_main                     []
% 19.68/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.68/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.68/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/3.01  --sup_input_bw                          []
% 19.68/3.01  
% 19.68/3.01  ------ Combination Options
% 19.68/3.01  
% 19.68/3.01  --comb_res_mult                         3
% 19.68/3.01  --comb_sup_mult                         2
% 19.68/3.01  --comb_inst_mult                        10
% 19.68/3.01  
% 19.68/3.01  ------ Debug Options
% 19.68/3.01  
% 19.68/3.01  --dbg_backtrace                         false
% 19.68/3.01  --dbg_dump_prop_clauses                 false
% 19.68/3.01  --dbg_dump_prop_clauses_file            -
% 19.68/3.01  --dbg_out_stat                          false
% 19.68/3.01  ------ Parsing...
% 19.68/3.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.68/3.01  
% 19.68/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.68/3.01  
% 19.68/3.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.68/3.01  
% 19.68/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.68/3.01  ------ Proving...
% 19.68/3.01  ------ Problem Properties 
% 19.68/3.01  
% 19.68/3.01  
% 19.68/3.01  clauses                                 40
% 19.68/3.01  conjectures                             11
% 19.68/3.01  EPR                                     7
% 19.68/3.01  Horn                                    36
% 19.68/3.01  unary                                   17
% 19.68/3.01  binary                                  4
% 19.68/3.01  lits                                    149
% 19.68/3.01  lits eq                                 34
% 19.68/3.01  fd_pure                                 0
% 19.68/3.01  fd_pseudo                               0
% 19.68/3.01  fd_cond                                 4
% 19.68/3.01  fd_pseudo_cond                          1
% 19.68/3.01  AC symbols                              0
% 19.68/3.01  
% 19.68/3.01  ------ Schedule dynamic 5 is on 
% 19.68/3.01  
% 19.68/3.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.68/3.01  
% 19.68/3.01  
% 19.68/3.01  ------ 
% 19.68/3.01  Current options:
% 19.68/3.01  ------ 
% 19.68/3.01  
% 19.68/3.01  ------ Input Options
% 19.68/3.01  
% 19.68/3.01  --out_options                           all
% 19.68/3.01  --tptp_safe_out                         true
% 19.68/3.01  --problem_path                          ""
% 19.68/3.01  --include_path                          ""
% 19.68/3.01  --clausifier                            res/vclausify_rel
% 19.68/3.01  --clausifier_options                    ""
% 19.68/3.01  --stdin                                 false
% 19.68/3.01  --stats_out                             all
% 19.68/3.01  
% 19.68/3.01  ------ General Options
% 19.68/3.01  
% 19.68/3.01  --fof                                   false
% 19.68/3.01  --time_out_real                         305.
% 19.68/3.01  --time_out_virtual                      -1.
% 19.68/3.01  --symbol_type_check                     false
% 19.68/3.01  --clausify_out                          false
% 19.68/3.01  --sig_cnt_out                           false
% 19.68/3.01  --trig_cnt_out                          false
% 19.68/3.01  --trig_cnt_out_tolerance                1.
% 19.68/3.01  --trig_cnt_out_sk_spl                   false
% 19.68/3.01  --abstr_cl_out                          false
% 19.68/3.01  
% 19.68/3.01  ------ Global Options
% 19.68/3.01  
% 19.68/3.01  --schedule                              default
% 19.68/3.01  --add_important_lit                     false
% 19.68/3.01  --prop_solver_per_cl                    1000
% 19.68/3.01  --min_unsat_core                        false
% 19.68/3.01  --soft_assumptions                      false
% 19.68/3.01  --soft_lemma_size                       3
% 19.68/3.01  --prop_impl_unit_size                   0
% 19.68/3.01  --prop_impl_unit                        []
% 19.68/3.01  --share_sel_clauses                     true
% 19.68/3.01  --reset_solvers                         false
% 19.68/3.01  --bc_imp_inh                            [conj_cone]
% 19.68/3.01  --conj_cone_tolerance                   3.
% 19.68/3.01  --extra_neg_conj                        none
% 19.68/3.01  --large_theory_mode                     true
% 19.68/3.01  --prolific_symb_bound                   200
% 19.68/3.01  --lt_threshold                          2000
% 19.68/3.01  --clause_weak_htbl                      true
% 19.68/3.01  --gc_record_bc_elim                     false
% 19.68/3.01  
% 19.68/3.01  ------ Preprocessing Options
% 19.68/3.01  
% 19.68/3.01  --preprocessing_flag                    true
% 19.68/3.01  --time_out_prep_mult                    0.1
% 19.68/3.01  --splitting_mode                        input
% 19.68/3.01  --splitting_grd                         true
% 19.68/3.01  --splitting_cvd                         false
% 19.68/3.01  --splitting_cvd_svl                     false
% 19.68/3.01  --splitting_nvd                         32
% 19.68/3.01  --sub_typing                            true
% 19.68/3.01  --prep_gs_sim                           true
% 19.68/3.01  --prep_unflatten                        true
% 19.68/3.01  --prep_res_sim                          true
% 19.68/3.01  --prep_upred                            true
% 19.68/3.01  --prep_sem_filter                       exhaustive
% 19.68/3.01  --prep_sem_filter_out                   false
% 19.68/3.01  --pred_elim                             true
% 19.68/3.01  --res_sim_input                         true
% 19.68/3.01  --eq_ax_congr_red                       true
% 19.68/3.01  --pure_diseq_elim                       true
% 19.68/3.01  --brand_transform                       false
% 19.68/3.01  --non_eq_to_eq                          false
% 19.68/3.01  --prep_def_merge                        true
% 19.68/3.01  --prep_def_merge_prop_impl              false
% 19.68/3.01  --prep_def_merge_mbd                    true
% 19.68/3.01  --prep_def_merge_tr_red                 false
% 19.68/3.01  --prep_def_merge_tr_cl                  false
% 19.68/3.01  --smt_preprocessing                     true
% 19.68/3.01  --smt_ac_axioms                         fast
% 19.68/3.01  --preprocessed_out                      false
% 19.68/3.01  --preprocessed_stats                    false
% 19.68/3.01  
% 19.68/3.01  ------ Abstraction refinement Options
% 19.68/3.01  
% 19.68/3.01  --abstr_ref                             []
% 19.68/3.01  --abstr_ref_prep                        false
% 19.68/3.01  --abstr_ref_until_sat                   false
% 19.68/3.01  --abstr_ref_sig_restrict                funpre
% 19.68/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.68/3.01  --abstr_ref_under                       []
% 19.68/3.01  
% 19.68/3.01  ------ SAT Options
% 19.68/3.01  
% 19.68/3.01  --sat_mode                              false
% 19.68/3.01  --sat_fm_restart_options                ""
% 19.68/3.01  --sat_gr_def                            false
% 19.68/3.01  --sat_epr_types                         true
% 19.68/3.01  --sat_non_cyclic_types                  false
% 19.68/3.01  --sat_finite_models                     false
% 19.68/3.01  --sat_fm_lemmas                         false
% 19.68/3.01  --sat_fm_prep                           false
% 19.68/3.01  --sat_fm_uc_incr                        true
% 19.68/3.01  --sat_out_model                         small
% 19.68/3.01  --sat_out_clauses                       false
% 19.68/3.01  
% 19.68/3.01  ------ QBF Options
% 19.68/3.01  
% 19.68/3.01  --qbf_mode                              false
% 19.68/3.01  --qbf_elim_univ                         false
% 19.68/3.01  --qbf_dom_inst                          none
% 19.68/3.01  --qbf_dom_pre_inst                      false
% 19.68/3.01  --qbf_sk_in                             false
% 19.68/3.01  --qbf_pred_elim                         true
% 19.68/3.01  --qbf_split                             512
% 19.68/3.01  
% 19.68/3.01  ------ BMC1 Options
% 19.68/3.01  
% 19.68/3.01  --bmc1_incremental                      false
% 19.68/3.01  --bmc1_axioms                           reachable_all
% 19.68/3.01  --bmc1_min_bound                        0
% 19.68/3.01  --bmc1_max_bound                        -1
% 19.68/3.01  --bmc1_max_bound_default                -1
% 19.68/3.01  --bmc1_symbol_reachability              true
% 19.68/3.01  --bmc1_property_lemmas                  false
% 19.68/3.01  --bmc1_k_induction                      false
% 19.68/3.01  --bmc1_non_equiv_states                 false
% 19.68/3.01  --bmc1_deadlock                         false
% 19.68/3.01  --bmc1_ucm                              false
% 19.68/3.01  --bmc1_add_unsat_core                   none
% 19.68/3.01  --bmc1_unsat_core_children              false
% 19.68/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.68/3.01  --bmc1_out_stat                         full
% 19.68/3.01  --bmc1_ground_init                      false
% 19.68/3.01  --bmc1_pre_inst_next_state              false
% 19.68/3.01  --bmc1_pre_inst_state                   false
% 19.68/3.01  --bmc1_pre_inst_reach_state             false
% 19.68/3.01  --bmc1_out_unsat_core                   false
% 19.68/3.01  --bmc1_aig_witness_out                  false
% 19.68/3.01  --bmc1_verbose                          false
% 19.68/3.01  --bmc1_dump_clauses_tptp                false
% 19.68/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.68/3.01  --bmc1_dump_file                        -
% 19.68/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.68/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.68/3.01  --bmc1_ucm_extend_mode                  1
% 19.68/3.01  --bmc1_ucm_init_mode                    2
% 19.68/3.01  --bmc1_ucm_cone_mode                    none
% 19.68/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.68/3.01  --bmc1_ucm_relax_model                  4
% 19.68/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.68/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.68/3.01  --bmc1_ucm_layered_model                none
% 19.68/3.01  --bmc1_ucm_max_lemma_size               10
% 19.68/3.01  
% 19.68/3.01  ------ AIG Options
% 19.68/3.01  
% 19.68/3.01  --aig_mode                              false
% 19.68/3.01  
% 19.68/3.01  ------ Instantiation Options
% 19.68/3.01  
% 19.68/3.01  --instantiation_flag                    true
% 19.68/3.01  --inst_sos_flag                         true
% 19.68/3.01  --inst_sos_phase                        true
% 19.68/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.68/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.68/3.01  --inst_lit_sel_side                     none
% 19.68/3.01  --inst_solver_per_active                1400
% 19.68/3.01  --inst_solver_calls_frac                1.
% 19.68/3.01  --inst_passive_queue_type               priority_queues
% 19.68/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.68/3.01  --inst_passive_queues_freq              [25;2]
% 19.68/3.01  --inst_dismatching                      true
% 19.68/3.01  --inst_eager_unprocessed_to_passive     true
% 19.68/3.01  --inst_prop_sim_given                   true
% 19.68/3.01  --inst_prop_sim_new                     false
% 19.68/3.01  --inst_subs_new                         false
% 19.68/3.01  --inst_eq_res_simp                      false
% 19.68/3.01  --inst_subs_given                       false
% 19.68/3.01  --inst_orphan_elimination               true
% 19.68/3.01  --inst_learning_loop_flag               true
% 19.68/3.01  --inst_learning_start                   3000
% 19.68/3.01  --inst_learning_factor                  2
% 19.68/3.01  --inst_start_prop_sim_after_learn       3
% 19.68/3.01  --inst_sel_renew                        solver
% 19.68/3.01  --inst_lit_activity_flag                true
% 19.68/3.01  --inst_restr_to_given                   false
% 19.68/3.01  --inst_activity_threshold               500
% 19.68/3.01  --inst_out_proof                        true
% 19.68/3.01  
% 19.68/3.01  ------ Resolution Options
% 19.68/3.01  
% 19.68/3.01  --resolution_flag                       false
% 19.68/3.01  --res_lit_sel                           adaptive
% 19.68/3.01  --res_lit_sel_side                      none
% 19.68/3.01  --res_ordering                          kbo
% 19.68/3.01  --res_to_prop_solver                    active
% 19.68/3.01  --res_prop_simpl_new                    false
% 19.68/3.01  --res_prop_simpl_given                  true
% 19.68/3.01  --res_passive_queue_type                priority_queues
% 19.68/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.68/3.01  --res_passive_queues_freq               [15;5]
% 19.68/3.01  --res_forward_subs                      full
% 19.68/3.01  --res_backward_subs                     full
% 19.68/3.01  --res_forward_subs_resolution           true
% 19.68/3.01  --res_backward_subs_resolution          true
% 19.68/3.01  --res_orphan_elimination                true
% 19.68/3.01  --res_time_limit                        2.
% 19.68/3.01  --res_out_proof                         true
% 19.68/3.01  
% 19.68/3.01  ------ Superposition Options
% 19.68/3.01  
% 19.68/3.01  --superposition_flag                    true
% 19.68/3.01  --sup_passive_queue_type                priority_queues
% 19.68/3.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.68/3.01  --sup_passive_queues_freq               [8;1;4]
% 19.68/3.01  --demod_completeness_check              fast
% 19.68/3.01  --demod_use_ground                      true
% 19.68/3.01  --sup_to_prop_solver                    passive
% 19.68/3.01  --sup_prop_simpl_new                    true
% 19.68/3.01  --sup_prop_simpl_given                  true
% 19.68/3.01  --sup_fun_splitting                     true
% 19.68/3.01  --sup_smt_interval                      50000
% 19.68/3.01  
% 19.68/3.01  ------ Superposition Simplification Setup
% 19.68/3.01  
% 19.68/3.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.68/3.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.68/3.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.68/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.68/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.68/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.68/3.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.68/3.01  --sup_immed_triv                        [TrivRules]
% 19.68/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/3.01  --sup_immed_bw_main                     []
% 19.68/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.68/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.68/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/3.01  --sup_input_bw                          []
% 19.68/3.01  
% 19.68/3.01  ------ Combination Options
% 19.68/3.01  
% 19.68/3.01  --comb_res_mult                         3
% 19.68/3.01  --comb_sup_mult                         2
% 19.68/3.01  --comb_inst_mult                        10
% 19.68/3.01  
% 19.68/3.01  ------ Debug Options
% 19.68/3.01  
% 19.68/3.01  --dbg_backtrace                         false
% 19.68/3.01  --dbg_dump_prop_clauses                 false
% 19.68/3.01  --dbg_dump_prop_clauses_file            -
% 19.68/3.01  --dbg_out_stat                          false
% 19.68/3.01  
% 19.68/3.01  
% 19.68/3.01  
% 19.68/3.01  
% 19.68/3.01  ------ Proving...
% 19.68/3.01  
% 19.68/3.01  
% 19.68/3.01  % SZS status Theorem for theBenchmark.p
% 19.68/3.01  
% 19.68/3.01  % SZS output start CNFRefutation for theBenchmark.p
% 19.68/3.01  
% 19.68/3.01  fof(f17,axiom,(
% 19.68/3.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f42,plain,(
% 19.68/3.01    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 19.68/3.01    inference(ennf_transformation,[],[f17])).
% 19.68/3.01  
% 19.68/3.01  fof(f43,plain,(
% 19.68/3.01    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 19.68/3.01    inference(flattening,[],[f42])).
% 19.68/3.01  
% 19.68/3.01  fof(f79,plain,(
% 19.68/3.01    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 19.68/3.01    inference(cnf_transformation,[],[f43])).
% 19.68/3.01  
% 19.68/3.01  fof(f21,conjecture,(
% 19.68/3.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f22,negated_conjecture,(
% 19.68/3.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 19.68/3.01    inference(negated_conjecture,[],[f21])).
% 19.68/3.01  
% 19.68/3.01  fof(f50,plain,(
% 19.68/3.01    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 19.68/3.01    inference(ennf_transformation,[],[f22])).
% 19.68/3.01  
% 19.68/3.01  fof(f51,plain,(
% 19.68/3.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 19.68/3.01    inference(flattening,[],[f50])).
% 19.68/3.01  
% 19.68/3.01  fof(f55,plain,(
% 19.68/3.01    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 19.68/3.01    introduced(choice_axiom,[])).
% 19.68/3.01  
% 19.68/3.01  fof(f54,plain,(
% 19.68/3.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 19.68/3.01    introduced(choice_axiom,[])).
% 19.68/3.01  
% 19.68/3.01  fof(f56,plain,(
% 19.68/3.01    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 19.68/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f51,f55,f54])).
% 19.68/3.01  
% 19.68/3.01  fof(f96,plain,(
% 19.68/3.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 19.68/3.01    inference(cnf_transformation,[],[f56])).
% 19.68/3.01  
% 19.68/3.01  fof(f89,plain,(
% 19.68/3.01    v1_funct_1(sK2)),
% 19.68/3.01    inference(cnf_transformation,[],[f56])).
% 19.68/3.01  
% 19.68/3.01  fof(f90,plain,(
% 19.68/3.01    v1_funct_2(sK2,sK0,sK1)),
% 19.68/3.01    inference(cnf_transformation,[],[f56])).
% 19.68/3.01  
% 19.68/3.01  fof(f91,plain,(
% 19.68/3.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 19.68/3.01    inference(cnf_transformation,[],[f56])).
% 19.68/3.01  
% 19.68/3.01  fof(f92,plain,(
% 19.68/3.01    v1_funct_1(sK3)),
% 19.68/3.01    inference(cnf_transformation,[],[f56])).
% 19.68/3.01  
% 19.68/3.01  fof(f93,plain,(
% 19.68/3.01    v1_funct_2(sK3,sK1,sK0)),
% 19.68/3.01    inference(cnf_transformation,[],[f56])).
% 19.68/3.01  
% 19.68/3.01  fof(f94,plain,(
% 19.68/3.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 19.68/3.01    inference(cnf_transformation,[],[f56])).
% 19.68/3.01  
% 19.68/3.01  fof(f20,axiom,(
% 19.68/3.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f48,plain,(
% 19.68/3.01    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 19.68/3.01    inference(ennf_transformation,[],[f20])).
% 19.68/3.01  
% 19.68/3.01  fof(f49,plain,(
% 19.68/3.01    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 19.68/3.01    inference(flattening,[],[f48])).
% 19.68/3.01  
% 19.68/3.01  fof(f87,plain,(
% 19.68/3.01    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 19.68/3.01    inference(cnf_transformation,[],[f49])).
% 19.68/3.01  
% 19.68/3.01  fof(f98,plain,(
% 19.68/3.01    k1_xboole_0 != sK0),
% 19.68/3.01    inference(cnf_transformation,[],[f56])).
% 19.68/3.01  
% 19.68/3.01  fof(f6,axiom,(
% 19.68/3.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f65,plain,(
% 19.68/3.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 19.68/3.01    inference(cnf_transformation,[],[f6])).
% 19.68/3.01  
% 19.68/3.01  fof(f16,axiom,(
% 19.68/3.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f78,plain,(
% 19.68/3.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 19.68/3.01    inference(cnf_transformation,[],[f16])).
% 19.68/3.01  
% 19.68/3.01  fof(f103,plain,(
% 19.68/3.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 19.68/3.01    inference(definition_unfolding,[],[f65,f78])).
% 19.68/3.01  
% 19.68/3.01  fof(f12,axiom,(
% 19.68/3.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f36,plain,(
% 19.68/3.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 19.68/3.01    inference(ennf_transformation,[],[f12])).
% 19.68/3.01  
% 19.68/3.01  fof(f37,plain,(
% 19.68/3.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.68/3.01    inference(flattening,[],[f36])).
% 19.68/3.01  
% 19.68/3.01  fof(f53,plain,(
% 19.68/3.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.68/3.01    inference(nnf_transformation,[],[f37])).
% 19.68/3.01  
% 19.68/3.01  fof(f72,plain,(
% 19.68/3.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.68/3.01    inference(cnf_transformation,[],[f53])).
% 19.68/3.01  
% 19.68/3.01  fof(f14,axiom,(
% 19.68/3.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f23,plain,(
% 19.68/3.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 19.68/3.01    inference(pure_predicate_removal,[],[f14])).
% 19.68/3.01  
% 19.68/3.01  fof(f76,plain,(
% 19.68/3.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 19.68/3.01    inference(cnf_transformation,[],[f23])).
% 19.68/3.01  
% 19.68/3.01  fof(f13,axiom,(
% 19.68/3.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f38,plain,(
% 19.68/3.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 19.68/3.01    inference(ennf_transformation,[],[f13])).
% 19.68/3.01  
% 19.68/3.01  fof(f39,plain,(
% 19.68/3.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 19.68/3.01    inference(flattening,[],[f38])).
% 19.68/3.01  
% 19.68/3.01  fof(f75,plain,(
% 19.68/3.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 19.68/3.01    inference(cnf_transformation,[],[f39])).
% 19.68/3.01  
% 19.68/3.01  fof(f95,plain,(
% 19.68/3.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 19.68/3.01    inference(cnf_transformation,[],[f56])).
% 19.68/3.01  
% 19.68/3.01  fof(f18,axiom,(
% 19.68/3.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f44,plain,(
% 19.68/3.01    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 19.68/3.01    inference(ennf_transformation,[],[f18])).
% 19.68/3.01  
% 19.68/3.01  fof(f45,plain,(
% 19.68/3.01    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 19.68/3.01    inference(flattening,[],[f44])).
% 19.68/3.01  
% 19.68/3.01  fof(f82,plain,(
% 19.68/3.01    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 19.68/3.01    inference(cnf_transformation,[],[f45])).
% 19.68/3.01  
% 19.68/3.01  fof(f8,axiom,(
% 19.68/3.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f31,plain,(
% 19.68/3.01    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.68/3.01    inference(ennf_transformation,[],[f8])).
% 19.68/3.01  
% 19.68/3.01  fof(f32,plain,(
% 19.68/3.01    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.68/3.01    inference(flattening,[],[f31])).
% 19.68/3.01  
% 19.68/3.01  fof(f68,plain,(
% 19.68/3.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.68/3.01    inference(cnf_transformation,[],[f32])).
% 19.68/3.01  
% 19.68/3.01  fof(f105,plain,(
% 19.68/3.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.68/3.01    inference(definition_unfolding,[],[f68,f78])).
% 19.68/3.01  
% 19.68/3.01  fof(f11,axiom,(
% 19.68/3.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f35,plain,(
% 19.68/3.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.68/3.01    inference(ennf_transformation,[],[f11])).
% 19.68/3.01  
% 19.68/3.01  fof(f71,plain,(
% 19.68/3.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.68/3.01    inference(cnf_transformation,[],[f35])).
% 19.68/3.01  
% 19.68/3.01  fof(f7,axiom,(
% 19.68/3.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f29,plain,(
% 19.68/3.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.68/3.01    inference(ennf_transformation,[],[f7])).
% 19.68/3.01  
% 19.68/3.01  fof(f30,plain,(
% 19.68/3.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.68/3.01    inference(flattening,[],[f29])).
% 19.68/3.01  
% 19.68/3.01  fof(f66,plain,(
% 19.68/3.01    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.68/3.01    inference(cnf_transformation,[],[f30])).
% 19.68/3.01  
% 19.68/3.01  fof(f9,axiom,(
% 19.68/3.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f33,plain,(
% 19.68/3.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.68/3.01    inference(ennf_transformation,[],[f9])).
% 19.68/3.01  
% 19.68/3.01  fof(f69,plain,(
% 19.68/3.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.68/3.01    inference(cnf_transformation,[],[f33])).
% 19.68/3.01  
% 19.68/3.01  fof(f67,plain,(
% 19.68/3.01    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.68/3.01    inference(cnf_transformation,[],[f30])).
% 19.68/3.01  
% 19.68/3.01  fof(f19,axiom,(
% 19.68/3.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f46,plain,(
% 19.68/3.01    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 19.68/3.01    inference(ennf_transformation,[],[f19])).
% 19.68/3.01  
% 19.68/3.01  fof(f47,plain,(
% 19.68/3.01    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 19.68/3.01    inference(flattening,[],[f46])).
% 19.68/3.01  
% 19.68/3.01  fof(f84,plain,(
% 19.68/3.01    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 19.68/3.01    inference(cnf_transformation,[],[f47])).
% 19.68/3.01  
% 19.68/3.01  fof(f86,plain,(
% 19.68/3.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 19.68/3.01    inference(cnf_transformation,[],[f47])).
% 19.68/3.01  
% 19.68/3.01  fof(f4,axiom,(
% 19.68/3.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f27,plain,(
% 19.68/3.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.68/3.01    inference(ennf_transformation,[],[f4])).
% 19.68/3.01  
% 19.68/3.01  fof(f28,plain,(
% 19.68/3.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.68/3.01    inference(flattening,[],[f27])).
% 19.68/3.01  
% 19.68/3.01  fof(f61,plain,(
% 19.68/3.01    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.68/3.01    inference(cnf_transformation,[],[f28])).
% 19.68/3.01  
% 19.68/3.01  fof(f5,axiom,(
% 19.68/3.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f63,plain,(
% 19.68/3.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 19.68/3.01    inference(cnf_transformation,[],[f5])).
% 19.68/3.01  
% 19.68/3.01  fof(f101,plain,(
% 19.68/3.01    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 19.68/3.01    inference(definition_unfolding,[],[f63,f78])).
% 19.68/3.01  
% 19.68/3.01  fof(f10,axiom,(
% 19.68/3.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f24,plain,(
% 19.68/3.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 19.68/3.01    inference(pure_predicate_removal,[],[f10])).
% 19.68/3.01  
% 19.68/3.01  fof(f34,plain,(
% 19.68/3.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.68/3.01    inference(ennf_transformation,[],[f24])).
% 19.68/3.01  
% 19.68/3.01  fof(f70,plain,(
% 19.68/3.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.68/3.01    inference(cnf_transformation,[],[f34])).
% 19.68/3.01  
% 19.68/3.01  fof(f2,axiom,(
% 19.68/3.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f26,plain,(
% 19.68/3.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.68/3.01    inference(ennf_transformation,[],[f2])).
% 19.68/3.01  
% 19.68/3.01  fof(f52,plain,(
% 19.68/3.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 19.68/3.01    inference(nnf_transformation,[],[f26])).
% 19.68/3.01  
% 19.68/3.01  fof(f58,plain,(
% 19.68/3.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.68/3.01    inference(cnf_transformation,[],[f52])).
% 19.68/3.01  
% 19.68/3.01  fof(f62,plain,(
% 19.68/3.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 19.68/3.01    inference(cnf_transformation,[],[f5])).
% 19.68/3.01  
% 19.68/3.01  fof(f102,plain,(
% 19.68/3.01    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 19.68/3.01    inference(definition_unfolding,[],[f62,f78])).
% 19.68/3.01  
% 19.68/3.01  fof(f15,axiom,(
% 19.68/3.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 19.68/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.01  
% 19.68/3.01  fof(f40,plain,(
% 19.68/3.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 19.68/3.01    inference(ennf_transformation,[],[f15])).
% 19.68/3.01  
% 19.68/3.01  fof(f41,plain,(
% 19.68/3.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 19.68/3.01    inference(flattening,[],[f40])).
% 19.68/3.01  
% 19.68/3.01  fof(f77,plain,(
% 19.68/3.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 19.68/3.01    inference(cnf_transformation,[],[f41])).
% 19.68/3.01  
% 19.68/3.01  fof(f100,plain,(
% 19.68/3.01    k2_funct_1(sK2) != sK3),
% 19.68/3.01    inference(cnf_transformation,[],[f56])).
% 19.68/3.01  
% 19.68/3.01  fof(f97,plain,(
% 19.68/3.01    v2_funct_1(sK2)),
% 19.68/3.01    inference(cnf_transformation,[],[f56])).
% 19.68/3.01  
% 19.68/3.01  cnf(c_21,plain,
% 19.68/3.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 19.68/3.01      | ~ v1_funct_2(X2,X0,X1)
% 19.68/3.01      | ~ v1_funct_2(X3,X1,X0)
% 19.68/3.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 19.68/3.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.68/3.01      | ~ v1_funct_1(X2)
% 19.68/3.01      | ~ v1_funct_1(X3)
% 19.68/3.01      | k2_relset_1(X1,X0,X3) = X0 ),
% 19.68/3.01      inference(cnf_transformation,[],[f79]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_35,negated_conjecture,
% 19.68/3.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 19.68/3.01      inference(cnf_transformation,[],[f96]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_513,plain,
% 19.68/3.01      ( ~ v1_funct_2(X0,X1,X2)
% 19.68/3.01      | ~ v1_funct_2(X3,X2,X1)
% 19.68/3.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 19.68/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | ~ v1_funct_1(X3)
% 19.68/3.01      | ~ v1_funct_1(X0)
% 19.68/3.01      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 19.68/3.01      | k2_relset_1(X2,X1,X3) = X1
% 19.68/3.01      | k6_partfun1(X1) != k6_partfun1(sK0)
% 19.68/3.01      | sK0 != X1 ),
% 19.68/3.01      inference(resolution_lifted,[status(thm)],[c_21,c_35]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_514,plain,
% 19.68/3.01      ( ~ v1_funct_2(X0,X1,sK0)
% 19.68/3.01      | ~ v1_funct_2(X2,sK0,X1)
% 19.68/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 19.68/3.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 19.68/3.01      | ~ v1_funct_1(X2)
% 19.68/3.01      | ~ v1_funct_1(X0)
% 19.68/3.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 19.68/3.01      | k2_relset_1(X1,sK0,X0) = sK0
% 19.68/3.01      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 19.68/3.01      inference(unflattening,[status(thm)],[c_513]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_602,plain,
% 19.68/3.01      ( ~ v1_funct_2(X0,X1,sK0)
% 19.68/3.01      | ~ v1_funct_2(X2,sK0,X1)
% 19.68/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 19.68/3.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 19.68/3.01      | ~ v1_funct_1(X0)
% 19.68/3.01      | ~ v1_funct_1(X2)
% 19.68/3.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 19.68/3.01      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 19.68/3.01      inference(equality_resolution_simp,[status(thm)],[c_514]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1387,plain,
% 19.68/3.01      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 19.68/3.01      | k2_relset_1(X0,sK0,X2) = sK0
% 19.68/3.01      | v1_funct_2(X2,X0,sK0) != iProver_top
% 19.68/3.01      | v1_funct_2(X1,sK0,X0) != iProver_top
% 19.68/3.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 19.68/3.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 19.68/3.01      | v1_funct_1(X2) != iProver_top
% 19.68/3.01      | v1_funct_1(X1) != iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1932,plain,
% 19.68/3.01      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 19.68/3.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 19.68/3.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 19.68/3.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 19.68/3.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 19.68/3.01      | v1_funct_1(sK3) != iProver_top
% 19.68/3.01      | v1_funct_1(sK2) != iProver_top ),
% 19.68/3.01      inference(equality_resolution,[status(thm)],[c_1387]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_42,negated_conjecture,
% 19.68/3.01      ( v1_funct_1(sK2) ),
% 19.68/3.01      inference(cnf_transformation,[],[f89]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_43,plain,
% 19.68/3.01      ( v1_funct_1(sK2) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_41,negated_conjecture,
% 19.68/3.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 19.68/3.01      inference(cnf_transformation,[],[f90]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_44,plain,
% 19.68/3.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_40,negated_conjecture,
% 19.68/3.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 19.68/3.01      inference(cnf_transformation,[],[f91]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_45,plain,
% 19.68/3.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_39,negated_conjecture,
% 19.68/3.01      ( v1_funct_1(sK3) ),
% 19.68/3.01      inference(cnf_transformation,[],[f92]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_46,plain,
% 19.68/3.01      ( v1_funct_1(sK3) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_38,negated_conjecture,
% 19.68/3.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 19.68/3.01      inference(cnf_transformation,[],[f93]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_47,plain,
% 19.68/3.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_37,negated_conjecture,
% 19.68/3.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 19.68/3.01      inference(cnf_transformation,[],[f94]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_48,plain,
% 19.68/3.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_2139,plain,
% 19.68/3.01      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_1932,c_43,c_44,c_45,c_46,c_47,c_48]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_30,plain,
% 19.68/3.01      ( ~ v1_funct_2(X0,X1,X2)
% 19.68/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | ~ v1_funct_1(X0)
% 19.68/3.01      | ~ v2_funct_1(X0)
% 19.68/3.01      | k2_relset_1(X1,X2,X0) != X2
% 19.68/3.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 19.68/3.01      | k1_xboole_0 = X2 ),
% 19.68/3.01      inference(cnf_transformation,[],[f87]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1398,plain,
% 19.68/3.01      ( k2_relset_1(X0,X1,X2) != X1
% 19.68/3.01      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 19.68/3.01      | k1_xboole_0 = X1
% 19.68/3.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 19.68/3.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.68/3.01      | v1_funct_1(X2) != iProver_top
% 19.68/3.01      | v2_funct_1(X2) != iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_3219,plain,
% 19.68/3.01      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 19.68/3.01      | sK0 = k1_xboole_0
% 19.68/3.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 19.68/3.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 19.68/3.01      | v1_funct_1(sK3) != iProver_top
% 19.68/3.01      | v2_funct_1(sK3) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_2139,c_1398]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_33,negated_conjecture,
% 19.68/3.01      ( k1_xboole_0 != sK0 ),
% 19.68/3.01      inference(cnf_transformation,[],[f98]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_822,plain,( X0 = X0 ),theory(equality) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_855,plain,
% 19.68/3.01      ( k1_xboole_0 = k1_xboole_0 ),
% 19.68/3.01      inference(instantiation,[status(thm)],[c_822]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_823,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1507,plain,
% 19.68/3.01      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 19.68/3.01      inference(instantiation,[status(thm)],[c_823]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1508,plain,
% 19.68/3.01      ( sK0 != k1_xboole_0
% 19.68/3.01      | k1_xboole_0 = sK0
% 19.68/3.01      | k1_xboole_0 != k1_xboole_0 ),
% 19.68/3.01      inference(instantiation,[status(thm)],[c_1507]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_7,plain,
% 19.68/3.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 19.68/3.01      inference(cnf_transformation,[],[f103]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5059,plain,
% 19.68/3.01      ( v2_funct_1(k6_partfun1(sK0)) ),
% 19.68/3.01      inference(instantiation,[status(thm)],[c_7]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5060,plain,
% 19.68/3.01      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_5059]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_16,plain,
% 19.68/3.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 19.68/3.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.68/3.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.68/3.01      | X3 = X2 ),
% 19.68/3.01      inference(cnf_transformation,[],[f72]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_500,plain,
% 19.68/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | X3 = X0
% 19.68/3.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 19.68/3.01      | k6_partfun1(sK0) != X3
% 19.68/3.01      | sK0 != X2
% 19.68/3.01      | sK0 != X1 ),
% 19.68/3.01      inference(resolution_lifted,[status(thm)],[c_16,c_35]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_501,plain,
% 19.68/3.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 19.68/3.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 19.68/3.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 19.68/3.01      inference(unflattening,[status(thm)],[c_500]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_19,plain,
% 19.68/3.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 19.68/3.01      inference(cnf_transformation,[],[f76]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_509,plain,
% 19.68/3.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 19.68/3.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 19.68/3.01      inference(forward_subsumption_resolution,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_501,c_19]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1388,plain,
% 19.68/3.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 19.68/3.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_17,plain,
% 19.68/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 19.68/3.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 19.68/3.01      | ~ v1_funct_1(X0)
% 19.68/3.01      | ~ v1_funct_1(X3) ),
% 19.68/3.01      inference(cnf_transformation,[],[f75]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1509,plain,
% 19.68/3.01      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 19.68/3.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 19.68/3.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.68/3.01      | ~ v1_funct_1(sK3)
% 19.68/3.01      | ~ v1_funct_1(sK2) ),
% 19.68/3.01      inference(instantiation,[status(thm)],[c_17]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_2132,plain,
% 19.68/3.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_1388,c_42,c_40,c_39,c_37,c_509,c_1509]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_36,negated_conjecture,
% 19.68/3.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 19.68/3.01      inference(cnf_transformation,[],[f95]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_23,plain,
% 19.68/3.01      ( ~ v1_funct_2(X0,X1,X2)
% 19.68/3.01      | ~ v1_funct_2(X3,X2,X4)
% 19.68/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 19.68/3.01      | ~ v1_funct_1(X3)
% 19.68/3.01      | ~ v1_funct_1(X0)
% 19.68/3.01      | v2_funct_1(X3)
% 19.68/3.01      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 19.68/3.01      | k2_relset_1(X1,X2,X0) != X2
% 19.68/3.01      | k1_xboole_0 = X4 ),
% 19.68/3.01      inference(cnf_transformation,[],[f82]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1405,plain,
% 19.68/3.01      ( k2_relset_1(X0,X1,X2) != X1
% 19.68/3.01      | k1_xboole_0 = X3
% 19.68/3.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 19.68/3.01      | v1_funct_2(X4,X1,X3) != iProver_top
% 19.68/3.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.68/3.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 19.68/3.01      | v1_funct_1(X2) != iProver_top
% 19.68/3.01      | v1_funct_1(X4) != iProver_top
% 19.68/3.01      | v2_funct_1(X4) = iProver_top
% 19.68/3.01      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_6509,plain,
% 19.68/3.01      ( k1_xboole_0 = X0
% 19.68/3.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 19.68/3.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 19.68/3.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 19.68/3.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 19.68/3.01      | v1_funct_1(X1) != iProver_top
% 19.68/3.01      | v1_funct_1(sK2) != iProver_top
% 19.68/3.01      | v2_funct_1(X1) = iProver_top
% 19.68/3.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_36,c_1405]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_6518,plain,
% 19.68/3.01      ( v1_funct_1(X1) != iProver_top
% 19.68/3.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 19.68/3.01      | k1_xboole_0 = X0
% 19.68/3.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 19.68/3.01      | v2_funct_1(X1) = iProver_top
% 19.68/3.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_6509,c_43,c_44,c_45]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_6519,plain,
% 19.68/3.01      ( k1_xboole_0 = X0
% 19.68/3.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 19.68/3.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 19.68/3.01      | v1_funct_1(X1) != iProver_top
% 19.68/3.01      | v2_funct_1(X1) = iProver_top
% 19.68/3.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 19.68/3.01      inference(renaming,[status(thm)],[c_6518]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_6522,plain,
% 19.68/3.01      ( sK0 = k1_xboole_0
% 19.68/3.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 19.68/3.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 19.68/3.01      | v1_funct_1(sK3) != iProver_top
% 19.68/3.01      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 19.68/3.01      | v2_funct_1(sK3) = iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_2132,c_6519]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_7182,plain,
% 19.68/3.01      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_3219,c_46,c_47,c_48,c_33,c_855,c_1508,c_5060,c_6522]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_11,plain,
% 19.68/3.01      ( ~ v1_funct_1(X0)
% 19.68/3.01      | ~ v1_funct_1(X1)
% 19.68/3.01      | ~ v2_funct_1(X0)
% 19.68/3.01      | ~ v1_relat_1(X0)
% 19.68/3.01      | ~ v1_relat_1(X1)
% 19.68/3.01      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 19.68/3.01      | k2_funct_1(X0) = X1
% 19.68/3.01      | k2_relat_1(X1) != k1_relat_1(X0) ),
% 19.68/3.01      inference(cnf_transformation,[],[f105]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1413,plain,
% 19.68/3.01      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 19.68/3.01      | k2_funct_1(X1) = X0
% 19.68/3.01      | k2_relat_1(X0) != k1_relat_1(X1)
% 19.68/3.01      | v1_funct_1(X1) != iProver_top
% 19.68/3.01      | v1_funct_1(X0) != iProver_top
% 19.68/3.01      | v2_funct_1(X1) != iProver_top
% 19.68/3.01      | v1_relat_1(X1) != iProver_top
% 19.68/3.01      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_7184,plain,
% 19.68/3.01      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 19.68/3.01      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
% 19.68/3.01      | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
% 19.68/3.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 19.68/3.01      | v1_funct_1(sK3) != iProver_top
% 19.68/3.01      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 19.68/3.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_7182,c_1413]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1396,plain,
% 19.68/3.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_14,plain,
% 19.68/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 19.68/3.01      inference(cnf_transformation,[],[f71]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1411,plain,
% 19.68/3.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 19.68/3.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_2372,plain,
% 19.68/3.01      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_1396,c_1411]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_2375,plain,
% 19.68/3.01      ( k2_relat_1(sK3) = sK0 ),
% 19.68/3.01      inference(light_normalisation,[status(thm)],[c_2372,c_2139]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_6633,plain,
% 19.68/3.01      ( v2_funct_1(sK3) = iProver_top ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_6522,c_46,c_47,c_48,c_33,c_855,c_1508,c_5060]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1394,plain,
% 19.68/3.01      ( v1_funct_1(sK3) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_10,plain,
% 19.68/3.01      ( ~ v1_funct_1(X0)
% 19.68/3.01      | ~ v2_funct_1(X0)
% 19.68/3.01      | ~ v1_relat_1(X0)
% 19.68/3.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 19.68/3.01      inference(cnf_transformation,[],[f66]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1414,plain,
% 19.68/3.01      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 19.68/3.01      | v1_funct_1(X0) != iProver_top
% 19.68/3.01      | v2_funct_1(X0) != iProver_top
% 19.68/3.01      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_3225,plain,
% 19.68/3.01      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 19.68/3.01      | v2_funct_1(sK3) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_1394,c_1414]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_3228,plain,
% 19.68/3.01      ( k1_relat_1(k2_funct_1(sK3)) = sK0
% 19.68/3.01      | v2_funct_1(sK3) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) != iProver_top ),
% 19.68/3.01      inference(light_normalisation,[status(thm)],[c_3225,c_2375]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_12,plain,
% 19.68/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | v1_relat_1(X0) ),
% 19.68/3.01      inference(cnf_transformation,[],[f69]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1561,plain,
% 19.68/3.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.68/3.01      | v1_relat_1(sK3) ),
% 19.68/3.01      inference(instantiation,[status(thm)],[c_12]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1916,plain,
% 19.68/3.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 19.68/3.01      | v1_relat_1(sK3) ),
% 19.68/3.01      inference(instantiation,[status(thm)],[c_1561]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1917,plain,
% 19.68/3.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_1916]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_4159,plain,
% 19.68/3.01      ( v2_funct_1(sK3) != iProver_top
% 19.68/3.01      | k1_relat_1(k2_funct_1(sK3)) = sK0 ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_3228,c_48,c_1917]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_4160,plain,
% 19.68/3.01      ( k1_relat_1(k2_funct_1(sK3)) = sK0
% 19.68/3.01      | v2_funct_1(sK3) != iProver_top ),
% 19.68/3.01      inference(renaming,[status(thm)],[c_4159]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_6637,plain,
% 19.68/3.01      ( k1_relat_1(k2_funct_1(sK3)) = sK0 ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_6633,c_4160]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_9,plain,
% 19.68/3.01      ( ~ v1_funct_1(X0)
% 19.68/3.01      | ~ v2_funct_1(X0)
% 19.68/3.01      | ~ v1_relat_1(X0)
% 19.68/3.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 19.68/3.01      inference(cnf_transformation,[],[f67]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1415,plain,
% 19.68/3.01      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 19.68/3.01      | v1_funct_1(X0) != iProver_top
% 19.68/3.01      | v2_funct_1(X0) != iProver_top
% 19.68/3.01      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_3272,plain,
% 19.68/3.01      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 19.68/3.01      | v2_funct_1(sK3) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_1394,c_1415]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_3409,plain,
% 19.68/3.01      ( v2_funct_1(sK3) != iProver_top
% 19.68/3.01      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_3272,c_48,c_1917]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_3410,plain,
% 19.68/3.01      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 19.68/3.01      | v2_funct_1(sK3) != iProver_top ),
% 19.68/3.01      inference(renaming,[status(thm)],[c_3409]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_6638,plain,
% 19.68/3.01      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_6633,c_3410]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_7185,plain,
% 19.68/3.01      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 19.68/3.01      | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
% 19.68/3.01      | sK0 != sK0
% 19.68/3.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 19.68/3.01      | v1_funct_1(sK3) != iProver_top
% 19.68/3.01      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 19.68/3.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) != iProver_top ),
% 19.68/3.01      inference(light_normalisation,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_7184,c_2375,c_6637,c_6638]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_7186,plain,
% 19.68/3.01      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 19.68/3.01      | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
% 19.68/3.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 19.68/3.01      | v1_funct_1(sK3) != iProver_top
% 19.68/3.01      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 19.68/3.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) != iProver_top ),
% 19.68/3.01      inference(equality_resolution_simp,[status(thm)],[c_7185]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_28,plain,
% 19.68/3.01      ( ~ v1_funct_2(X0,X1,X2)
% 19.68/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | ~ v1_funct_1(X0)
% 19.68/3.01      | v1_funct_1(k2_funct_1(X0))
% 19.68/3.01      | ~ v2_funct_1(X0)
% 19.68/3.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 19.68/3.01      inference(cnf_transformation,[],[f84]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1400,plain,
% 19.68/3.01      ( k2_relset_1(X0,X1,X2) != X1
% 19.68/3.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 19.68/3.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.68/3.01      | v1_funct_1(X2) != iProver_top
% 19.68/3.01      | v1_funct_1(k2_funct_1(X2)) = iProver_top
% 19.68/3.01      | v2_funct_1(X2) != iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5140,plain,
% 19.68/3.01      ( v1_funct_2(sK3,sK1,sK0) != iProver_top
% 19.68/3.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 19.68/3.01      | v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 19.68/3.01      | v1_funct_1(sK3) != iProver_top
% 19.68/3.01      | v2_funct_1(sK3) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_2139,c_1400]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_26,plain,
% 19.68/3.01      ( ~ v1_funct_2(X0,X1,X2)
% 19.68/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 19.68/3.01      | ~ v1_funct_1(X0)
% 19.68/3.01      | ~ v2_funct_1(X0)
% 19.68/3.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 19.68/3.01      inference(cnf_transformation,[],[f86]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1402,plain,
% 19.68/3.01      ( k2_relset_1(X0,X1,X2) != X1
% 19.68/3.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 19.68/3.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.68/3.01      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 19.68/3.01      | v1_funct_1(X2) != iProver_top
% 19.68/3.01      | v2_funct_1(X2) != iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5688,plain,
% 19.68/3.01      ( v1_funct_2(sK3,sK1,sK0) != iProver_top
% 19.68/3.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 19.68/3.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 19.68/3.01      | v1_funct_1(sK3) != iProver_top
% 19.68/3.01      | v2_funct_1(sK3) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_2139,c_1402]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_2054,plain,
% 19.68/3.01      ( ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | v1_relat_1(k2_funct_1(X0)) ),
% 19.68/3.01      inference(instantiation,[status(thm)],[c_12]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_15495,plain,
% 19.68/3.01      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.68/3.01      | v1_relat_1(k2_funct_1(sK3)) ),
% 19.68/3.01      inference(instantiation,[status(thm)],[c_2054]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_15496,plain,
% 19.68/3.01      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 19.68/3.01      | v1_relat_1(k2_funct_1(sK3)) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_15495]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_58002,plain,
% 19.68/3.01      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 19.68/3.01      | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
% 19.68/3.01      | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_7186,c_46,c_47,c_48,c_33,c_855,c_1508,c_1917,c_5060,
% 19.68/3.01                 c_5140,c_5688,c_6522,c_15496]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_4,plain,
% 19.68/3.01      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 19.68/3.01      | ~ v1_relat_1(X0)
% 19.68/3.01      | ~ v1_relat_1(X1)
% 19.68/3.01      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 19.68/3.01      inference(cnf_transformation,[],[f61]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1418,plain,
% 19.68/3.01      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 19.68/3.01      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
% 19.68/3.01      | v1_relat_1(X1) != iProver_top
% 19.68/3.01      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_6667,plain,
% 19.68/3.01      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k2_relat_1(k2_funct_1(sK3))
% 19.68/3.01      | r1_tarski(sK0,k2_relat_1(X0)) != iProver_top
% 19.68/3.01      | v1_relat_1(X0) != iProver_top
% 19.68/3.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_6637,c_1418]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_6668,plain,
% 19.68/3.01      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 19.68/3.01      | r1_tarski(sK0,k2_relat_1(X0)) != iProver_top
% 19.68/3.01      | v1_relat_1(X0) != iProver_top
% 19.68/3.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 19.68/3.01      inference(light_normalisation,[status(thm)],[c_6667,c_6638]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_18631,plain,
% 19.68/3.01      ( v1_relat_1(X0) != iProver_top
% 19.68/3.01      | r1_tarski(sK0,k2_relat_1(X0)) != iProver_top
% 19.68/3.01      | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_6668,c_46,c_47,c_48,c_33,c_855,c_1508,c_5060,c_5688,
% 19.68/3.01                 c_6522,c_15496]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_18632,plain,
% 19.68/3.01      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 19.68/3.01      | r1_tarski(sK0,k2_relat_1(X0)) != iProver_top
% 19.68/3.01      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.01      inference(renaming,[status(thm)],[c_18631]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_18639,plain,
% 19.68/3.01      ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 19.68/3.01      | r1_tarski(sK0,sK0) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_2375,c_18632]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_18671,plain,
% 19.68/3.01      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
% 19.68/3.01      | r1_tarski(sK0,sK0) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) != iProver_top ),
% 19.68/3.01      inference(light_normalisation,[status(thm)],[c_18639,c_7182]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5,plain,
% 19.68/3.01      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 19.68/3.01      inference(cnf_transformation,[],[f101]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_18672,plain,
% 19.68/3.01      ( k1_relat_1(sK3) = sK1
% 19.68/3.01      | r1_tarski(sK0,sK0) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) != iProver_top ),
% 19.68/3.01      inference(demodulation,[status(thm)],[c_18671,c_5]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5691,plain,
% 19.68/3.01      ( ~ v1_funct_2(sK3,sK1,sK0)
% 19.68/3.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.68/3.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 19.68/3.01      | ~ v1_funct_1(sK3)
% 19.68/3.01      | ~ v2_funct_1(sK3) ),
% 19.68/3.01      inference(predicate_to_equality_rev,[status(thm)],[c_5688]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_6524,plain,
% 19.68/3.01      ( ~ v1_funct_2(sK3,sK1,sK0)
% 19.68/3.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 19.68/3.01      | ~ v1_funct_1(sK3)
% 19.68/3.01      | ~ v2_funct_1(k6_partfun1(sK0))
% 19.68/3.01      | v2_funct_1(sK3)
% 19.68/3.01      | sK0 = k1_xboole_0 ),
% 19.68/3.01      inference(predicate_to_equality_rev,[status(thm)],[c_6522]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1408,plain,
% 19.68/3.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_13,plain,
% 19.68/3.01      ( v4_relat_1(X0,X1)
% 19.68/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 19.68/3.01      inference(cnf_transformation,[],[f70]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_2,plain,
% 19.68/3.01      ( r1_tarski(k1_relat_1(X0),X1)
% 19.68/3.01      | ~ v4_relat_1(X0,X1)
% 19.68/3.01      | ~ v1_relat_1(X0) ),
% 19.68/3.01      inference(cnf_transformation,[],[f58]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_416,plain,
% 19.68/3.01      ( r1_tarski(k1_relat_1(X0),X1)
% 19.68/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | ~ v1_relat_1(X0) ),
% 19.68/3.01      inference(resolution,[status(thm)],[c_13,c_2]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_420,plain,
% 19.68/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | r1_tarski(k1_relat_1(X0),X1) ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_416,c_13,c_12,c_2]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_421,plain,
% 19.68/3.01      ( r1_tarski(k1_relat_1(X0),X1)
% 19.68/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 19.68/3.01      inference(renaming,[status(thm)],[c_420]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1390,plain,
% 19.68/3.01      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 19.68/3.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_2575,plain,
% 19.68/3.01      ( r1_tarski(k1_relat_1(k6_partfun1(X0)),X0) = iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_1408,c_1390]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_6,plain,
% 19.68/3.01      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 19.68/3.01      inference(cnf_transformation,[],[f102]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_2578,plain,
% 19.68/3.01      ( r1_tarski(X0,X0) = iProver_top ),
% 19.68/3.01      inference(light_normalisation,[status(thm)],[c_2575,c_6]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_3280,plain,
% 19.68/3.01      ( k2_relat_1(k5_relat_1(sK3,X0)) = k2_relat_1(X0)
% 19.68/3.01      | r1_tarski(k1_relat_1(X0),sK0) != iProver_top
% 19.68/3.01      | v1_relat_1(X0) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_2375,c_1418]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_9206,plain,
% 19.68/3.01      ( v1_relat_1(X0) != iProver_top
% 19.68/3.01      | r1_tarski(k1_relat_1(X0),sK0) != iProver_top
% 19.68/3.01      | k2_relat_1(k5_relat_1(sK3,X0)) = k2_relat_1(X0) ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_3280,c_48,c_1917]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_9207,plain,
% 19.68/3.01      ( k2_relat_1(k5_relat_1(sK3,X0)) = k2_relat_1(X0)
% 19.68/3.01      | r1_tarski(k1_relat_1(X0),sK0) != iProver_top
% 19.68/3.01      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.01      inference(renaming,[status(thm)],[c_9206]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_9214,plain,
% 19.68/3.01      ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k2_relat_1(k2_funct_1(sK3))
% 19.68/3.01      | r1_tarski(sK0,sK0) != iProver_top
% 19.68/3.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_6637,c_9207]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_9217,plain,
% 19.68/3.01      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
% 19.68/3.01      | r1_tarski(sK0,sK0) != iProver_top
% 19.68/3.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 19.68/3.01      inference(light_normalisation,[status(thm)],[c_9214,c_6638,c_7182]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_9218,plain,
% 19.68/3.01      ( k1_relat_1(sK3) = sK1
% 19.68/3.01      | r1_tarski(sK0,sK0) != iProver_top
% 19.68/3.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 19.68/3.01      inference(demodulation,[status(thm)],[c_9217,c_5]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_9227,plain,
% 19.68/3.01      ( k1_relat_1(sK3) = sK1
% 19.68/3.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_2578,c_9218]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_9228,plain,
% 19.68/3.01      ( ~ v1_relat_1(k2_funct_1(sK3)) | k1_relat_1(sK3) = sK1 ),
% 19.68/3.01      inference(predicate_to_equality_rev,[status(thm)],[c_9227]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_19104,plain,
% 19.68/3.01      ( k1_relat_1(sK3) = sK1 ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_18672,c_39,c_38,c_37,c_33,c_855,c_1508,c_5059,c_5691,
% 19.68/3.01                 c_6524,c_9228,c_15495]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1393,plain,
% 19.68/3.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_20,plain,
% 19.68/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 19.68/3.01      | ~ v1_funct_1(X0)
% 19.68/3.01      | ~ v1_funct_1(X3)
% 19.68/3.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 19.68/3.01      inference(cnf_transformation,[],[f77]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_1407,plain,
% 19.68/3.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 19.68/3.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 19.68/3.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.68/3.01      | v1_funct_1(X5) != iProver_top
% 19.68/3.01      | v1_funct_1(X4) != iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5317,plain,
% 19.68/3.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 19.68/3.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.68/3.01      | v1_funct_1(X2) != iProver_top
% 19.68/3.01      | v1_funct_1(sK3) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_1396,c_1407]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5457,plain,
% 19.68/3.01      ( v1_funct_1(X2) != iProver_top
% 19.68/3.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.68/3.01      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_5317,c_46]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5458,plain,
% 19.68/3.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 19.68/3.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.68/3.01      | v1_funct_1(X2) != iProver_top ),
% 19.68/3.01      inference(renaming,[status(thm)],[c_5457]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5465,plain,
% 19.68/3.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 19.68/3.01      | v1_funct_1(sK2) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_1393,c_5458]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5466,plain,
% 19.68/3.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 19.68/3.01      | v1_funct_1(sK2) != iProver_top ),
% 19.68/3.01      inference(light_normalisation,[status(thm)],[c_5465,c_2132]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5596,plain,
% 19.68/3.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 19.68/3.01      inference(global_propositional_subsumption,
% 19.68/3.01                [status(thm)],
% 19.68/3.01                [c_5466,c_43]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5832,plain,
% 19.68/3.01      ( k2_funct_1(sK3) = sK2
% 19.68/3.01      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 19.68/3.01      | k2_relat_1(sK2) != k1_relat_1(sK3)
% 19.68/3.01      | v1_funct_1(sK3) != iProver_top
% 19.68/3.01      | v1_funct_1(sK2) != iProver_top
% 19.68/3.01      | v2_funct_1(sK3) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) != iProver_top
% 19.68/3.01      | v1_relat_1(sK2) != iProver_top ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_5596,c_1413]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_2373,plain,
% 19.68/3.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 19.68/3.01      inference(superposition,[status(thm)],[c_1393,c_1411]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_2374,plain,
% 19.68/3.01      ( k2_relat_1(sK2) = sK1 ),
% 19.68/3.01      inference(light_normalisation,[status(thm)],[c_2373,c_36]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5833,plain,
% 19.68/3.01      ( k2_funct_1(sK3) = sK2
% 19.68/3.01      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 19.68/3.01      | k1_relat_1(sK3) != sK1
% 19.68/3.01      | v1_funct_1(sK3) != iProver_top
% 19.68/3.01      | v1_funct_1(sK2) != iProver_top
% 19.68/3.01      | v2_funct_1(sK3) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) != iProver_top
% 19.68/3.01      | v1_relat_1(sK2) != iProver_top ),
% 19.68/3.01      inference(light_normalisation,[status(thm)],[c_5832,c_2374,c_2375]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_5834,plain,
% 19.68/3.01      ( k2_funct_1(sK3) = sK2
% 19.68/3.01      | k1_relat_1(sK3) != sK1
% 19.68/3.01      | v1_funct_1(sK3) != iProver_top
% 19.68/3.01      | v1_funct_1(sK2) != iProver_top
% 19.68/3.01      | v2_funct_1(sK3) != iProver_top
% 19.68/3.01      | v1_relat_1(sK3) != iProver_top
% 19.68/3.01      | v1_relat_1(sK2) != iProver_top ),
% 19.68/3.01      inference(equality_resolution_simp,[status(thm)],[c_5833]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_2040,plain,
% 19.68/3.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.68/3.01      | v1_relat_1(sK2) ),
% 19.68/3.01      inference(instantiation,[status(thm)],[c_12]) ).
% 19.68/3.01  
% 19.68/3.01  cnf(c_2041,plain,
% 19.68/3.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 19.68/3.01      | v1_relat_1(sK2) = iProver_top ),
% 19.68/3.01      inference(predicate_to_equality,[status(thm)],[c_2040]) ).
% 19.68/3.02  
% 19.68/3.02  cnf(c_11053,plain,
% 19.68/3.02      ( k1_relat_1(sK3) != sK1 | k2_funct_1(sK3) = sK2 ),
% 19.68/3.02      inference(global_propositional_subsumption,
% 19.68/3.02                [status(thm)],
% 19.68/3.02                [c_5834,c_43,c_45,c_46,c_47,c_48,c_33,c_855,c_1508,
% 19.68/3.02                 c_1917,c_2041,c_5060,c_6522]) ).
% 19.68/3.02  
% 19.68/3.02  cnf(c_11054,plain,
% 19.68/3.02      ( k2_funct_1(sK3) = sK2 | k1_relat_1(sK3) != sK1 ),
% 19.68/3.02      inference(renaming,[status(thm)],[c_11053]) ).
% 19.68/3.02  
% 19.68/3.02  cnf(c_19128,plain,
% 19.68/3.02      ( k2_funct_1(sK3) = sK2 | sK1 != sK1 ),
% 19.68/3.02      inference(demodulation,[status(thm)],[c_19104,c_11054]) ).
% 19.68/3.02  
% 19.68/3.02  cnf(c_19136,plain,
% 19.68/3.02      ( k2_funct_1(sK3) = sK2 ),
% 19.68/3.02      inference(equality_resolution_simp,[status(thm)],[c_19128]) ).
% 19.68/3.02  
% 19.68/3.02  cnf(c_58006,plain,
% 19.68/3.02      ( k2_funct_1(sK2) = sK3
% 19.68/3.02      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 19.68/3.02      | v2_funct_1(sK2) != iProver_top ),
% 19.68/3.02      inference(light_normalisation,
% 19.68/3.02                [status(thm)],
% 19.68/3.02                [c_58002,c_19104,c_19136]) ).
% 19.68/3.02  
% 19.68/3.02  cnf(c_58007,plain,
% 19.68/3.02      ( k2_funct_1(sK2) = sK3 | v2_funct_1(sK2) != iProver_top ),
% 19.68/3.02      inference(equality_resolution_simp,[status(thm)],[c_58006]) ).
% 19.68/3.02  
% 19.68/3.02  cnf(c_31,negated_conjecture,
% 19.68/3.02      ( k2_funct_1(sK2) != sK3 ),
% 19.68/3.02      inference(cnf_transformation,[],[f100]) ).
% 19.68/3.02  
% 19.68/3.02  cnf(c_34,negated_conjecture,
% 19.68/3.02      ( v2_funct_1(sK2) ),
% 19.68/3.02      inference(cnf_transformation,[],[f97]) ).
% 19.68/3.02  
% 19.68/3.02  cnf(c_50,plain,
% 19.68/3.02      ( v2_funct_1(sK2) = iProver_top ),
% 19.68/3.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 19.68/3.02  
% 19.68/3.02  cnf(contradiction,plain,
% 19.68/3.02      ( $false ),
% 19.68/3.02      inference(minisat,[status(thm)],[c_58007,c_31,c_50]) ).
% 19.68/3.02  
% 19.68/3.02  
% 19.68/3.02  % SZS output end CNFRefutation for theBenchmark.p
% 19.68/3.02  
% 19.68/3.02  ------                               Statistics
% 19.68/3.02  
% 19.68/3.02  ------ General
% 19.68/3.02  
% 19.68/3.02  abstr_ref_over_cycles:                  0
% 19.68/3.02  abstr_ref_under_cycles:                 0
% 19.68/3.02  gc_basic_clause_elim:                   0
% 19.68/3.02  forced_gc_time:                         0
% 19.68/3.02  parsing_time:                           0.015
% 19.68/3.02  unif_index_cands_time:                  0.
% 19.68/3.02  unif_index_add_time:                    0.
% 19.68/3.02  orderings_time:                         0.
% 19.68/3.02  out_proof_time:                         0.026
% 19.68/3.02  total_time:                             2.197
% 19.68/3.02  num_of_symbols:                         53
% 19.68/3.02  num_of_terms:                           85462
% 19.68/3.02  
% 19.68/3.02  ------ Preprocessing
% 19.68/3.02  
% 19.68/3.02  num_of_splits:                          0
% 19.68/3.02  num_of_split_atoms:                     0
% 19.68/3.02  num_of_reused_defs:                     0
% 19.68/3.02  num_eq_ax_congr_red:                    2
% 19.68/3.02  num_of_sem_filtered_clauses:            1
% 19.68/3.02  num_of_subtypes:                        0
% 19.68/3.02  monotx_restored_types:                  0
% 19.68/3.02  sat_num_of_epr_types:                   0
% 19.68/3.02  sat_num_of_non_cyclic_types:            0
% 19.68/3.02  sat_guarded_non_collapsed_types:        0
% 19.68/3.02  num_pure_diseq_elim:                    0
% 19.68/3.02  simp_replaced_by:                       0
% 19.68/3.02  res_preprocessed:                       198
% 19.68/3.02  prep_upred:                             0
% 19.68/3.02  prep_unflattend:                        14
% 19.68/3.02  smt_new_axioms:                         0
% 19.68/3.02  pred_elim_cands:                        6
% 19.68/3.02  pred_elim:                              2
% 19.68/3.02  pred_elim_cl:                           3
% 19.68/3.02  pred_elim_cycles:                       5
% 19.68/3.02  merged_defs:                            0
% 19.68/3.02  merged_defs_ncl:                        0
% 19.68/3.02  bin_hyper_res:                          0
% 19.68/3.02  prep_cycles:                            4
% 19.68/3.02  pred_elim_time:                         0.007
% 19.68/3.02  splitting_time:                         0.
% 19.68/3.02  sem_filter_time:                        0.
% 19.68/3.02  monotx_time:                            0.
% 19.68/3.02  subtype_inf_time:                       0.
% 19.68/3.02  
% 19.68/3.02  ------ Problem properties
% 19.68/3.02  
% 19.68/3.02  clauses:                                40
% 19.68/3.02  conjectures:                            11
% 19.68/3.02  epr:                                    7
% 19.68/3.02  horn:                                   36
% 19.68/3.02  ground:                                 12
% 19.68/3.02  unary:                                  17
% 19.68/3.02  binary:                                 4
% 19.68/3.02  lits:                                   149
% 19.68/3.02  lits_eq:                                34
% 19.68/3.02  fd_pure:                                0
% 19.68/3.02  fd_pseudo:                              0
% 19.68/3.02  fd_cond:                                4
% 19.68/3.02  fd_pseudo_cond:                         1
% 19.68/3.02  ac_symbols:                             0
% 19.68/3.02  
% 19.68/3.02  ------ Propositional Solver
% 19.68/3.02  
% 19.68/3.02  prop_solver_calls:                      37
% 19.68/3.02  prop_fast_solver_calls:                 3893
% 19.68/3.02  smt_solver_calls:                       0
% 19.68/3.02  smt_fast_solver_calls:                  0
% 19.68/3.02  prop_num_of_clauses:                    31662
% 19.68/3.02  prop_preprocess_simplified:             46889
% 19.68/3.02  prop_fo_subsumed:                       565
% 19.68/3.02  prop_solver_time:                       0.
% 19.68/3.02  smt_solver_time:                        0.
% 19.68/3.02  smt_fast_solver_time:                   0.
% 19.68/3.02  prop_fast_solver_time:                  0.
% 19.68/3.02  prop_unsat_core_time:                   0.005
% 19.68/3.02  
% 19.68/3.02  ------ QBF
% 19.68/3.02  
% 19.68/3.02  qbf_q_res:                              0
% 19.68/3.02  qbf_num_tautologies:                    0
% 19.68/3.02  qbf_prep_cycles:                        0
% 19.68/3.02  
% 19.68/3.02  ------ BMC1
% 19.68/3.02  
% 19.68/3.02  bmc1_current_bound:                     -1
% 19.68/3.02  bmc1_last_solved_bound:                 -1
% 19.68/3.02  bmc1_unsat_core_size:                   -1
% 19.68/3.02  bmc1_unsat_core_parents_size:           -1
% 19.68/3.02  bmc1_merge_next_fun:                    0
% 19.68/3.02  bmc1_unsat_core_clauses_time:           0.
% 19.68/3.02  
% 19.68/3.02  ------ Instantiation
% 19.68/3.02  
% 19.68/3.02  inst_num_of_clauses:                    7912
% 19.68/3.02  inst_num_in_passive:                    2007
% 19.68/3.02  inst_num_in_active:                     2606
% 19.68/3.02  inst_num_in_unprocessed:                3300
% 19.68/3.02  inst_num_of_loops:                      2880
% 19.68/3.02  inst_num_of_learning_restarts:          0
% 19.68/3.02  inst_num_moves_active_passive:          271
% 19.68/3.02  inst_lit_activity:                      0
% 19.68/3.02  inst_lit_activity_moves:                4
% 19.68/3.02  inst_num_tautologies:                   0
% 19.68/3.02  inst_num_prop_implied:                  0
% 19.68/3.02  inst_num_existing_simplified:           0
% 19.68/3.02  inst_num_eq_res_simplified:             0
% 19.68/3.02  inst_num_child_elim:                    0
% 19.68/3.02  inst_num_of_dismatching_blockings:      3808
% 19.68/3.02  inst_num_of_non_proper_insts:           6805
% 19.68/3.02  inst_num_of_duplicates:                 0
% 19.68/3.02  inst_inst_num_from_inst_to_res:         0
% 19.68/3.02  inst_dismatching_checking_time:         0.
% 19.68/3.02  
% 19.68/3.02  ------ Resolution
% 19.68/3.02  
% 19.68/3.02  res_num_of_clauses:                     0
% 19.68/3.02  res_num_in_passive:                     0
% 19.68/3.02  res_num_in_active:                      0
% 19.68/3.02  res_num_of_loops:                       202
% 19.68/3.02  res_forward_subset_subsumed:            436
% 19.68/3.02  res_backward_subset_subsumed:           2
% 19.68/3.02  res_forward_subsumed:                   0
% 19.68/3.02  res_backward_subsumed:                  0
% 19.68/3.02  res_forward_subsumption_resolution:     2
% 19.68/3.02  res_backward_subsumption_resolution:    0
% 19.68/3.02  res_clause_to_clause_subsumption:       4176
% 19.68/3.02  res_orphan_elimination:                 0
% 19.68/3.02  res_tautology_del:                      287
% 19.68/3.02  res_num_eq_res_simplified:              1
% 19.68/3.02  res_num_sel_changes:                    0
% 19.68/3.02  res_moves_from_active_to_pass:          0
% 19.68/3.02  
% 19.68/3.02  ------ Superposition
% 19.68/3.02  
% 19.68/3.02  sup_time_total:                         0.
% 19.68/3.02  sup_time_generating:                    0.
% 19.68/3.02  sup_time_sim_full:                      0.
% 19.68/3.02  sup_time_sim_immed:                     0.
% 19.68/3.02  
% 19.68/3.02  sup_num_of_clauses:                     1932
% 19.68/3.02  sup_num_in_active:                      489
% 19.68/3.02  sup_num_in_passive:                     1443
% 19.68/3.02  sup_num_of_loops:                       574
% 19.68/3.02  sup_fw_superposition:                   1045
% 19.68/3.02  sup_bw_superposition:                   1216
% 19.68/3.02  sup_immediate_simplified:               751
% 19.68/3.02  sup_given_eliminated:                   0
% 19.68/3.02  comparisons_done:                       0
% 19.68/3.02  comparisons_avoided:                    4
% 19.68/3.02  
% 19.68/3.02  ------ Simplifications
% 19.68/3.02  
% 19.68/3.02  
% 19.68/3.02  sim_fw_subset_subsumed:                 70
% 19.68/3.02  sim_bw_subset_subsumed:                 96
% 19.68/3.02  sim_fw_subsumed:                        67
% 19.68/3.02  sim_bw_subsumed:                        1
% 19.68/3.02  sim_fw_subsumption_res:                 0
% 19.68/3.02  sim_bw_subsumption_res:                 0
% 19.68/3.02  sim_tautology_del:                      0
% 19.68/3.02  sim_eq_tautology_del:                   86
% 19.68/3.02  sim_eq_res_simp:                        6
% 19.68/3.02  sim_fw_demodulated:                     64
% 19.68/3.02  sim_bw_demodulated:                     43
% 19.68/3.02  sim_light_normalised:                   647
% 19.68/3.02  sim_joinable_taut:                      0
% 19.68/3.02  sim_joinable_simp:                      0
% 19.68/3.02  sim_ac_normalised:                      0
% 19.68/3.02  sim_smt_subsumption:                    0
% 19.68/3.02  
%------------------------------------------------------------------------------
