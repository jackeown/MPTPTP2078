%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:11 EST 2020

% Result     : Theorem 11.69s
% Output     : CNFRefutation 11.69s
% Verified   : 
% Statistics : Number of formulae       :  293 (3124 expanded)
%              Number of clauses        :  205 (1030 expanded)
%              Number of leaves         :   27 ( 753 expanded)
%              Depth                    :   27
%              Number of atoms          :  991 (24891 expanded)
%              Number of equality atoms :  506 (8812 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f51,f50])).

fof(f87,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f41,plain,(
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
    inference(flattening,[],[f41])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f19,axiom,(
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

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f52])).

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

fof(f43,plain,(
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
    inference(flattening,[],[f43])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f63,f72])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f60,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f58,f72])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f72])).

fof(f55,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_424,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_432,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_424,c_17])).

cnf(c_720,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_432])).

cnf(c_1379,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_742,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1449,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_1738,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1379,c_37,c_35,c_34,c_32,c_720,c_1449])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_436,plain,
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
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_437,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_524,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_437])).

cnf(c_719,plain,
    ( ~ v1_funct_2(X0_50,X0_51,sK0)
    | ~ v1_funct_2(X1_50,sK0,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k2_relset_1(X0_51,sK0,X0_50) = sK0
    | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_524])).

cnf(c_1380,plain,
    ( k2_relset_1(X0_51,sK0,X0_50) = sK0
    | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | v1_funct_2(X0_50,X0_51,sK0) != iProver_top
    | v1_funct_2(X1_50,sK0,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_1831,plain,
    ( k2_relset_1(X0_51,sK0,X0_50) = sK0
    | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k6_partfun1(sK0)
    | v1_funct_2(X0_50,X0_51,sK0) != iProver_top
    | v1_funct_2(X1_50,sK0,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1380,c_1738])).

cnf(c_1835,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1738,c_1831])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1457,plain,
    ( ~ v1_funct_2(X0_50,sK0,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,X0_50,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_1459,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_757,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1501,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_1838,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1835,c_37,c_36,c_35,c_34,c_33,c_32,c_1459,c_1501])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_733,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = X1_51
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1370,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = X1_51
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51)
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_3486,plain,
    ( sK0 = k1_xboole_0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_1370])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_730,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_728,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1423,plain,
    ( ~ v1_funct_2(X0_50,X0_51,sK0)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X0_51,sK0,X0_50) != sK0
    | k1_xboole_0 = sK0
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51) ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_1493,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) != sK0
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_1423])).

cnf(c_761,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_1515,plain,
    ( X0_50 != X1_50
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_50
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_50 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_1570,plain,
    ( X0_50 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_50
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1515])).

cnf(c_1715,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_737,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ v1_funct_2(X1_50,X2_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | v2_funct_1(X0_50)
    | ~ v2_funct_1(k1_partfun1(X2_51,X0_51,X0_51,X1_51,X1_50,X0_50))
    | k2_relset_1(X2_51,X0_51,X1_50) != X0_51
    | k1_xboole_0 = X1_51 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1523,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ v1_funct_2(sK3,X1_51,X2_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(X0_51,X1_51,X1_51,X2_51,X0_50,sK3))
    | v2_funct_1(sK3)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = X2_51 ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_1678,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ v1_funct_2(sK3,X1_51,sK0)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK0)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(X0_51,X1_51,X1_51,sK0,X0_50,sK3))
    | v2_funct_1(sK3)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1523])).

cnf(c_1792,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_770,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1952,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0_50 ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_2409,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v2_funct_1(k6_partfun1(sK0))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1952])).

cnf(c_10,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_745,plain,
    ( v2_funct_1(k6_partfun1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3042,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_745])).

cnf(c_21346,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3486,c_37,c_36,c_35,c_34,c_33,c_32,c_730,c_728,c_720,c_1449,c_1459,c_1493,c_1501,c_1715,c_1792,c_2409,c_3042])).

cnf(c_1366,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = X2_51
    | v1_funct_2(X1_50,X1_51,X2_51) != iProver_top
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v2_funct_1(X1_50) = iProver_top
    | v2_funct_1(k1_partfun1(X0_51,X1_51,X1_51,X2_51,X0_50,X1_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_3516,plain,
    ( k1_xboole_0 = X0_51
    | v1_funct_2(X0_50,sK1,X0_51) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X0_50) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_51,sK2,X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_1366])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_39,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3683,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | v1_funct_2(X0_50,sK1,X0_51) != iProver_top
    | k1_xboole_0 = X0_51
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51))) != iProver_top
    | v2_funct_1(X0_50) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_51,sK2,X0_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3516,c_38,c_39,c_40])).

cnf(c_3684,plain,
    ( k1_xboole_0 = X0_51
    | v1_funct_2(X0_50,sK1,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_51,sK2,X0_50)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3683])).

cnf(c_3687,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1738,c_3684])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1793,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1792])).

cnf(c_2410,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0)
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) = iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2409])).

cnf(c_3043,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3042])).

cnf(c_3690,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3687,c_37,c_38,c_39,c_35,c_40,c_34,c_41,c_42,c_32,c_43,c_730,c_728,c_720,c_1449,c_1501,c_1715,c_1793,c_2410,c_3043])).

cnf(c_725,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1374,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_748,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k2_funct_1(X0_50) = k4_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1355,plain,
    ( k2_funct_1(X0_50) = k4_relat_1(X0_50)
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_2754,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1374,c_1355])).

cnf(c_727,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1372,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1359,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_2184,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_1359])).

cnf(c_2946,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2754,c_2184])).

cnf(c_2947,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2946])).

cnf(c_3694,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3690,c_2947])).

cnf(c_21348,plain,
    ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_21346,c_3694])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_755,plain,
    ( ~ v1_relat_1(X0_50)
    | v1_relat_1(k4_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1348,plain,
    ( v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(k4_relat_1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_724,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1375,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_2185,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_1359])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_752,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(X1_50)
    | ~ v1_relat_1(X2_50)
    | k5_relat_1(k5_relat_1(X0_50,X2_50),X1_50) = k5_relat_1(X0_50,k5_relat_1(X2_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1351,plain,
    ( k5_relat_1(k5_relat_1(X0_50,X1_50),X2_50) = k5_relat_1(X0_50,k5_relat_1(X1_50,X2_50))
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X2_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_2765,plain,
    ( k5_relat_1(sK2,k5_relat_1(X0_50,X1_50)) = k5_relat_1(k5_relat_1(sK2,X0_50),X1_50)
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2185,c_1351])).

cnf(c_4552,plain,
    ( k5_relat_1(k5_relat_1(sK2,sK3),X0_50) = k5_relat_1(sK2,k5_relat_1(sK3,X0_50))
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2184,c_2765])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1364,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_2809,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_1364])).

cnf(c_3130,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2809,c_41])).

cnf(c_3131,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3130])).

cnf(c_3137,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_3131])).

cnf(c_3141,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3137,c_1738])).

cnf(c_4438,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3141,c_38])).

cnf(c_4554,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,X0_50)) = k5_relat_1(k6_partfun1(sK0),X0_50)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4552,c_4438])).

cnf(c_9287,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(X0_50))) = k5_relat_1(k6_partfun1(sK0),k4_relat_1(X0_50))
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_4554])).

cnf(c_11304,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k4_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_2184,c_9287])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_750,plain,
    ( ~ v1_relat_1(X0_50)
    | k5_relat_1(k6_partfun1(X0_51),X0_50) = k7_relat_1(X0_50,X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1353,plain,
    ( k5_relat_1(k6_partfun1(X0_51),X0_50) = k7_relat_1(X0_50,X0_51)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_2154,plain,
    ( k5_relat_1(k6_partfun1(X0_51),k4_relat_1(X0_50)) = k7_relat_1(k4_relat_1(X0_50),X0_51)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_1353])).

cnf(c_6109,plain,
    ( k5_relat_1(k6_partfun1(X0_51),k4_relat_1(sK3)) = k7_relat_1(k4_relat_1(sK3),X0_51) ),
    inference(superposition,[status(thm)],[c_2184,c_2154])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_746,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | v1_relat_1(k2_funct_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1357,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(k2_funct_1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_749,plain,
    ( ~ v1_relat_1(X0_50)
    | k7_relat_1(X0_50,k1_relat_1(X0_50)) = X0_50 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1354,plain,
    ( k7_relat_1(X0_50,k1_relat_1(X0_50)) = X0_50
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_2231,plain,
    ( k7_relat_1(k2_funct_1(X0_50),k1_relat_1(k2_funct_1(X0_50))) = k2_funct_1(X0_50)
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_1354])).

cnf(c_7946,plain,
    ( k7_relat_1(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3))) = k2_funct_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1374,c_2231])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_753,plain,
    ( ~ v1_relat_1(X0_50)
    | k1_relat_1(k4_relat_1(X0_50)) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1350,plain,
    ( k1_relat_1(k4_relat_1(X0_50)) = k2_relat_1(X0_50)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_2306,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2184,c_1350])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1360,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_2251,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1372,c_1360])).

cnf(c_2255,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2251,c_1838])).

cnf(c_2310,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2306,c_2255])).

cnf(c_7955,plain,
    ( k7_relat_1(k4_relat_1(sK3),sK0) = k4_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7946,c_2310,c_3694])).

cnf(c_8374,plain,
    ( k7_relat_1(k4_relat_1(sK3),sK0) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7955,c_2184])).

cnf(c_11313,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(sK3))) = k4_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_11304,c_6109,c_8374])).

cnf(c_21351,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = k4_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_21348,c_11313])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_751,plain,
    ( ~ v1_relat_1(X0_50)
    | k5_relat_1(X0_50,k6_partfun1(k2_relat_1(X0_50))) = X0_50 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1352,plain,
    ( k5_relat_1(X0_50,k6_partfun1(k2_relat_1(X0_50))) = X0_50
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_2401,plain,
    ( k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_2185,c_1352])).

cnf(c_2252,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1375,c_1360])).

cnf(c_2254,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2252,c_728])).

cnf(c_2402,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2401,c_2254])).

cnf(c_21352,plain,
    ( k4_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_21351,c_2402])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_754,plain,
    ( ~ v1_relat_1(X0_50)
    | k2_relat_1(k4_relat_1(X0_50)) = k1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1349,plain,
    ( k2_relat_1(k4_relat_1(X0_50)) = k1_relat_1(X0_50)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_2307,plain,
    ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2184,c_1349])).

cnf(c_21678,plain,
    ( k1_relat_1(sK3) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_21352,c_2307])).

cnf(c_21679,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_21678,c_2254])).

cnf(c_2305,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2184,c_1354])).

cnf(c_21686,plain,
    ( k7_relat_1(sK3,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_21679,c_2305])).

cnf(c_6108,plain,
    ( k5_relat_1(k6_partfun1(X0_51),k4_relat_1(sK2)) = k7_relat_1(k4_relat_1(sK2),X0_51) ),
    inference(superposition,[status(thm)],[c_2185,c_2154])).

cnf(c_722,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_1377,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_2763,plain,
    ( k5_relat_1(k2_funct_1(X0_50),k5_relat_1(X1_50,X2_50)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_50),X1_50),X2_50)
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X2_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_1351])).

cnf(c_13463,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_50),X1_50) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_50,X1_50))
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_2763])).

cnf(c_2755,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_1355])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_45,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_819,plain,
    ( k2_funct_1(X0_50) = k4_relat_1(X0_50)
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_821,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_3067,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2755,c_38,c_45,c_821,c_2185])).

cnf(c_13471,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0_50,X1_50)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0_50),X1_50)
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13463,c_3067])).

cnf(c_15178,plain,
    ( v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0_50,X1_50)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0_50),X1_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13471,c_2185])).

cnf(c_15179,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0_50,X1_50)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0_50),X1_50)
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_15178])).

cnf(c_15184,plain,
    ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),X0_50) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0_50))
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2185,c_15179])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_734,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = X1_51
    | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(X1_51) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1369,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = X1_51
    | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(X1_51)
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_734])).

cnf(c_3479,plain,
    ( sK1 = k1_xboole_0
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_1369])).

cnf(c_3481,plain,
    ( sK1 = k1_xboole_0
    | k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3479,c_3067])).

cnf(c_758,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_795,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_731,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_762,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_1445,plain,
    ( sK1 != X0_51
    | k1_xboole_0 != X0_51
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_1446,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_3785,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3481,c_38,c_39,c_40,c_45,c_795,c_731,c_1446])).

cnf(c_15190,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0_50)) = k5_relat_1(k6_partfun1(sK1),X0_50)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15184,c_3785])).

cnf(c_15265,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,k4_relat_1(X0_50))) = k5_relat_1(k6_partfun1(sK1),k4_relat_1(X0_50))
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_15190])).

cnf(c_15381,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,k4_relat_1(sK2))) = k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2185,c_15265])).

cnf(c_3485,plain,
    ( sK1 = k1_xboole_0
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_1370])).

cnf(c_3487,plain,
    ( sK1 = k1_xboole_0
    | k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(sK0)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3485,c_3067])).

cnf(c_3788,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3487,c_38,c_39,c_40,c_45,c_795,c_731,c_1446])).

cnf(c_15267,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2184,c_15190])).

cnf(c_15278,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(light_normalisation,[status(thm)],[c_15267,c_4438])).

cnf(c_2304,plain,
    ( k5_relat_1(k6_partfun1(X0_51),sK3) = k7_relat_1(sK3,X0_51) ),
    inference(superposition,[status(thm)],[c_2184,c_1353])).

cnf(c_15279,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k7_relat_1(sK3,sK1) ),
    inference(demodulation,[status(thm)],[c_15278,c_2304])).

cnf(c_15392,plain,
    ( k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)) = k7_relat_1(sK3,sK1) ),
    inference(light_normalisation,[status(thm)],[c_15381,c_3788,c_15279])).

cnf(c_15509,plain,
    ( k7_relat_1(k4_relat_1(sK2),sK1) = k7_relat_1(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_6108,c_15392])).

cnf(c_7947,plain,
    ( k7_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_2231])).

cnf(c_2399,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2185,c_1350])).

cnf(c_2403,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2399,c_2254])).

cnf(c_7954,plain,
    ( k7_relat_1(k4_relat_1(sK2),sK1) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7947,c_2403,c_3067])).

cnf(c_8371,plain,
    ( k7_relat_1(k4_relat_1(sK2),sK1) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7954,c_2185])).

cnf(c_15511,plain,
    ( k7_relat_1(sK3,sK1) = k4_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_15509,c_8371])).

cnf(c_21864,plain,
    ( k4_relat_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_21686,c_15511])).

cnf(c_26,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_732,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3069,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_3067,c_732])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21864,c_3069])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:36:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 11.69/1.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.69/1.97  
% 11.69/1.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.69/1.97  
% 11.69/1.97  ------  iProver source info
% 11.69/1.97  
% 11.69/1.97  git: date: 2020-06-30 10:37:57 +0100
% 11.69/1.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.69/1.97  git: non_committed_changes: false
% 11.69/1.97  git: last_make_outside_of_git: false
% 11.69/1.97  
% 11.69/1.97  ------ 
% 11.69/1.97  
% 11.69/1.97  ------ Input Options
% 11.69/1.97  
% 11.69/1.97  --out_options                           all
% 11.69/1.97  --tptp_safe_out                         true
% 11.69/1.97  --problem_path                          ""
% 11.69/1.97  --include_path                          ""
% 11.69/1.97  --clausifier                            res/vclausify_rel
% 11.69/1.97  --clausifier_options                    ""
% 11.69/1.97  --stdin                                 false
% 11.69/1.97  --stats_out                             all
% 11.69/1.97  
% 11.69/1.97  ------ General Options
% 11.69/1.97  
% 11.69/1.97  --fof                                   false
% 11.69/1.97  --time_out_real                         305.
% 11.69/1.97  --time_out_virtual                      -1.
% 11.69/1.97  --symbol_type_check                     false
% 11.69/1.97  --clausify_out                          false
% 11.69/1.97  --sig_cnt_out                           false
% 11.69/1.97  --trig_cnt_out                          false
% 11.69/1.97  --trig_cnt_out_tolerance                1.
% 11.69/1.97  --trig_cnt_out_sk_spl                   false
% 11.69/1.97  --abstr_cl_out                          false
% 11.69/1.97  
% 11.69/1.97  ------ Global Options
% 11.69/1.97  
% 11.69/1.97  --schedule                              default
% 11.69/1.97  --add_important_lit                     false
% 11.69/1.97  --prop_solver_per_cl                    1000
% 11.69/1.97  --min_unsat_core                        false
% 11.69/1.97  --soft_assumptions                      false
% 11.69/1.97  --soft_lemma_size                       3
% 11.69/1.97  --prop_impl_unit_size                   0
% 11.69/1.97  --prop_impl_unit                        []
% 11.69/1.97  --share_sel_clauses                     true
% 11.69/1.97  --reset_solvers                         false
% 11.69/1.97  --bc_imp_inh                            [conj_cone]
% 11.69/1.97  --conj_cone_tolerance                   3.
% 11.69/1.97  --extra_neg_conj                        none
% 11.69/1.97  --large_theory_mode                     true
% 11.69/1.97  --prolific_symb_bound                   200
% 11.69/1.97  --lt_threshold                          2000
% 11.69/1.97  --clause_weak_htbl                      true
% 11.69/1.97  --gc_record_bc_elim                     false
% 11.69/1.97  
% 11.69/1.97  ------ Preprocessing Options
% 11.69/1.97  
% 11.69/1.97  --preprocessing_flag                    true
% 11.69/1.97  --time_out_prep_mult                    0.1
% 11.69/1.97  --splitting_mode                        input
% 11.69/1.97  --splitting_grd                         true
% 11.69/1.97  --splitting_cvd                         false
% 11.69/1.97  --splitting_cvd_svl                     false
% 11.69/1.97  --splitting_nvd                         32
% 11.69/1.97  --sub_typing                            true
% 11.69/1.97  --prep_gs_sim                           true
% 11.69/1.97  --prep_unflatten                        true
% 11.69/1.97  --prep_res_sim                          true
% 11.69/1.97  --prep_upred                            true
% 11.69/1.97  --prep_sem_filter                       exhaustive
% 11.69/1.97  --prep_sem_filter_out                   false
% 11.69/1.97  --pred_elim                             true
% 11.69/1.97  --res_sim_input                         true
% 11.69/1.97  --eq_ax_congr_red                       true
% 11.69/1.97  --pure_diseq_elim                       true
% 11.69/1.97  --brand_transform                       false
% 11.69/1.97  --non_eq_to_eq                          false
% 11.69/1.97  --prep_def_merge                        true
% 11.69/1.97  --prep_def_merge_prop_impl              false
% 11.69/1.97  --prep_def_merge_mbd                    true
% 11.69/1.97  --prep_def_merge_tr_red                 false
% 11.69/1.97  --prep_def_merge_tr_cl                  false
% 11.69/1.97  --smt_preprocessing                     true
% 11.69/1.97  --smt_ac_axioms                         fast
% 11.69/1.97  --preprocessed_out                      false
% 11.69/1.97  --preprocessed_stats                    false
% 11.69/1.97  
% 11.69/1.97  ------ Abstraction refinement Options
% 11.69/1.97  
% 11.69/1.97  --abstr_ref                             []
% 11.69/1.97  --abstr_ref_prep                        false
% 11.69/1.97  --abstr_ref_until_sat                   false
% 11.69/1.97  --abstr_ref_sig_restrict                funpre
% 11.69/1.97  --abstr_ref_af_restrict_to_split_sk     false
% 11.69/1.97  --abstr_ref_under                       []
% 11.69/1.97  
% 11.69/1.97  ------ SAT Options
% 11.69/1.97  
% 11.69/1.97  --sat_mode                              false
% 11.69/1.97  --sat_fm_restart_options                ""
% 11.69/1.97  --sat_gr_def                            false
% 11.69/1.97  --sat_epr_types                         true
% 11.69/1.97  --sat_non_cyclic_types                  false
% 11.69/1.97  --sat_finite_models                     false
% 11.69/1.97  --sat_fm_lemmas                         false
% 11.69/1.97  --sat_fm_prep                           false
% 11.69/1.97  --sat_fm_uc_incr                        true
% 11.69/1.97  --sat_out_model                         small
% 11.69/1.97  --sat_out_clauses                       false
% 11.69/1.97  
% 11.69/1.97  ------ QBF Options
% 11.69/1.97  
% 11.69/1.97  --qbf_mode                              false
% 11.69/1.97  --qbf_elim_univ                         false
% 11.69/1.97  --qbf_dom_inst                          none
% 11.69/1.97  --qbf_dom_pre_inst                      false
% 11.69/1.97  --qbf_sk_in                             false
% 11.69/1.97  --qbf_pred_elim                         true
% 11.69/1.97  --qbf_split                             512
% 11.69/1.97  
% 11.69/1.97  ------ BMC1 Options
% 11.69/1.97  
% 11.69/1.97  --bmc1_incremental                      false
% 11.69/1.97  --bmc1_axioms                           reachable_all
% 11.69/1.97  --bmc1_min_bound                        0
% 11.69/1.97  --bmc1_max_bound                        -1
% 11.69/1.97  --bmc1_max_bound_default                -1
% 11.69/1.97  --bmc1_symbol_reachability              true
% 11.69/1.97  --bmc1_property_lemmas                  false
% 11.69/1.97  --bmc1_k_induction                      false
% 11.69/1.97  --bmc1_non_equiv_states                 false
% 11.69/1.97  --bmc1_deadlock                         false
% 11.69/1.97  --bmc1_ucm                              false
% 11.69/1.97  --bmc1_add_unsat_core                   none
% 11.69/1.97  --bmc1_unsat_core_children              false
% 11.69/1.97  --bmc1_unsat_core_extrapolate_axioms    false
% 11.69/1.97  --bmc1_out_stat                         full
% 11.69/1.97  --bmc1_ground_init                      false
% 11.69/1.97  --bmc1_pre_inst_next_state              false
% 11.69/1.97  --bmc1_pre_inst_state                   false
% 11.69/1.97  --bmc1_pre_inst_reach_state             false
% 11.69/1.97  --bmc1_out_unsat_core                   false
% 11.69/1.97  --bmc1_aig_witness_out                  false
% 11.69/1.97  --bmc1_verbose                          false
% 11.69/1.97  --bmc1_dump_clauses_tptp                false
% 11.69/1.97  --bmc1_dump_unsat_core_tptp             false
% 11.69/1.97  --bmc1_dump_file                        -
% 11.69/1.97  --bmc1_ucm_expand_uc_limit              128
% 11.69/1.97  --bmc1_ucm_n_expand_iterations          6
% 11.69/1.97  --bmc1_ucm_extend_mode                  1
% 11.69/1.97  --bmc1_ucm_init_mode                    2
% 11.69/1.97  --bmc1_ucm_cone_mode                    none
% 11.69/1.97  --bmc1_ucm_reduced_relation_type        0
% 11.69/1.97  --bmc1_ucm_relax_model                  4
% 11.69/1.97  --bmc1_ucm_full_tr_after_sat            true
% 11.69/1.97  --bmc1_ucm_expand_neg_assumptions       false
% 11.69/1.97  --bmc1_ucm_layered_model                none
% 11.69/1.97  --bmc1_ucm_max_lemma_size               10
% 11.69/1.97  
% 11.69/1.97  ------ AIG Options
% 11.69/1.97  
% 11.69/1.97  --aig_mode                              false
% 11.69/1.97  
% 11.69/1.97  ------ Instantiation Options
% 11.69/1.97  
% 11.69/1.97  --instantiation_flag                    true
% 11.69/1.97  --inst_sos_flag                         true
% 11.69/1.97  --inst_sos_phase                        true
% 11.69/1.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.69/1.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.69/1.97  --inst_lit_sel_side                     num_symb
% 11.69/1.97  --inst_solver_per_active                1400
% 11.69/1.97  --inst_solver_calls_frac                1.
% 11.69/1.97  --inst_passive_queue_type               priority_queues
% 11.69/1.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.69/1.97  --inst_passive_queues_freq              [25;2]
% 11.69/1.97  --inst_dismatching                      true
% 11.69/1.97  --inst_eager_unprocessed_to_passive     true
% 11.69/1.97  --inst_prop_sim_given                   true
% 11.69/1.97  --inst_prop_sim_new                     false
% 11.69/1.97  --inst_subs_new                         false
% 11.69/1.97  --inst_eq_res_simp                      false
% 11.69/1.97  --inst_subs_given                       false
% 11.69/1.97  --inst_orphan_elimination               true
% 11.69/1.97  --inst_learning_loop_flag               true
% 11.69/1.97  --inst_learning_start                   3000
% 11.69/1.97  --inst_learning_factor                  2
% 11.69/1.97  --inst_start_prop_sim_after_learn       3
% 11.69/1.97  --inst_sel_renew                        solver
% 11.69/1.97  --inst_lit_activity_flag                true
% 11.69/1.97  --inst_restr_to_given                   false
% 11.69/1.97  --inst_activity_threshold               500
% 11.69/1.97  --inst_out_proof                        true
% 11.69/1.97  
% 11.69/1.97  ------ Resolution Options
% 11.69/1.97  
% 11.69/1.97  --resolution_flag                       true
% 11.69/1.97  --res_lit_sel                           adaptive
% 11.69/1.97  --res_lit_sel_side                      none
% 11.69/1.97  --res_ordering                          kbo
% 11.69/1.97  --res_to_prop_solver                    active
% 11.69/1.97  --res_prop_simpl_new                    false
% 11.69/1.97  --res_prop_simpl_given                  true
% 11.69/1.97  --res_passive_queue_type                priority_queues
% 11.69/1.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.69/1.97  --res_passive_queues_freq               [15;5]
% 11.69/1.97  --res_forward_subs                      full
% 11.69/1.97  --res_backward_subs                     full
% 11.69/1.97  --res_forward_subs_resolution           true
% 11.69/1.97  --res_backward_subs_resolution          true
% 11.69/1.97  --res_orphan_elimination                true
% 11.69/1.97  --res_time_limit                        2.
% 11.69/1.97  --res_out_proof                         true
% 11.69/1.97  
% 11.69/1.97  ------ Superposition Options
% 11.69/1.97  
% 11.69/1.97  --superposition_flag                    true
% 11.69/1.97  --sup_passive_queue_type                priority_queues
% 11.69/1.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.69/1.97  --sup_passive_queues_freq               [8;1;4]
% 11.69/1.97  --demod_completeness_check              fast
% 11.69/1.97  --demod_use_ground                      true
% 11.69/1.97  --sup_to_prop_solver                    passive
% 11.69/1.97  --sup_prop_simpl_new                    true
% 11.69/1.97  --sup_prop_simpl_given                  true
% 11.69/1.97  --sup_fun_splitting                     true
% 11.69/1.97  --sup_smt_interval                      50000
% 11.69/1.97  
% 11.69/1.97  ------ Superposition Simplification Setup
% 11.69/1.97  
% 11.69/1.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.69/1.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.69/1.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.69/1.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.69/1.97  --sup_full_triv                         [TrivRules;PropSubs]
% 11.69/1.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.69/1.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.69/1.97  --sup_immed_triv                        [TrivRules]
% 11.69/1.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.69/1.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.69/1.97  --sup_immed_bw_main                     []
% 11.69/1.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.69/1.97  --sup_input_triv                        [Unflattening;TrivRules]
% 11.69/1.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.69/1.97  --sup_input_bw                          []
% 11.69/1.97  
% 11.69/1.97  ------ Combination Options
% 11.69/1.97  
% 11.69/1.97  --comb_res_mult                         3
% 11.69/1.97  --comb_sup_mult                         2
% 11.69/1.97  --comb_inst_mult                        10
% 11.69/1.97  
% 11.69/1.97  ------ Debug Options
% 11.69/1.97  
% 11.69/1.97  --dbg_backtrace                         false
% 11.69/1.97  --dbg_dump_prop_clauses                 false
% 11.69/1.97  --dbg_dump_prop_clauses_file            -
% 11.69/1.97  --dbg_out_stat                          false
% 11.69/1.97  ------ Parsing...
% 11.69/1.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.69/1.97  
% 11.69/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.69/1.97  
% 11.69/1.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.69/1.97  
% 11.69/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.69/1.97  ------ Proving...
% 11.69/1.97  ------ Problem Properties 
% 11.69/1.97  
% 11.69/1.97  
% 11.69/1.97  clauses                                 37
% 11.69/1.97  conjectures                             11
% 11.69/1.97  EPR                                     7
% 11.69/1.97  Horn                                    33
% 11.69/1.97  unary                                   13
% 11.69/1.97  binary                                  9
% 11.69/1.97  lits                                    128
% 11.69/1.97  lits eq                                 30
% 11.69/1.97  fd_pure                                 0
% 11.69/1.97  fd_pseudo                               0
% 11.69/1.97  fd_cond                                 4
% 11.69/1.97  fd_pseudo_cond                          0
% 11.69/1.97  AC symbols                              0
% 11.69/1.97  
% 11.69/1.97  ------ Schedule dynamic 5 is on 
% 11.69/1.97  
% 11.69/1.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.69/1.97  
% 11.69/1.97  
% 11.69/1.97  ------ 
% 11.69/1.97  Current options:
% 11.69/1.97  ------ 
% 11.69/1.97  
% 11.69/1.97  ------ Input Options
% 11.69/1.97  
% 11.69/1.97  --out_options                           all
% 11.69/1.97  --tptp_safe_out                         true
% 11.69/1.97  --problem_path                          ""
% 11.69/1.97  --include_path                          ""
% 11.69/1.97  --clausifier                            res/vclausify_rel
% 11.69/1.97  --clausifier_options                    ""
% 11.69/1.97  --stdin                                 false
% 11.69/1.97  --stats_out                             all
% 11.69/1.97  
% 11.69/1.97  ------ General Options
% 11.69/1.97  
% 11.69/1.97  --fof                                   false
% 11.69/1.97  --time_out_real                         305.
% 11.69/1.97  --time_out_virtual                      -1.
% 11.69/1.97  --symbol_type_check                     false
% 11.69/1.97  --clausify_out                          false
% 11.69/1.97  --sig_cnt_out                           false
% 11.69/1.97  --trig_cnt_out                          false
% 11.69/1.97  --trig_cnt_out_tolerance                1.
% 11.69/1.97  --trig_cnt_out_sk_spl                   false
% 11.69/1.97  --abstr_cl_out                          false
% 11.69/1.97  
% 11.69/1.97  ------ Global Options
% 11.69/1.97  
% 11.69/1.97  --schedule                              default
% 11.69/1.97  --add_important_lit                     false
% 11.69/1.97  --prop_solver_per_cl                    1000
% 11.69/1.97  --min_unsat_core                        false
% 11.69/1.97  --soft_assumptions                      false
% 11.69/1.97  --soft_lemma_size                       3
% 11.69/1.97  --prop_impl_unit_size                   0
% 11.69/1.97  --prop_impl_unit                        []
% 11.69/1.97  --share_sel_clauses                     true
% 11.69/1.97  --reset_solvers                         false
% 11.69/1.97  --bc_imp_inh                            [conj_cone]
% 11.69/1.97  --conj_cone_tolerance                   3.
% 11.69/1.97  --extra_neg_conj                        none
% 11.69/1.97  --large_theory_mode                     true
% 11.69/1.97  --prolific_symb_bound                   200
% 11.69/1.97  --lt_threshold                          2000
% 11.69/1.97  --clause_weak_htbl                      true
% 11.69/1.97  --gc_record_bc_elim                     false
% 11.69/1.97  
% 11.69/1.97  ------ Preprocessing Options
% 11.69/1.97  
% 11.69/1.97  --preprocessing_flag                    true
% 11.69/1.97  --time_out_prep_mult                    0.1
% 11.69/1.97  --splitting_mode                        input
% 11.69/1.97  --splitting_grd                         true
% 11.69/1.97  --splitting_cvd                         false
% 11.69/1.97  --splitting_cvd_svl                     false
% 11.69/1.97  --splitting_nvd                         32
% 11.69/1.97  --sub_typing                            true
% 11.69/1.97  --prep_gs_sim                           true
% 11.69/1.97  --prep_unflatten                        true
% 11.69/1.97  --prep_res_sim                          true
% 11.69/1.97  --prep_upred                            true
% 11.69/1.97  --prep_sem_filter                       exhaustive
% 11.69/1.97  --prep_sem_filter_out                   false
% 11.69/1.97  --pred_elim                             true
% 11.69/1.97  --res_sim_input                         true
% 11.69/1.97  --eq_ax_congr_red                       true
% 11.69/1.97  --pure_diseq_elim                       true
% 11.69/1.97  --brand_transform                       false
% 11.69/1.98  --non_eq_to_eq                          false
% 11.69/1.98  --prep_def_merge                        true
% 11.69/1.98  --prep_def_merge_prop_impl              false
% 11.69/1.98  --prep_def_merge_mbd                    true
% 11.69/1.98  --prep_def_merge_tr_red                 false
% 11.69/1.98  --prep_def_merge_tr_cl                  false
% 11.69/1.98  --smt_preprocessing                     true
% 11.69/1.98  --smt_ac_axioms                         fast
% 11.69/1.98  --preprocessed_out                      false
% 11.69/1.98  --preprocessed_stats                    false
% 11.69/1.98  
% 11.69/1.98  ------ Abstraction refinement Options
% 11.69/1.98  
% 11.69/1.98  --abstr_ref                             []
% 11.69/1.98  --abstr_ref_prep                        false
% 11.69/1.98  --abstr_ref_until_sat                   false
% 11.69/1.98  --abstr_ref_sig_restrict                funpre
% 11.69/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.69/1.98  --abstr_ref_under                       []
% 11.69/1.98  
% 11.69/1.98  ------ SAT Options
% 11.69/1.98  
% 11.69/1.98  --sat_mode                              false
% 11.69/1.98  --sat_fm_restart_options                ""
% 11.69/1.98  --sat_gr_def                            false
% 11.69/1.98  --sat_epr_types                         true
% 11.69/1.98  --sat_non_cyclic_types                  false
% 11.69/1.98  --sat_finite_models                     false
% 11.69/1.98  --sat_fm_lemmas                         false
% 11.69/1.98  --sat_fm_prep                           false
% 11.69/1.98  --sat_fm_uc_incr                        true
% 11.69/1.98  --sat_out_model                         small
% 11.69/1.98  --sat_out_clauses                       false
% 11.69/1.98  
% 11.69/1.98  ------ QBF Options
% 11.69/1.98  
% 11.69/1.98  --qbf_mode                              false
% 11.69/1.98  --qbf_elim_univ                         false
% 11.69/1.98  --qbf_dom_inst                          none
% 11.69/1.98  --qbf_dom_pre_inst                      false
% 11.69/1.98  --qbf_sk_in                             false
% 11.69/1.98  --qbf_pred_elim                         true
% 11.69/1.98  --qbf_split                             512
% 11.69/1.98  
% 11.69/1.98  ------ BMC1 Options
% 11.69/1.98  
% 11.69/1.98  --bmc1_incremental                      false
% 11.69/1.98  --bmc1_axioms                           reachable_all
% 11.69/1.98  --bmc1_min_bound                        0
% 11.69/1.98  --bmc1_max_bound                        -1
% 11.69/1.98  --bmc1_max_bound_default                -1
% 11.69/1.98  --bmc1_symbol_reachability              true
% 11.69/1.98  --bmc1_property_lemmas                  false
% 11.69/1.98  --bmc1_k_induction                      false
% 11.69/1.98  --bmc1_non_equiv_states                 false
% 11.69/1.98  --bmc1_deadlock                         false
% 11.69/1.98  --bmc1_ucm                              false
% 11.69/1.98  --bmc1_add_unsat_core                   none
% 11.69/1.98  --bmc1_unsat_core_children              false
% 11.69/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.69/1.98  --bmc1_out_stat                         full
% 11.69/1.98  --bmc1_ground_init                      false
% 11.69/1.98  --bmc1_pre_inst_next_state              false
% 11.69/1.98  --bmc1_pre_inst_state                   false
% 11.69/1.98  --bmc1_pre_inst_reach_state             false
% 11.69/1.98  --bmc1_out_unsat_core                   false
% 11.69/1.98  --bmc1_aig_witness_out                  false
% 11.69/1.98  --bmc1_verbose                          false
% 11.69/1.98  --bmc1_dump_clauses_tptp                false
% 11.69/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.69/1.98  --bmc1_dump_file                        -
% 11.69/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.69/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.69/1.98  --bmc1_ucm_extend_mode                  1
% 11.69/1.98  --bmc1_ucm_init_mode                    2
% 11.69/1.98  --bmc1_ucm_cone_mode                    none
% 11.69/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.69/1.98  --bmc1_ucm_relax_model                  4
% 11.69/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.69/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.69/1.98  --bmc1_ucm_layered_model                none
% 11.69/1.98  --bmc1_ucm_max_lemma_size               10
% 11.69/1.98  
% 11.69/1.98  ------ AIG Options
% 11.69/1.98  
% 11.69/1.98  --aig_mode                              false
% 11.69/1.98  
% 11.69/1.98  ------ Instantiation Options
% 11.69/1.98  
% 11.69/1.98  --instantiation_flag                    true
% 11.69/1.98  --inst_sos_flag                         true
% 11.69/1.98  --inst_sos_phase                        true
% 11.69/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.69/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.69/1.98  --inst_lit_sel_side                     none
% 11.69/1.98  --inst_solver_per_active                1400
% 11.69/1.98  --inst_solver_calls_frac                1.
% 11.69/1.98  --inst_passive_queue_type               priority_queues
% 11.69/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.69/1.98  --inst_passive_queues_freq              [25;2]
% 11.69/1.98  --inst_dismatching                      true
% 11.69/1.98  --inst_eager_unprocessed_to_passive     true
% 11.69/1.98  --inst_prop_sim_given                   true
% 11.69/1.98  --inst_prop_sim_new                     false
% 11.69/1.98  --inst_subs_new                         false
% 11.69/1.98  --inst_eq_res_simp                      false
% 11.69/1.98  --inst_subs_given                       false
% 11.69/1.98  --inst_orphan_elimination               true
% 11.69/1.98  --inst_learning_loop_flag               true
% 11.69/1.98  --inst_learning_start                   3000
% 11.69/1.98  --inst_learning_factor                  2
% 11.69/1.98  --inst_start_prop_sim_after_learn       3
% 11.69/1.98  --inst_sel_renew                        solver
% 11.69/1.98  --inst_lit_activity_flag                true
% 11.69/1.98  --inst_restr_to_given                   false
% 11.69/1.98  --inst_activity_threshold               500
% 11.69/1.98  --inst_out_proof                        true
% 11.69/1.98  
% 11.69/1.98  ------ Resolution Options
% 11.69/1.98  
% 11.69/1.98  --resolution_flag                       false
% 11.69/1.98  --res_lit_sel                           adaptive
% 11.69/1.98  --res_lit_sel_side                      none
% 11.69/1.98  --res_ordering                          kbo
% 11.69/1.98  --res_to_prop_solver                    active
% 11.69/1.98  --res_prop_simpl_new                    false
% 11.69/1.98  --res_prop_simpl_given                  true
% 11.69/1.98  --res_passive_queue_type                priority_queues
% 11.69/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.69/1.98  --res_passive_queues_freq               [15;5]
% 11.69/1.98  --res_forward_subs                      full
% 11.69/1.98  --res_backward_subs                     full
% 11.69/1.98  --res_forward_subs_resolution           true
% 11.69/1.98  --res_backward_subs_resolution          true
% 11.69/1.98  --res_orphan_elimination                true
% 11.69/1.98  --res_time_limit                        2.
% 11.69/1.98  --res_out_proof                         true
% 11.69/1.98  
% 11.69/1.98  ------ Superposition Options
% 11.69/1.98  
% 11.69/1.98  --superposition_flag                    true
% 11.69/1.98  --sup_passive_queue_type                priority_queues
% 11.69/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.69/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.69/1.98  --demod_completeness_check              fast
% 11.69/1.98  --demod_use_ground                      true
% 11.69/1.98  --sup_to_prop_solver                    passive
% 11.69/1.98  --sup_prop_simpl_new                    true
% 11.69/1.98  --sup_prop_simpl_given                  true
% 11.69/1.98  --sup_fun_splitting                     true
% 11.69/1.98  --sup_smt_interval                      50000
% 11.69/1.98  
% 11.69/1.98  ------ Superposition Simplification Setup
% 11.69/1.98  
% 11.69/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.69/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.69/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.69/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.69/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.69/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.69/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.69/1.98  --sup_immed_triv                        [TrivRules]
% 11.69/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.69/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.69/1.98  --sup_immed_bw_main                     []
% 11.69/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.69/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.69/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.69/1.98  --sup_input_bw                          []
% 11.69/1.98  
% 11.69/1.98  ------ Combination Options
% 11.69/1.98  
% 11.69/1.98  --comb_res_mult                         3
% 11.69/1.98  --comb_sup_mult                         2
% 11.69/1.98  --comb_inst_mult                        10
% 11.69/1.98  
% 11.69/1.98  ------ Debug Options
% 11.69/1.98  
% 11.69/1.98  --dbg_backtrace                         false
% 11.69/1.98  --dbg_dump_prop_clauses                 false
% 11.69/1.98  --dbg_dump_prop_clauses_file            -
% 11.69/1.98  --dbg_out_stat                          false
% 11.69/1.98  
% 11.69/1.98  
% 11.69/1.98  
% 11.69/1.98  
% 11.69/1.98  ------ Proving...
% 11.69/1.98  
% 11.69/1.98  
% 11.69/1.98  % SZS status Theorem for theBenchmark.p
% 11.69/1.98  
% 11.69/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.69/1.98  
% 11.69/1.98  fof(f12,axiom,(
% 11.69/1.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f35,plain,(
% 11.69/1.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.69/1.98    inference(ennf_transformation,[],[f12])).
% 11.69/1.98  
% 11.69/1.98  fof(f36,plain,(
% 11.69/1.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.69/1.98    inference(flattening,[],[f35])).
% 11.69/1.98  
% 11.69/1.98  fof(f49,plain,(
% 11.69/1.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.69/1.98    inference(nnf_transformation,[],[f36])).
% 11.69/1.98  
% 11.69/1.98  fof(f66,plain,(
% 11.69/1.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.69/1.98    inference(cnf_transformation,[],[f49])).
% 11.69/1.98  
% 11.69/1.98  fof(f20,conjecture,(
% 11.69/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f21,negated_conjecture,(
% 11.69/1.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.69/1.98    inference(negated_conjecture,[],[f20])).
% 11.69/1.98  
% 11.69/1.98  fof(f47,plain,(
% 11.69/1.98    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.69/1.98    inference(ennf_transformation,[],[f21])).
% 11.69/1.98  
% 11.69/1.98  fof(f48,plain,(
% 11.69/1.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.69/1.98    inference(flattening,[],[f47])).
% 11.69/1.98  
% 11.69/1.98  fof(f51,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 11.69/1.98    introduced(choice_axiom,[])).
% 11.69/1.98  
% 11.69/1.98  fof(f50,plain,(
% 11.69/1.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 11.69/1.98    introduced(choice_axiom,[])).
% 11.69/1.98  
% 11.69/1.98  fof(f52,plain,(
% 11.69/1.98    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 11.69/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f51,f50])).
% 11.69/1.98  
% 11.69/1.98  fof(f87,plain,(
% 11.69/1.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 11.69/1.98    inference(cnf_transformation,[],[f52])).
% 11.69/1.98  
% 11.69/1.98  fof(f14,axiom,(
% 11.69/1.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f22,plain,(
% 11.69/1.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.69/1.98    inference(pure_predicate_removal,[],[f14])).
% 11.69/1.98  
% 11.69/1.98  fof(f70,plain,(
% 11.69/1.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.69/1.98    inference(cnf_transformation,[],[f22])).
% 11.69/1.98  
% 11.69/1.98  fof(f80,plain,(
% 11.69/1.98    v1_funct_1(sK2)),
% 11.69/1.98    inference(cnf_transformation,[],[f52])).
% 11.69/1.98  
% 11.69/1.98  fof(f82,plain,(
% 11.69/1.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.69/1.98    inference(cnf_transformation,[],[f52])).
% 11.69/1.98  
% 11.69/1.98  fof(f83,plain,(
% 11.69/1.98    v1_funct_1(sK3)),
% 11.69/1.98    inference(cnf_transformation,[],[f52])).
% 11.69/1.98  
% 11.69/1.98  fof(f85,plain,(
% 11.69/1.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.69/1.98    inference(cnf_transformation,[],[f52])).
% 11.69/1.98  
% 11.69/1.98  fof(f13,axiom,(
% 11.69/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f37,plain,(
% 11.69/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.69/1.98    inference(ennf_transformation,[],[f13])).
% 11.69/1.98  
% 11.69/1.98  fof(f38,plain,(
% 11.69/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.69/1.98    inference(flattening,[],[f37])).
% 11.69/1.98  
% 11.69/1.98  fof(f69,plain,(
% 11.69/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f38])).
% 11.69/1.98  
% 11.69/1.98  fof(f17,axiom,(
% 11.69/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f41,plain,(
% 11.69/1.98    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.69/1.98    inference(ennf_transformation,[],[f17])).
% 11.69/1.98  
% 11.69/1.98  fof(f42,plain,(
% 11.69/1.98    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.69/1.98    inference(flattening,[],[f41])).
% 11.69/1.98  
% 11.69/1.98  fof(f73,plain,(
% 11.69/1.98    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f42])).
% 11.69/1.98  
% 11.69/1.98  fof(f81,plain,(
% 11.69/1.98    v1_funct_2(sK2,sK0,sK1)),
% 11.69/1.98    inference(cnf_transformation,[],[f52])).
% 11.69/1.98  
% 11.69/1.98  fof(f84,plain,(
% 11.69/1.98    v1_funct_2(sK3,sK1,sK0)),
% 11.69/1.98    inference(cnf_transformation,[],[f52])).
% 11.69/1.98  
% 11.69/1.98  fof(f19,axiom,(
% 11.69/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f45,plain,(
% 11.69/1.98    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.69/1.98    inference(ennf_transformation,[],[f19])).
% 11.69/1.98  
% 11.69/1.98  fof(f46,plain,(
% 11.69/1.98    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.69/1.98    inference(flattening,[],[f45])).
% 11.69/1.98  
% 11.69/1.98  fof(f78,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f46])).
% 11.69/1.98  
% 11.69/1.98  fof(f89,plain,(
% 11.69/1.98    k1_xboole_0 != sK0),
% 11.69/1.98    inference(cnf_transformation,[],[f52])).
% 11.69/1.98  
% 11.69/1.98  fof(f86,plain,(
% 11.69/1.98    k2_relset_1(sK0,sK1,sK2) = sK1),
% 11.69/1.98    inference(cnf_transformation,[],[f52])).
% 11.69/1.98  
% 11.69/1.98  fof(f18,axiom,(
% 11.69/1.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f43,plain,(
% 11.69/1.98    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.69/1.98    inference(ennf_transformation,[],[f18])).
% 11.69/1.98  
% 11.69/1.98  fof(f44,plain,(
% 11.69/1.98    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.69/1.98    inference(flattening,[],[f43])).
% 11.69/1.98  
% 11.69/1.98  fof(f76,plain,(
% 11.69/1.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f44])).
% 11.69/1.98  
% 11.69/1.98  fof(f9,axiom,(
% 11.69/1.98    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f63,plain,(
% 11.69/1.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.69/1.98    inference(cnf_transformation,[],[f9])).
% 11.69/1.98  
% 11.69/1.98  fof(f16,axiom,(
% 11.69/1.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f72,plain,(
% 11.69/1.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f16])).
% 11.69/1.98  
% 11.69/1.98  fof(f94,plain,(
% 11.69/1.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 11.69/1.98    inference(definition_unfolding,[],[f63,f72])).
% 11.69/1.98  
% 11.69/1.98  fof(f7,axiom,(
% 11.69/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f29,plain,(
% 11.69/1.98    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.69/1.98    inference(ennf_transformation,[],[f7])).
% 11.69/1.98  
% 11.69/1.98  fof(f30,plain,(
% 11.69/1.98    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.69/1.98    inference(flattening,[],[f29])).
% 11.69/1.98  
% 11.69/1.98  fof(f60,plain,(
% 11.69/1.98    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f30])).
% 11.69/1.98  
% 11.69/1.98  fof(f10,axiom,(
% 11.69/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f33,plain,(
% 11.69/1.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.69/1.98    inference(ennf_transformation,[],[f10])).
% 11.69/1.98  
% 11.69/1.98  fof(f64,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.69/1.98    inference(cnf_transformation,[],[f33])).
% 11.69/1.98  
% 11.69/1.98  fof(f1,axiom,(
% 11.69/1.98    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f23,plain,(
% 11.69/1.98    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 11.69/1.98    inference(ennf_transformation,[],[f1])).
% 11.69/1.98  
% 11.69/1.98  fof(f53,plain,(
% 11.69/1.98    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f23])).
% 11.69/1.98  
% 11.69/1.98  fof(f3,axiom,(
% 11.69/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f25,plain,(
% 11.69/1.98    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.69/1.98    inference(ennf_transformation,[],[f3])).
% 11.69/1.98  
% 11.69/1.98  fof(f56,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f25])).
% 11.69/1.98  
% 11.69/1.98  fof(f15,axiom,(
% 11.69/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f39,plain,(
% 11.69/1.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.69/1.98    inference(ennf_transformation,[],[f15])).
% 11.69/1.98  
% 11.69/1.98  fof(f40,plain,(
% 11.69/1.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.69/1.98    inference(flattening,[],[f39])).
% 11.69/1.98  
% 11.69/1.98  fof(f71,plain,(
% 11.69/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f40])).
% 11.69/1.98  
% 11.69/1.98  fof(f5,axiom,(
% 11.69/1.98    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f27,plain,(
% 11.69/1.98    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.69/1.98    inference(ennf_transformation,[],[f5])).
% 11.69/1.98  
% 11.69/1.98  fof(f58,plain,(
% 11.69/1.98    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f27])).
% 11.69/1.98  
% 11.69/1.98  fof(f93,plain,(
% 11.69/1.98    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.69/1.98    inference(definition_unfolding,[],[f58,f72])).
% 11.69/1.98  
% 11.69/1.98  fof(f8,axiom,(
% 11.69/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f31,plain,(
% 11.69/1.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.69/1.98    inference(ennf_transformation,[],[f8])).
% 11.69/1.98  
% 11.69/1.98  fof(f32,plain,(
% 11.69/1.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.69/1.98    inference(flattening,[],[f31])).
% 11.69/1.98  
% 11.69/1.98  fof(f61,plain,(
% 11.69/1.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f32])).
% 11.69/1.98  
% 11.69/1.98  fof(f6,axiom,(
% 11.69/1.98    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f28,plain,(
% 11.69/1.98    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 11.69/1.98    inference(ennf_transformation,[],[f6])).
% 11.69/1.98  
% 11.69/1.98  fof(f59,plain,(
% 11.69/1.98    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f28])).
% 11.69/1.98  
% 11.69/1.98  fof(f2,axiom,(
% 11.69/1.98    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f24,plain,(
% 11.69/1.98    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 11.69/1.98    inference(ennf_transformation,[],[f2])).
% 11.69/1.98  
% 11.69/1.98  fof(f54,plain,(
% 11.69/1.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f24])).
% 11.69/1.98  
% 11.69/1.98  fof(f11,axiom,(
% 11.69/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f34,plain,(
% 11.69/1.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.69/1.98    inference(ennf_transformation,[],[f11])).
% 11.69/1.98  
% 11.69/1.98  fof(f65,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.69/1.98    inference(cnf_transformation,[],[f34])).
% 11.69/1.98  
% 11.69/1.98  fof(f4,axiom,(
% 11.69/1.98    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 11.69/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f26,plain,(
% 11.69/1.98    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 11.69/1.98    inference(ennf_transformation,[],[f4])).
% 11.69/1.98  
% 11.69/1.98  fof(f57,plain,(
% 11.69/1.98    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f26])).
% 11.69/1.98  
% 11.69/1.98  fof(f92,plain,(
% 11.69/1.98    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 11.69/1.98    inference(definition_unfolding,[],[f57,f72])).
% 11.69/1.98  
% 11.69/1.98  fof(f55,plain,(
% 11.69/1.98    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f24])).
% 11.69/1.98  
% 11.69/1.98  fof(f88,plain,(
% 11.69/1.98    v2_funct_1(sK2)),
% 11.69/1.98    inference(cnf_transformation,[],[f52])).
% 11.69/1.98  
% 11.69/1.98  fof(f79,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f46])).
% 11.69/1.98  
% 11.69/1.98  fof(f90,plain,(
% 11.69/1.98    k1_xboole_0 != sK1),
% 11.69/1.98    inference(cnf_transformation,[],[f52])).
% 11.69/1.98  
% 11.69/1.98  fof(f91,plain,(
% 11.69/1.98    k2_funct_1(sK2) != sK3),
% 11.69/1.98    inference(cnf_transformation,[],[f52])).
% 11.69/1.98  
% 11.69/1.98  cnf(c_14,plain,
% 11.69/1.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.69/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.69/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.69/1.98      | X3 = X2 ),
% 11.69/1.98      inference(cnf_transformation,[],[f66]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_30,negated_conjecture,
% 11.69/1.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 11.69/1.98      inference(cnf_transformation,[],[f87]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_423,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.69/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.69/1.98      | X3 = X0
% 11.69/1.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 11.69/1.98      | k6_partfun1(sK0) != X3
% 11.69/1.98      | sK0 != X2
% 11.69/1.98      | sK0 != X1 ),
% 11.69/1.98      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_424,plain,
% 11.69/1.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.69/1.98      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.69/1.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.69/1.98      inference(unflattening,[status(thm)],[c_423]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_17,plain,
% 11.69/1.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.69/1.98      inference(cnf_transformation,[],[f70]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_432,plain,
% 11.69/1.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.69/1.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.69/1.98      inference(forward_subsumption_resolution,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_424,c_17]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_720,plain,
% 11.69/1.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.69/1.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_432]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1379,plain,
% 11.69/1.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.69/1.98      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_37,negated_conjecture,
% 11.69/1.98      ( v1_funct_1(sK2) ),
% 11.69/1.98      inference(cnf_transformation,[],[f80]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_35,negated_conjecture,
% 11.69/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.69/1.98      inference(cnf_transformation,[],[f82]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_34,negated_conjecture,
% 11.69/1.98      ( v1_funct_1(sK3) ),
% 11.69/1.98      inference(cnf_transformation,[],[f83]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_32,negated_conjecture,
% 11.69/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.69/1.98      inference(cnf_transformation,[],[f85]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.69/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.69/1.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.69/1.98      | ~ v1_funct_1(X0)
% 11.69/1.98      | ~ v1_funct_1(X3) ),
% 11.69/1.98      inference(cnf_transformation,[],[f69]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_742,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.69/1.98      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 11.69/1.98      | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 11.69/1.98      | ~ v1_funct_1(X0_50)
% 11.69/1.98      | ~ v1_funct_1(X1_50) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_15]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1449,plain,
% 11.69/1.98      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.69/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.69/1.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.69/1.98      | ~ v1_funct_1(sK3)
% 11.69/1.98      | ~ v1_funct_1(sK2) ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_742]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1738,plain,
% 11.69/1.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_1379,c_37,c_35,c_34,c_32,c_720,c_1449]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_19,plain,
% 11.69/1.98      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.69/1.98      | ~ v1_funct_2(X2,X0,X1)
% 11.69/1.98      | ~ v1_funct_2(X3,X1,X0)
% 11.69/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.69/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.69/1.98      | ~ v1_funct_1(X2)
% 11.69/1.98      | ~ v1_funct_1(X3)
% 11.69/1.98      | k2_relset_1(X1,X0,X3) = X0 ),
% 11.69/1.98      inference(cnf_transformation,[],[f73]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_436,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 11.69/1.98      | ~ v1_funct_2(X3,X2,X1)
% 11.69/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.69/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.69/1.98      | ~ v1_funct_1(X0)
% 11.69/1.98      | ~ v1_funct_1(X3)
% 11.69/1.98      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.69/1.98      | k2_relset_1(X1,X2,X0) = X2
% 11.69/1.98      | k6_partfun1(X2) != k6_partfun1(sK0)
% 11.69/1.98      | sK0 != X2 ),
% 11.69/1.98      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_437,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0,X1,sK0)
% 11.69/1.98      | ~ v1_funct_2(X2,sK0,X1)
% 11.69/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 11.69/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 11.69/1.98      | ~ v1_funct_1(X0)
% 11.69/1.98      | ~ v1_funct_1(X2)
% 11.69/1.98      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.69/1.98      | k2_relset_1(X1,sK0,X0) = sK0
% 11.69/1.98      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 11.69/1.98      inference(unflattening,[status(thm)],[c_436]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_524,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0,X1,sK0)
% 11.69/1.98      | ~ v1_funct_2(X2,sK0,X1)
% 11.69/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 11.69/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 11.69/1.98      | ~ v1_funct_1(X0)
% 11.69/1.98      | ~ v1_funct_1(X2)
% 11.69/1.98      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.69/1.98      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 11.69/1.98      inference(equality_resolution_simp,[status(thm)],[c_437]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_719,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0_50,X0_51,sK0)
% 11.69/1.98      | ~ v1_funct_2(X1_50,sK0,X0_51)
% 11.69/1.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
% 11.69/1.98      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
% 11.69/1.98      | ~ v1_funct_1(X0_50)
% 11.69/1.98      | ~ v1_funct_1(X1_50)
% 11.69/1.98      | k2_relset_1(X0_51,sK0,X0_50) = sK0
% 11.69/1.98      | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_524]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1380,plain,
% 11.69/1.98      ( k2_relset_1(X0_51,sK0,X0_50) = sK0
% 11.69/1.98      | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.69/1.98      | v1_funct_2(X0_50,X0_51,sK0) != iProver_top
% 11.69/1.98      | v1_funct_2(X1_50,sK0,X0_51) != iProver_top
% 11.69/1.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top
% 11.69/1.98      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
% 11.69/1.98      | v1_funct_1(X1_50) != iProver_top
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1831,plain,
% 11.69/1.98      ( k2_relset_1(X0_51,sK0,X0_50) = sK0
% 11.69/1.98      | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k6_partfun1(sK0)
% 11.69/1.98      | v1_funct_2(X0_50,X0_51,sK0) != iProver_top
% 11.69/1.98      | v1_funct_2(X1_50,sK0,X0_51) != iProver_top
% 11.69/1.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top
% 11.69/1.98      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
% 11.69/1.98      | v1_funct_1(X1_50) != iProver_top
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_1380,c_1738]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1835,plain,
% 11.69/1.98      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 11.69/1.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.69/1.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.69/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.69/1.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.69/1.98      | v1_funct_1(sK3) != iProver_top
% 11.69/1.98      | v1_funct_1(sK2) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1738,c_1831]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_36,negated_conjecture,
% 11.69/1.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 11.69/1.98      inference(cnf_transformation,[],[f81]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_33,negated_conjecture,
% 11.69/1.98      ( v1_funct_2(sK3,sK1,sK0) ),
% 11.69/1.98      inference(cnf_transformation,[],[f84]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1457,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0_50,sK0,sK1)
% 11.69/1.98      | ~ v1_funct_2(sK3,sK1,sK0)
% 11.69/1.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.69/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.69/1.98      | ~ v1_funct_1(X0_50)
% 11.69/1.98      | ~ v1_funct_1(sK3)
% 11.69/1.98      | k2_relset_1(sK1,sK0,sK3) = sK0
% 11.69/1.98      | k1_partfun1(sK0,sK1,sK1,sK0,X0_50,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_719]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1459,plain,
% 11.69/1.98      ( ~ v1_funct_2(sK3,sK1,sK0)
% 11.69/1.98      | ~ v1_funct_2(sK2,sK0,sK1)
% 11.69/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.69/1.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.69/1.98      | ~ v1_funct_1(sK3)
% 11.69/1.98      | ~ v1_funct_1(sK2)
% 11.69/1.98      | k2_relset_1(sK1,sK0,sK3) = sK0
% 11.69/1.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_1457]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_757,plain,( X0_50 = X0_50 ),theory(equality) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1501,plain,
% 11.69/1.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_757]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1838,plain,
% 11.69/1.98      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_1835,c_37,c_36,c_35,c_34,c_33,c_32,c_1459,c_1501]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_25,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 11.69/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.69/1.98      | ~ v1_funct_1(X0)
% 11.69/1.98      | ~ v2_funct_1(X0)
% 11.69/1.98      | k2_relset_1(X1,X2,X0) != X2
% 11.69/1.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.69/1.98      | k1_xboole_0 = X2 ),
% 11.69/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_733,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 11.69/1.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.69/1.98      | ~ v1_funct_1(X0_50)
% 11.69/1.98      | ~ v2_funct_1(X0_50)
% 11.69/1.98      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 11.69/1.98      | k1_xboole_0 = X1_51
% 11.69/1.98      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_25]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1370,plain,
% 11.69/1.98      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 11.69/1.98      | k1_xboole_0 = X1_51
% 11.69/1.98      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51)
% 11.69/1.98      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 11.69/1.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v2_funct_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3486,plain,
% 11.69/1.98      ( sK0 = k1_xboole_0
% 11.69/1.98      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 11.69/1.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.69/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.69/1.98      | v1_funct_1(sK3) != iProver_top
% 11.69/1.98      | v2_funct_1(sK3) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1838,c_1370]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_28,negated_conjecture,
% 11.69/1.98      ( k1_xboole_0 != sK0 ),
% 11.69/1.98      inference(cnf_transformation,[],[f89]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_730,negated_conjecture,
% 11.69/1.98      ( k1_xboole_0 != sK0 ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_28]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_31,negated_conjecture,
% 11.69/1.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 11.69/1.98      inference(cnf_transformation,[],[f86]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_728,negated_conjecture,
% 11.69/1.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_31]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1423,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0_50,X0_51,sK0)
% 11.69/1.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
% 11.69/1.98      | ~ v1_funct_1(X0_50)
% 11.69/1.98      | ~ v2_funct_1(X0_50)
% 11.69/1.98      | k2_relset_1(X0_51,sK0,X0_50) != sK0
% 11.69/1.98      | k1_xboole_0 = sK0
% 11.69/1.98      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51) ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_733]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1493,plain,
% 11.69/1.98      ( ~ v1_funct_2(sK3,sK1,sK0)
% 11.69/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.69/1.98      | ~ v1_funct_1(sK3)
% 11.69/1.98      | ~ v2_funct_1(sK3)
% 11.69/1.98      | k2_relset_1(sK1,sK0,sK3) != sK0
% 11.69/1.98      | k1_xboole_0 = sK0
% 11.69/1.98      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_1423]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_761,plain,
% 11.69/1.98      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 11.69/1.98      theory(equality) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1515,plain,
% 11.69/1.98      ( X0_50 != X1_50
% 11.69/1.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_50
% 11.69/1.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_50 ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_761]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1570,plain,
% 11.69/1.98      ( X0_50 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.69/1.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_50
% 11.69/1.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_1515]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1715,plain,
% 11.69/1.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.69/1.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 11.69/1.98      | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_1570]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_21,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 11.69/1.98      | ~ v1_funct_2(X3,X4,X1)
% 11.69/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 11.69/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.69/1.98      | ~ v1_funct_1(X0)
% 11.69/1.98      | ~ v1_funct_1(X3)
% 11.69/1.98      | v2_funct_1(X0)
% 11.69/1.98      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 11.69/1.98      | k2_relset_1(X4,X1,X3) != X1
% 11.69/1.98      | k1_xboole_0 = X2 ),
% 11.69/1.98      inference(cnf_transformation,[],[f76]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_737,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 11.69/1.98      | ~ v1_funct_2(X1_50,X2_51,X0_51)
% 11.69/1.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.69/1.98      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X0_51)))
% 11.69/1.98      | ~ v1_funct_1(X0_50)
% 11.69/1.98      | ~ v1_funct_1(X1_50)
% 11.69/1.98      | v2_funct_1(X0_50)
% 11.69/1.98      | ~ v2_funct_1(k1_partfun1(X2_51,X0_51,X0_51,X1_51,X1_50,X0_50))
% 11.69/1.98      | k2_relset_1(X2_51,X0_51,X1_50) != X0_51
% 11.69/1.98      | k1_xboole_0 = X1_51 ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_21]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1523,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 11.69/1.98      | ~ v1_funct_2(sK3,X1_51,X2_51)
% 11.69/1.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.69/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 11.69/1.98      | ~ v1_funct_1(X0_50)
% 11.69/1.98      | ~ v1_funct_1(sK3)
% 11.69/1.98      | ~ v2_funct_1(k1_partfun1(X0_51,X1_51,X1_51,X2_51,X0_50,sK3))
% 11.69/1.98      | v2_funct_1(sK3)
% 11.69/1.98      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 11.69/1.98      | k1_xboole_0 = X2_51 ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_737]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1678,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 11.69/1.98      | ~ v1_funct_2(sK3,X1_51,sK0)
% 11.69/1.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.69/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK0)))
% 11.69/1.98      | ~ v1_funct_1(X0_50)
% 11.69/1.98      | ~ v1_funct_1(sK3)
% 11.69/1.98      | ~ v2_funct_1(k1_partfun1(X0_51,X1_51,X1_51,sK0,X0_50,sK3))
% 11.69/1.98      | v2_funct_1(sK3)
% 11.69/1.98      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 11.69/1.98      | k1_xboole_0 = sK0 ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_1523]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1792,plain,
% 11.69/1.98      ( ~ v1_funct_2(sK3,sK1,sK0)
% 11.69/1.98      | ~ v1_funct_2(sK2,sK0,sK1)
% 11.69/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.69/1.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.69/1.98      | ~ v1_funct_1(sK3)
% 11.69/1.98      | ~ v1_funct_1(sK2)
% 11.69/1.98      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 11.69/1.98      | v2_funct_1(sK3)
% 11.69/1.98      | k2_relset_1(sK0,sK1,sK2) != sK1
% 11.69/1.98      | k1_xboole_0 = sK0 ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_1678]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_770,plain,
% 11.69/1.98      ( ~ v2_funct_1(X0_50) | v2_funct_1(X1_50) | X1_50 != X0_50 ),
% 11.69/1.98      theory(equality) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1952,plain,
% 11.69/1.98      ( ~ v2_funct_1(X0_50)
% 11.69/1.98      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 11.69/1.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0_50 ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_770]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2409,plain,
% 11.69/1.98      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 11.69/1.98      | ~ v2_funct_1(k6_partfun1(sK0))
% 11.69/1.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0) ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_1952]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_10,plain,
% 11.69/1.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 11.69/1.98      inference(cnf_transformation,[],[f94]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_745,plain,
% 11.69/1.98      ( v2_funct_1(k6_partfun1(X0_51)) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_10]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3042,plain,
% 11.69/1.98      ( v2_funct_1(k6_partfun1(sK0)) ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_745]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_21346,plain,
% 11.69/1.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_3486,c_37,c_36,c_35,c_34,c_33,c_32,c_730,c_728,c_720,
% 11.69/1.98                 c_1449,c_1459,c_1493,c_1501,c_1715,c_1792,c_2409,c_3042]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1366,plain,
% 11.69/1.98      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 11.69/1.98      | k1_xboole_0 = X2_51
% 11.69/1.98      | v1_funct_2(X1_50,X1_51,X2_51) != iProver_top
% 11.69/1.98      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 11.69/1.98      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 11.69/1.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v1_funct_1(X1_50) != iProver_top
% 11.69/1.98      | v2_funct_1(X1_50) = iProver_top
% 11.69/1.98      | v2_funct_1(k1_partfun1(X0_51,X1_51,X1_51,X2_51,X0_50,X1_50)) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3516,plain,
% 11.69/1.98      ( k1_xboole_0 = X0_51
% 11.69/1.98      | v1_funct_2(X0_50,sK1,X0_51) != iProver_top
% 11.69/1.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.69/1.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51))) != iProver_top
% 11.69/1.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v1_funct_1(sK2) != iProver_top
% 11.69/1.98      | v2_funct_1(X0_50) = iProver_top
% 11.69/1.98      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_51,sK2,X0_50)) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_728,c_1366]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_38,plain,
% 11.69/1.98      ( v1_funct_1(sK2) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_39,plain,
% 11.69/1.98      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_40,plain,
% 11.69/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3683,plain,
% 11.69/1.98      ( v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v1_funct_2(X0_50,sK1,X0_51) != iProver_top
% 11.69/1.98      | k1_xboole_0 = X0_51
% 11.69/1.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51))) != iProver_top
% 11.69/1.98      | v2_funct_1(X0_50) = iProver_top
% 11.69/1.98      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_51,sK2,X0_50)) != iProver_top ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_3516,c_38,c_39,c_40]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3684,plain,
% 11.69/1.98      ( k1_xboole_0 = X0_51
% 11.69/1.98      | v1_funct_2(X0_50,sK1,X0_51) != iProver_top
% 11.69/1.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51))) != iProver_top
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v2_funct_1(X0_50) = iProver_top
% 11.69/1.98      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_51,sK2,X0_50)) != iProver_top ),
% 11.69/1.98      inference(renaming,[status(thm)],[c_3683]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3687,plain,
% 11.69/1.98      ( sK0 = k1_xboole_0
% 11.69/1.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.69/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.69/1.98      | v1_funct_1(sK3) != iProver_top
% 11.69/1.98      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 11.69/1.98      | v2_funct_1(sK3) = iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1738,c_3684]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_41,plain,
% 11.69/1.98      ( v1_funct_1(sK3) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_42,plain,
% 11.69/1.98      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_43,plain,
% 11.69/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1793,plain,
% 11.69/1.98      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 11.69/1.98      | k1_xboole_0 = sK0
% 11.69/1.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.69/1.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.69/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.69/1.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.69/1.98      | v1_funct_1(sK3) != iProver_top
% 11.69/1.98      | v1_funct_1(sK2) != iProver_top
% 11.69/1.98      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) != iProver_top
% 11.69/1.98      | v2_funct_1(sK3) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_1792]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2410,plain,
% 11.69/1.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0)
% 11.69/1.98      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) = iProver_top
% 11.69/1.98      | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_2409]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3043,plain,
% 11.69/1.98      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_3042]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3690,plain,
% 11.69/1.98      ( v2_funct_1(sK3) = iProver_top ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_3687,c_37,c_38,c_39,c_35,c_40,c_34,c_41,c_42,c_32,
% 11.69/1.98                 c_43,c_730,c_728,c_720,c_1449,c_1501,c_1715,c_1793,
% 11.69/1.98                 c_2410,c_3043]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_725,negated_conjecture,
% 11.69/1.98      ( v1_funct_1(sK3) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_34]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1374,plain,
% 11.69/1.98      ( v1_funct_1(sK3) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_7,plain,
% 11.69/1.98      ( ~ v1_funct_1(X0)
% 11.69/1.98      | ~ v2_funct_1(X0)
% 11.69/1.98      | ~ v1_relat_1(X0)
% 11.69/1.98      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 11.69/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_748,plain,
% 11.69/1.98      ( ~ v1_funct_1(X0_50)
% 11.69/1.98      | ~ v2_funct_1(X0_50)
% 11.69/1.98      | ~ v1_relat_1(X0_50)
% 11.69/1.98      | k2_funct_1(X0_50) = k4_relat_1(X0_50) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_7]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1355,plain,
% 11.69/1.98      ( k2_funct_1(X0_50) = k4_relat_1(X0_50)
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v2_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2754,plain,
% 11.69/1.98      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 11.69/1.98      | v2_funct_1(sK3) != iProver_top
% 11.69/1.98      | v1_relat_1(sK3) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1374,c_1355]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_727,negated_conjecture,
% 11.69/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_32]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1372,plain,
% 11.69/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_11,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.69/1.98      | v1_relat_1(X0) ),
% 11.69/1.98      inference(cnf_transformation,[],[f64]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_744,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.69/1.98      | v1_relat_1(X0_50) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_11]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1359,plain,
% 11.69/1.98      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 11.69/1.98      | v1_relat_1(X0_50) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2184,plain,
% 11.69/1.98      ( v1_relat_1(sK3) = iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1372,c_1359]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2946,plain,
% 11.69/1.98      ( v2_funct_1(sK3) != iProver_top
% 11.69/1.98      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_2754,c_2184]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2947,plain,
% 11.69/1.98      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 11.69/1.98      | v2_funct_1(sK3) != iProver_top ),
% 11.69/1.98      inference(renaming,[status(thm)],[c_2946]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3694,plain,
% 11.69/1.98      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_3690,c_2947]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_21348,plain,
% 11.69/1.98      ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1) ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_21346,c_3694]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_0,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 11.69/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_755,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0_50) | v1_relat_1(k4_relat_1(X0_50)) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_0]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1348,plain,
% 11.69/1.98      ( v1_relat_1(X0_50) != iProver_top
% 11.69/1.98      | v1_relat_1(k4_relat_1(X0_50)) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_724,negated_conjecture,
% 11.69/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_35]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1375,plain,
% 11.69/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2185,plain,
% 11.69/1.98      ( v1_relat_1(sK2) = iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1375,c_1359]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0)
% 11.69/1.98      | ~ v1_relat_1(X1)
% 11.69/1.98      | ~ v1_relat_1(X2)
% 11.69/1.98      | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
% 11.69/1.98      inference(cnf_transformation,[],[f56]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_752,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0_50)
% 11.69/1.98      | ~ v1_relat_1(X1_50)
% 11.69/1.98      | ~ v1_relat_1(X2_50)
% 11.69/1.98      | k5_relat_1(k5_relat_1(X0_50,X2_50),X1_50) = k5_relat_1(X0_50,k5_relat_1(X2_50,X1_50)) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_3]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1351,plain,
% 11.69/1.98      ( k5_relat_1(k5_relat_1(X0_50,X1_50),X2_50) = k5_relat_1(X0_50,k5_relat_1(X1_50,X2_50))
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X2_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X1_50) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2765,plain,
% 11.69/1.98      ( k5_relat_1(sK2,k5_relat_1(X0_50,X1_50)) = k5_relat_1(k5_relat_1(sK2,X0_50),X1_50)
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X1_50) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2185,c_1351]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_4552,plain,
% 11.69/1.98      ( k5_relat_1(k5_relat_1(sK2,sK3),X0_50) = k5_relat_1(sK2,k5_relat_1(sK3,X0_50))
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2184,c_2765]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_18,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.69/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.69/1.98      | ~ v1_funct_1(X0)
% 11.69/1.98      | ~ v1_funct_1(X3)
% 11.69/1.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.69/1.98      inference(cnf_transformation,[],[f71]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_739,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.69/1.98      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 11.69/1.98      | ~ v1_funct_1(X0_50)
% 11.69/1.98      | ~ v1_funct_1(X1_50)
% 11.69/1.98      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_18]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1364,plain,
% 11.69/1.98      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 11.69/1.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 11.69/1.98      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v1_funct_1(X1_50) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2809,plain,
% 11.69/1.98      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
% 11.69/1.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1372,c_1364]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3130,plain,
% 11.69/1.98      ( v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 11.69/1.98      | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_2809,c_41]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3131,plain,
% 11.69/1.98      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
% 11.69/1.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(renaming,[status(thm)],[c_3130]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3137,plain,
% 11.69/1.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 11.69/1.98      | v1_funct_1(sK2) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1375,c_3131]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3141,plain,
% 11.69/1.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 11.69/1.98      | v1_funct_1(sK2) != iProver_top ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_3137,c_1738]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_4438,plain,
% 11.69/1.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_3141,c_38]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_4554,plain,
% 11.69/1.98      ( k5_relat_1(sK2,k5_relat_1(sK3,X0_50)) = k5_relat_1(k6_partfun1(sK0),X0_50)
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_4552,c_4438]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_9287,plain,
% 11.69/1.98      ( k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(X0_50))) = k5_relat_1(k6_partfun1(sK0),k4_relat_1(X0_50))
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1348,c_4554]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_11304,plain,
% 11.69/1.98      ( k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k4_relat_1(sK3)) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2184,c_9287]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_5,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0)
% 11.69/1.98      | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
% 11.69/1.98      inference(cnf_transformation,[],[f93]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_750,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0_50)
% 11.69/1.98      | k5_relat_1(k6_partfun1(X0_51),X0_50) = k7_relat_1(X0_50,X0_51) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_5]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1353,plain,
% 11.69/1.98      ( k5_relat_1(k6_partfun1(X0_51),X0_50) = k7_relat_1(X0_50,X0_51)
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2154,plain,
% 11.69/1.98      ( k5_relat_1(k6_partfun1(X0_51),k4_relat_1(X0_50)) = k7_relat_1(k4_relat_1(X0_50),X0_51)
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1348,c_1353]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_6109,plain,
% 11.69/1.98      ( k5_relat_1(k6_partfun1(X0_51),k4_relat_1(sK3)) = k7_relat_1(k4_relat_1(sK3),X0_51) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2184,c_2154]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_9,plain,
% 11.69/1.98      ( ~ v1_funct_1(X0)
% 11.69/1.98      | ~ v1_relat_1(X0)
% 11.69/1.98      | v1_relat_1(k2_funct_1(X0)) ),
% 11.69/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_746,plain,
% 11.69/1.98      ( ~ v1_funct_1(X0_50)
% 11.69/1.98      | ~ v1_relat_1(X0_50)
% 11.69/1.98      | v1_relat_1(k2_funct_1(X0_50)) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_9]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1357,plain,
% 11.69/1.98      ( v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top
% 11.69/1.98      | v1_relat_1(k2_funct_1(X0_50)) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_6,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 11.69/1.98      inference(cnf_transformation,[],[f59]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_749,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0_50)
% 11.69/1.98      | k7_relat_1(X0_50,k1_relat_1(X0_50)) = X0_50 ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_6]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1354,plain,
% 11.69/1.98      ( k7_relat_1(X0_50,k1_relat_1(X0_50)) = X0_50
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_749]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2231,plain,
% 11.69/1.98      ( k7_relat_1(k2_funct_1(X0_50),k1_relat_1(k2_funct_1(X0_50))) = k2_funct_1(X0_50)
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1357,c_1354]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_7946,plain,
% 11.69/1.98      ( k7_relat_1(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3))) = k2_funct_1(sK3)
% 11.69/1.98      | v1_relat_1(sK3) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1374,c_2231]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 11.69/1.98      inference(cnf_transformation,[],[f54]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_753,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0_50)
% 11.69/1.98      | k1_relat_1(k4_relat_1(X0_50)) = k2_relat_1(X0_50) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_2]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1350,plain,
% 11.69/1.98      ( k1_relat_1(k4_relat_1(X0_50)) = k2_relat_1(X0_50)
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2306,plain,
% 11.69/1.98      ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2184,c_1350]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_12,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.69/1.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.69/1.98      inference(cnf_transformation,[],[f65]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_743,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.69/1.98      | k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_12]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1360,plain,
% 11.69/1.98      ( k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50)
% 11.69/1.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2251,plain,
% 11.69/1.98      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1372,c_1360]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2255,plain,
% 11.69/1.98      ( k2_relat_1(sK3) = sK0 ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_2251,c_1838]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2310,plain,
% 11.69/1.98      ( k1_relat_1(k4_relat_1(sK3)) = sK0 ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_2306,c_2255]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_7955,plain,
% 11.69/1.98      ( k7_relat_1(k4_relat_1(sK3),sK0) = k4_relat_1(sK3)
% 11.69/1.98      | v1_relat_1(sK3) != iProver_top ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_7946,c_2310,c_3694]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_8374,plain,
% 11.69/1.98      ( k7_relat_1(k4_relat_1(sK3),sK0) = k4_relat_1(sK3) ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_7955,c_2184]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_11313,plain,
% 11.69/1.98      ( k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(sK3))) = k4_relat_1(sK3) ),
% 11.69/1.98      inference(demodulation,[status(thm)],[c_11304,c_6109,c_8374]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_21351,plain,
% 11.69/1.98      ( k5_relat_1(sK2,k6_partfun1(sK1)) = k4_relat_1(sK3) ),
% 11.69/1.98      inference(demodulation,[status(thm)],[c_21348,c_11313]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_4,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0)
% 11.69/1.98      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 11.69/1.98      inference(cnf_transformation,[],[f92]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_751,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0_50)
% 11.69/1.98      | k5_relat_1(X0_50,k6_partfun1(k2_relat_1(X0_50))) = X0_50 ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_4]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1352,plain,
% 11.69/1.98      ( k5_relat_1(X0_50,k6_partfun1(k2_relat_1(X0_50))) = X0_50
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2401,plain,
% 11.69/1.98      ( k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) = sK2 ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2185,c_1352]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2252,plain,
% 11.69/1.98      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1375,c_1360]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2254,plain,
% 11.69/1.98      ( k2_relat_1(sK2) = sK1 ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_2252,c_728]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2402,plain,
% 11.69/1.98      ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_2401,c_2254]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_21352,plain,
% 11.69/1.98      ( k4_relat_1(sK3) = sK2 ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_21351,c_2402]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 11.69/1.98      inference(cnf_transformation,[],[f55]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_754,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0_50)
% 11.69/1.98      | k2_relat_1(k4_relat_1(X0_50)) = k1_relat_1(X0_50) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_1]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1349,plain,
% 11.69/1.98      ( k2_relat_1(k4_relat_1(X0_50)) = k1_relat_1(X0_50)
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2307,plain,
% 11.69/1.98      ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2184,c_1349]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_21678,plain,
% 11.69/1.98      ( k1_relat_1(sK3) = k2_relat_1(sK2) ),
% 11.69/1.98      inference(demodulation,[status(thm)],[c_21352,c_2307]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_21679,plain,
% 11.69/1.98      ( k1_relat_1(sK3) = sK1 ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_21678,c_2254]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2305,plain,
% 11.69/1.98      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2184,c_1354]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_21686,plain,
% 11.69/1.98      ( k7_relat_1(sK3,sK1) = sK3 ),
% 11.69/1.98      inference(demodulation,[status(thm)],[c_21679,c_2305]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_6108,plain,
% 11.69/1.98      ( k5_relat_1(k6_partfun1(X0_51),k4_relat_1(sK2)) = k7_relat_1(k4_relat_1(sK2),X0_51) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2185,c_2154]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_722,negated_conjecture,
% 11.69/1.98      ( v1_funct_1(sK2) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_37]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1377,plain,
% 11.69/1.98      ( v1_funct_1(sK2) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2763,plain,
% 11.69/1.98      ( k5_relat_1(k2_funct_1(X0_50),k5_relat_1(X1_50,X2_50)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_50),X1_50),X2_50)
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X1_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X2_50) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1357,c_1351]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_13463,plain,
% 11.69/1.98      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_50),X1_50) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_50,X1_50))
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X1_50) != iProver_top
% 11.69/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1377,c_2763]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2755,plain,
% 11.69/1.98      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 11.69/1.98      | v2_funct_1(sK2) != iProver_top
% 11.69/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1377,c_1355]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_29,negated_conjecture,
% 11.69/1.98      ( v2_funct_1(sK2) ),
% 11.69/1.98      inference(cnf_transformation,[],[f88]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_45,plain,
% 11.69/1.98      ( v2_funct_1(sK2) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_819,plain,
% 11.69/1.98      ( k2_funct_1(X0_50) = k4_relat_1(X0_50)
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v2_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_821,plain,
% 11.69/1.98      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 11.69/1.98      | v1_funct_1(sK2) != iProver_top
% 11.69/1.98      | v2_funct_1(sK2) != iProver_top
% 11.69/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_819]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3067,plain,
% 11.69/1.98      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_2755,c_38,c_45,c_821,c_2185]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_13471,plain,
% 11.69/1.98      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0_50,X1_50)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0_50),X1_50)
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X1_50) != iProver_top
% 11.69/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_13463,c_3067]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15178,plain,
% 11.69/1.98      ( v1_relat_1(X1_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top
% 11.69/1.98      | k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0_50,X1_50)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0_50),X1_50) ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_13471,c_2185]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15179,plain,
% 11.69/1.98      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0_50,X1_50)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0_50),X1_50)
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top
% 11.69/1.98      | v1_relat_1(X1_50) != iProver_top ),
% 11.69/1.98      inference(renaming,[status(thm)],[c_15178]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15184,plain,
% 11.69/1.98      ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),X0_50) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0_50))
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2185,c_15179]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_24,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 11.69/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.69/1.98      | ~ v1_funct_1(X0)
% 11.69/1.98      | ~ v2_funct_1(X0)
% 11.69/1.98      | k2_relset_1(X1,X2,X0) != X2
% 11.69/1.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 11.69/1.98      | k1_xboole_0 = X2 ),
% 11.69/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_734,plain,
% 11.69/1.98      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 11.69/1.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 11.69/1.98      | ~ v1_funct_1(X0_50)
% 11.69/1.98      | ~ v2_funct_1(X0_50)
% 11.69/1.98      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 11.69/1.98      | k1_xboole_0 = X1_51
% 11.69/1.98      | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(X1_51) ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_24]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1369,plain,
% 11.69/1.98      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 11.69/1.98      | k1_xboole_0 = X1_51
% 11.69/1.98      | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(X1_51)
% 11.69/1.98      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 11.69/1.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 11.69/1.98      | v1_funct_1(X0_50) != iProver_top
% 11.69/1.98      | v2_funct_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_734]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3479,plain,
% 11.69/1.98      ( sK1 = k1_xboole_0
% 11.69/1.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 11.69/1.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.69/1.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.69/1.98      | v1_funct_1(sK2) != iProver_top
% 11.69/1.98      | v2_funct_1(sK2) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_728,c_1369]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3481,plain,
% 11.69/1.98      ( sK1 = k1_xboole_0
% 11.69/1.98      | k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1)
% 11.69/1.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.69/1.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.69/1.98      | v1_funct_1(sK2) != iProver_top
% 11.69/1.98      | v2_funct_1(sK2) != iProver_top ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_3479,c_3067]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_758,plain,( X0_51 = X0_51 ),theory(equality) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_795,plain,
% 11.69/1.98      ( k1_xboole_0 = k1_xboole_0 ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_758]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_27,negated_conjecture,
% 11.69/1.98      ( k1_xboole_0 != sK1 ),
% 11.69/1.98      inference(cnf_transformation,[],[f90]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_731,negated_conjecture,
% 11.69/1.98      ( k1_xboole_0 != sK1 ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_27]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_762,plain,
% 11.69/1.98      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 11.69/1.98      theory(equality) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1445,plain,
% 11.69/1.98      ( sK1 != X0_51 | k1_xboole_0 != X0_51 | k1_xboole_0 = sK1 ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_762]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1446,plain,
% 11.69/1.98      ( sK1 != k1_xboole_0
% 11.69/1.98      | k1_xboole_0 = sK1
% 11.69/1.98      | k1_xboole_0 != k1_xboole_0 ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_1445]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3785,plain,
% 11.69/1.98      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_3481,c_38,c_39,c_40,c_45,c_795,c_731,c_1446]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15190,plain,
% 11.69/1.98      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0_50)) = k5_relat_1(k6_partfun1(sK1),X0_50)
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_15184,c_3785]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15265,plain,
% 11.69/1.98      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,k4_relat_1(X0_50))) = k5_relat_1(k6_partfun1(sK1),k4_relat_1(X0_50))
% 11.69/1.98      | v1_relat_1(X0_50) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1348,c_15190]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15381,plain,
% 11.69/1.98      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,k4_relat_1(sK2))) = k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2185,c_15265]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3485,plain,
% 11.69/1.98      ( sK1 = k1_xboole_0
% 11.69/1.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 11.69/1.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.69/1.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.69/1.98      | v1_funct_1(sK2) != iProver_top
% 11.69/1.98      | v2_funct_1(sK2) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_728,c_1370]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3487,plain,
% 11.69/1.98      ( sK1 = k1_xboole_0
% 11.69/1.98      | k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(sK0)
% 11.69/1.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.69/1.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.69/1.98      | v1_funct_1(sK2) != iProver_top
% 11.69/1.98      | v2_funct_1(sK2) != iProver_top ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_3485,c_3067]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3788,plain,
% 11.69/1.98      ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(sK0) ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_3487,c_38,c_39,c_40,c_45,c_795,c_731,c_1446]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15267,plain,
% 11.69/1.98      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2184,c_15190]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15278,plain,
% 11.69/1.98      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_15267,c_4438]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2304,plain,
% 11.69/1.98      ( k5_relat_1(k6_partfun1(X0_51),sK3) = k7_relat_1(sK3,X0_51) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2184,c_1353]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15279,plain,
% 11.69/1.98      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k7_relat_1(sK3,sK1) ),
% 11.69/1.98      inference(demodulation,[status(thm)],[c_15278,c_2304]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15392,plain,
% 11.69/1.98      ( k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)) = k7_relat_1(sK3,sK1) ),
% 11.69/1.98      inference(light_normalisation,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_15381,c_3788,c_15279]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15509,plain,
% 11.69/1.98      ( k7_relat_1(k4_relat_1(sK2),sK1) = k7_relat_1(sK3,sK1) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_6108,c_15392]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_7947,plain,
% 11.69/1.98      ( k7_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_funct_1(sK2)
% 11.69/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1377,c_2231]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2399,plain,
% 11.69/1.98      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2185,c_1350]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2403,plain,
% 11.69/1.98      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_2399,c_2254]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_7954,plain,
% 11.69/1.98      ( k7_relat_1(k4_relat_1(sK2),sK1) = k4_relat_1(sK2)
% 11.69/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_7947,c_2403,c_3067]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_8371,plain,
% 11.69/1.98      ( k7_relat_1(k4_relat_1(sK2),sK1) = k4_relat_1(sK2) ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_7954,c_2185]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15511,plain,
% 11.69/1.98      ( k7_relat_1(sK3,sK1) = k4_relat_1(sK2) ),
% 11.69/1.98      inference(light_normalisation,[status(thm)],[c_15509,c_8371]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_21864,plain,
% 11.69/1.98      ( k4_relat_1(sK2) = sK3 ),
% 11.69/1.98      inference(demodulation,[status(thm)],[c_21686,c_15511]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_26,negated_conjecture,
% 11.69/1.98      ( k2_funct_1(sK2) != sK3 ),
% 11.69/1.98      inference(cnf_transformation,[],[f91]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_732,negated_conjecture,
% 11.69/1.98      ( k2_funct_1(sK2) != sK3 ),
% 11.69/1.98      inference(subtyping,[status(esa)],[c_26]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3069,plain,
% 11.69/1.98      ( k4_relat_1(sK2) != sK3 ),
% 11.69/1.98      inference(demodulation,[status(thm)],[c_3067,c_732]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(contradiction,plain,
% 11.69/1.98      ( $false ),
% 11.69/1.98      inference(minisat,[status(thm)],[c_21864,c_3069]) ).
% 11.69/1.98  
% 11.69/1.98  
% 11.69/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.69/1.98  
% 11.69/1.98  ------                               Statistics
% 11.69/1.98  
% 11.69/1.98  ------ General
% 11.69/1.98  
% 11.69/1.98  abstr_ref_over_cycles:                  0
% 11.69/1.98  abstr_ref_under_cycles:                 0
% 11.69/1.98  gc_basic_clause_elim:                   0
% 11.69/1.98  forced_gc_time:                         0
% 11.69/1.98  parsing_time:                           0.01
% 11.69/1.98  unif_index_cands_time:                  0.
% 11.69/1.98  unif_index_add_time:                    0.
% 11.69/1.98  orderings_time:                         0.
% 11.69/1.98  out_proof_time:                         0.019
% 11.69/1.98  total_time:                             1.096
% 11.69/1.98  num_of_symbols:                         57
% 11.69/1.98  num_of_terms:                           31417
% 11.69/1.98  
% 11.69/1.98  ------ Preprocessing
% 11.69/1.98  
% 11.69/1.98  num_of_splits:                          0
% 11.69/1.98  num_of_split_atoms:                     0
% 11.69/1.98  num_of_reused_defs:                     0
% 11.69/1.98  num_eq_ax_congr_red:                    6
% 11.69/1.98  num_of_sem_filtered_clauses:            1
% 11.69/1.98  num_of_subtypes:                        4
% 11.69/1.98  monotx_restored_types:                  1
% 11.69/1.98  sat_num_of_epr_types:                   0
% 11.69/1.98  sat_num_of_non_cyclic_types:            0
% 11.69/1.98  sat_guarded_non_collapsed_types:        1
% 11.69/1.98  num_pure_diseq_elim:                    0
% 11.69/1.98  simp_replaced_by:                       0
% 11.69/1.98  res_preprocessed:                       192
% 11.69/1.98  prep_upred:                             0
% 11.69/1.98  prep_unflattend:                        12
% 11.69/1.98  smt_new_axioms:                         0
% 11.69/1.98  pred_elim_cands:                        5
% 11.69/1.98  pred_elim:                              1
% 11.69/1.98  pred_elim_cl:                           1
% 11.69/1.98  pred_elim_cycles:                       3
% 11.69/1.98  merged_defs:                            0
% 11.69/1.98  merged_defs_ncl:                        0
% 11.69/1.98  bin_hyper_res:                          0
% 11.69/1.98  prep_cycles:                            4
% 11.69/1.98  pred_elim_time:                         0.004
% 11.69/1.98  splitting_time:                         0.
% 11.69/1.98  sem_filter_time:                        0.
% 11.69/1.98  monotx_time:                            0.001
% 11.69/1.98  subtype_inf_time:                       0.002
% 11.69/1.98  
% 11.69/1.98  ------ Problem properties
% 11.69/1.98  
% 11.69/1.98  clauses:                                37
% 11.69/1.98  conjectures:                            11
% 11.69/1.98  epr:                                    7
% 11.69/1.98  horn:                                   33
% 11.69/1.98  ground:                                 12
% 11.69/1.98  unary:                                  13
% 11.69/1.98  binary:                                 9
% 11.69/1.98  lits:                                   128
% 11.69/1.98  lits_eq:                                30
% 11.69/1.98  fd_pure:                                0
% 11.69/1.98  fd_pseudo:                              0
% 11.69/1.98  fd_cond:                                4
% 11.69/1.98  fd_pseudo_cond:                         0
% 11.69/1.98  ac_symbols:                             0
% 11.69/1.98  
% 11.69/1.98  ------ Propositional Solver
% 11.69/1.98  
% 11.69/1.98  prop_solver_calls:                      34
% 11.69/1.98  prop_fast_solver_calls:                 2091
% 11.69/1.98  smt_solver_calls:                       0
% 11.69/1.98  smt_fast_solver_calls:                  0
% 11.69/1.98  prop_num_of_clauses:                    10512
% 11.69/1.98  prop_preprocess_simplified:             21060
% 11.69/1.98  prop_fo_subsumed:                       164
% 11.69/1.98  prop_solver_time:                       0.
% 11.69/1.98  smt_solver_time:                        0.
% 11.69/1.98  smt_fast_solver_time:                   0.
% 11.69/1.98  prop_fast_solver_time:                  0.
% 11.69/1.98  prop_unsat_core_time:                   0.001
% 11.69/1.98  
% 11.69/1.98  ------ QBF
% 11.69/1.98  
% 11.69/1.98  qbf_q_res:                              0
% 11.69/1.98  qbf_num_tautologies:                    0
% 11.69/1.98  qbf_prep_cycles:                        0
% 11.69/1.98  
% 11.69/1.98  ------ BMC1
% 11.69/1.98  
% 11.69/1.98  bmc1_current_bound:                     -1
% 11.69/1.98  bmc1_last_solved_bound:                 -1
% 11.69/1.98  bmc1_unsat_core_size:                   -1
% 11.69/1.98  bmc1_unsat_core_parents_size:           -1
% 11.69/1.98  bmc1_merge_next_fun:                    0
% 11.69/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.69/1.98  
% 11.69/1.98  ------ Instantiation
% 11.69/1.98  
% 11.69/1.98  inst_num_of_clauses:                    3016
% 11.69/1.98  inst_num_in_passive:                    771
% 11.69/1.98  inst_num_in_active:                     1415
% 11.69/1.98  inst_num_in_unprocessed:                830
% 11.69/1.98  inst_num_of_loops:                      1500
% 11.69/1.98  inst_num_of_learning_restarts:          0
% 11.69/1.98  inst_num_moves_active_passive:          78
% 11.69/1.98  inst_lit_activity:                      0
% 11.69/1.98  inst_lit_activity_moves:                0
% 11.69/1.98  inst_num_tautologies:                   0
% 11.69/1.98  inst_num_prop_implied:                  0
% 11.69/1.98  inst_num_existing_simplified:           0
% 11.69/1.98  inst_num_eq_res_simplified:             0
% 11.69/1.98  inst_num_child_elim:                    0
% 11.69/1.98  inst_num_of_dismatching_blockings:      749
% 11.69/1.98  inst_num_of_non_proper_insts:           2914
% 11.69/1.98  inst_num_of_duplicates:                 0
% 11.69/1.98  inst_inst_num_from_inst_to_res:         0
% 11.69/1.98  inst_dismatching_checking_time:         0.
% 11.69/1.98  
% 11.69/1.98  ------ Resolution
% 11.69/1.98  
% 11.69/1.98  res_num_of_clauses:                     0
% 11.69/1.98  res_num_in_passive:                     0
% 11.69/1.98  res_num_in_active:                      0
% 11.69/1.98  res_num_of_loops:                       196
% 11.69/1.98  res_forward_subset_subsumed:            447
% 11.69/1.98  res_backward_subset_subsumed:           0
% 11.69/1.98  res_forward_subsumed:                   0
% 11.69/1.98  res_backward_subsumed:                  0
% 11.69/1.98  res_forward_subsumption_resolution:     2
% 11.69/1.98  res_backward_subsumption_resolution:    0
% 11.69/1.98  res_clause_to_clause_subsumption:       2177
% 11.69/1.98  res_orphan_elimination:                 0
% 11.69/1.98  res_tautology_del:                      226
% 11.69/1.98  res_num_eq_res_simplified:              1
% 11.69/1.98  res_num_sel_changes:                    0
% 11.69/1.98  res_moves_from_active_to_pass:          0
% 11.69/1.98  
% 11.69/1.98  ------ Superposition
% 11.69/1.98  
% 11.69/1.98  sup_time_total:                         0.
% 11.69/1.98  sup_time_generating:                    0.
% 11.69/1.98  sup_time_sim_full:                      0.
% 11.69/1.98  sup_time_sim_immed:                     0.
% 11.69/1.98  
% 11.69/1.98  sup_num_of_clauses:                     869
% 11.69/1.98  sup_num_in_active:                      243
% 11.69/1.98  sup_num_in_passive:                     626
% 11.69/1.98  sup_num_of_loops:                       298
% 11.69/1.98  sup_fw_superposition:                   625
% 11.69/1.98  sup_bw_superposition:                   324
% 11.69/1.98  sup_immediate_simplified:               363
% 11.69/1.98  sup_given_eliminated:                   0
% 11.69/1.98  comparisons_done:                       0
% 11.69/1.98  comparisons_avoided:                    0
% 11.69/1.98  
% 11.69/1.98  ------ Simplifications
% 11.69/1.98  
% 11.69/1.98  
% 11.69/1.98  sim_fw_subset_subsumed:                 12
% 11.69/1.98  sim_bw_subset_subsumed:                 34
% 11.69/1.98  sim_fw_subsumed:                        12
% 11.69/1.98  sim_bw_subsumed:                        0
% 11.69/1.98  sim_fw_subsumption_res:                 0
% 11.69/1.98  sim_bw_subsumption_res:                 0
% 11.69/1.98  sim_tautology_del:                      2
% 11.69/1.98  sim_eq_tautology_del:                   25
% 11.69/1.98  sim_eq_res_simp:                        0
% 11.69/1.98  sim_fw_demodulated:                     88
% 11.69/1.98  sim_bw_demodulated:                     49
% 11.69/1.98  sim_light_normalised:                   262
% 11.69/1.98  sim_joinable_taut:                      0
% 11.69/1.98  sim_joinable_simp:                      0
% 11.69/1.98  sim_ac_normalised:                      0
% 11.69/1.98  sim_smt_subsumption:                    0
% 11.69/1.98  
%------------------------------------------------------------------------------
