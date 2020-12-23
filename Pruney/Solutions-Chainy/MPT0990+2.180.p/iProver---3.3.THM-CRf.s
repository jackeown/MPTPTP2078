%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:35 EST 2020

% Result     : Theorem 8.03s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :  229 (3911 expanded)
%              Number of clauses        :  140 (1101 expanded)
%              Number of leaves         :   23 (1035 expanded)
%              Depth                    :   23
%              Number of atoms          :  874 (33230 expanded)
%              Number of equality atoms :  439 (12074 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f20])).

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
    inference(flattening,[],[f46])).

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f50,f49])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f82,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f67,f74])).

fof(f88,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f18,axiom,(
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

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f44])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f74])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f94,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f74])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f96,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f61,f74])).

fof(f17,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f42])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f99,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1241,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1244,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1252,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4769,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1252])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_44,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4823,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4769,c_44])).

cnf(c_4824,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4823])).

cnf(c_4832,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_4824])).

cnf(c_17,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_33,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_430,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_438,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_430,c_20])).

cnf(c_1237,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1354,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1989,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1237,c_40,c_38,c_37,c_35,c_438,c_1354])).

cnf(c_4833,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4832,c_1989])).

cnf(c_41,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_5271,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4833,c_41])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1256,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5273,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5271,c_1256])).

cnf(c_34,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1247,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3600,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_34,c_1247])).

cnf(c_1239,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1264,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3208,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1239,c_1264])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_48,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1266,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1267,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2262,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1267])).

cnf(c_2289,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_2262])).

cnf(c_3310,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3208,c_48,c_2289])).

cnf(c_3602,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3600,c_3310])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_42,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_713,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_746,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_714,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1332,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_1333,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1332])).

cnf(c_5087,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3602,c_41,c_42,c_43,c_48,c_30,c_746,c_1333])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1258,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3256,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1239,c_1258])).

cnf(c_4819,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3256,c_48,c_2289])).

cnf(c_4821,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4819,c_3310])).

cnf(c_5089,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_5087,c_4821])).

cnf(c_3,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_5095,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_5089,c_3])).

cnf(c_5096,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_5095,c_3])).

cnf(c_5274,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5273,c_5096])).

cnf(c_2261,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1267])).

cnf(c_2286,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_2261])).

cnf(c_8,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1261,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f78])).

cnf(c_1250,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5508,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_34,c_1250])).

cnf(c_5570,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5508,c_41,c_42,c_43])).

cnf(c_5571,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5570])).

cnf(c_5574,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1989,c_5571])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_45,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1352,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_1353,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1352])).

cnf(c_6068,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5574,c_44,c_45,c_46,c_31,c_746,c_1353])).

cnf(c_6072,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_6068])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_442,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_443,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_529,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_443])).

cnf(c_1236,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_1792,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1236])).

cnf(c_1996,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1792,c_41,c_42,c_43,c_44,c_45,c_46])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1246,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2920,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1996,c_1246])).

cnf(c_6847,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2920,c_44,c_45,c_46,c_31,c_746,c_1353,c_6072])).

cnf(c_1242,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3207,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1264])).

cnf(c_3305,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3207,c_2286])).

cnf(c_3306,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3305])).

cnf(c_6077,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6072,c_3306])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1257,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3216,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1257])).

cnf(c_3435,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3216,c_2286])).

cnf(c_3436,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3435])).

cnf(c_6076,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_6072,c_3436])).

cnf(c_6078,plain,
    ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(demodulation,[status(thm)],[c_6076,c_6077])).

cnf(c_6849,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_6847,c_6077,c_6078])).

cnf(c_6857,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6849,c_3])).

cnf(c_6858,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_6857,c_3])).

cnf(c_3601,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1996,c_1247])).

cnf(c_10274,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3601,c_44,c_45,c_46,c_31,c_746,c_1353,c_6072])).

cnf(c_3255,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1258])).

cnf(c_3591,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3255,c_2286])).

cnf(c_3592,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3591])).

cnf(c_6075,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_6072,c_3592])).

cnf(c_6079,plain,
    ( k5_relat_1(k4_relat_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3)) ),
    inference(demodulation,[status(thm)],[c_6075,c_6077])).

cnf(c_10276,plain,
    ( k6_partfun1(k2_relat_1(sK3)) = k6_partfun1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_10274,c_6077,c_6079])).

cnf(c_16665,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5274,c_41,c_44,c_2286,c_2289,c_6072,c_6858,c_10276])).

cnf(c_16667,plain,
    ( k4_relat_1(sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_16665,c_6077])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1263,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3206,plain,
    ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_1264])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_108,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7604,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3206,c_108])).

cnf(c_7605,plain,
    ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7604])).

cnf(c_7612,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6077,c_7605])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1265,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2488,plain,
    ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2286,c_1265])).

cnf(c_7613,plain,
    ( k2_funct_1(k4_relat_1(sK3)) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7612,c_2488,c_6077])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1259,plain,
    ( v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6520,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k4_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6077,c_1259])).

cnf(c_8619,plain,
    ( k2_funct_1(k4_relat_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7613,c_44,c_2286,c_6072,c_6520])).

cnf(c_22966,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_16667,c_8619])).

cnf(c_29,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f93])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22966,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.03/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/1.51  
% 8.03/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.03/1.51  
% 8.03/1.51  ------  iProver source info
% 8.03/1.51  
% 8.03/1.51  git: date: 2020-06-30 10:37:57 +0100
% 8.03/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.03/1.51  git: non_committed_changes: false
% 8.03/1.51  git: last_make_outside_of_git: false
% 8.03/1.51  
% 8.03/1.51  ------ 
% 8.03/1.51  
% 8.03/1.51  ------ Input Options
% 8.03/1.51  
% 8.03/1.51  --out_options                           all
% 8.03/1.51  --tptp_safe_out                         true
% 8.03/1.51  --problem_path                          ""
% 8.03/1.51  --include_path                          ""
% 8.03/1.51  --clausifier                            res/vclausify_rel
% 8.03/1.51  --clausifier_options                    ""
% 8.03/1.51  --stdin                                 false
% 8.03/1.51  --stats_out                             all
% 8.03/1.51  
% 8.03/1.51  ------ General Options
% 8.03/1.51  
% 8.03/1.51  --fof                                   false
% 8.03/1.51  --time_out_real                         305.
% 8.03/1.51  --time_out_virtual                      -1.
% 8.03/1.51  --symbol_type_check                     false
% 8.03/1.51  --clausify_out                          false
% 8.03/1.51  --sig_cnt_out                           false
% 8.03/1.51  --trig_cnt_out                          false
% 8.03/1.51  --trig_cnt_out_tolerance                1.
% 8.03/1.51  --trig_cnt_out_sk_spl                   false
% 8.03/1.51  --abstr_cl_out                          false
% 8.03/1.51  
% 8.03/1.51  ------ Global Options
% 8.03/1.51  
% 8.03/1.51  --schedule                              default
% 8.03/1.51  --add_important_lit                     false
% 8.03/1.51  --prop_solver_per_cl                    1000
% 8.03/1.51  --min_unsat_core                        false
% 8.03/1.51  --soft_assumptions                      false
% 8.03/1.51  --soft_lemma_size                       3
% 8.03/1.51  --prop_impl_unit_size                   0
% 8.03/1.51  --prop_impl_unit                        []
% 8.03/1.51  --share_sel_clauses                     true
% 8.03/1.51  --reset_solvers                         false
% 8.03/1.51  --bc_imp_inh                            [conj_cone]
% 8.03/1.51  --conj_cone_tolerance                   3.
% 8.03/1.51  --extra_neg_conj                        none
% 8.03/1.51  --large_theory_mode                     true
% 8.03/1.51  --prolific_symb_bound                   200
% 8.03/1.51  --lt_threshold                          2000
% 8.03/1.51  --clause_weak_htbl                      true
% 8.03/1.51  --gc_record_bc_elim                     false
% 8.03/1.51  
% 8.03/1.51  ------ Preprocessing Options
% 8.03/1.51  
% 8.03/1.51  --preprocessing_flag                    true
% 8.03/1.51  --time_out_prep_mult                    0.1
% 8.03/1.51  --splitting_mode                        input
% 8.03/1.51  --splitting_grd                         true
% 8.03/1.51  --splitting_cvd                         false
% 8.03/1.51  --splitting_cvd_svl                     false
% 8.03/1.51  --splitting_nvd                         32
% 8.03/1.51  --sub_typing                            true
% 8.03/1.51  --prep_gs_sim                           true
% 8.03/1.51  --prep_unflatten                        true
% 8.03/1.51  --prep_res_sim                          true
% 8.03/1.51  --prep_upred                            true
% 8.03/1.51  --prep_sem_filter                       exhaustive
% 8.03/1.51  --prep_sem_filter_out                   false
% 8.03/1.51  --pred_elim                             true
% 8.03/1.51  --res_sim_input                         true
% 8.03/1.51  --eq_ax_congr_red                       true
% 8.03/1.51  --pure_diseq_elim                       true
% 8.03/1.51  --brand_transform                       false
% 8.03/1.51  --non_eq_to_eq                          false
% 8.03/1.51  --prep_def_merge                        true
% 8.03/1.51  --prep_def_merge_prop_impl              false
% 8.03/1.51  --prep_def_merge_mbd                    true
% 8.03/1.51  --prep_def_merge_tr_red                 false
% 8.03/1.51  --prep_def_merge_tr_cl                  false
% 8.03/1.51  --smt_preprocessing                     true
% 8.03/1.51  --smt_ac_axioms                         fast
% 8.03/1.51  --preprocessed_out                      false
% 8.03/1.51  --preprocessed_stats                    false
% 8.03/1.51  
% 8.03/1.51  ------ Abstraction refinement Options
% 8.03/1.51  
% 8.03/1.51  --abstr_ref                             []
% 8.03/1.51  --abstr_ref_prep                        false
% 8.03/1.51  --abstr_ref_until_sat                   false
% 8.03/1.51  --abstr_ref_sig_restrict                funpre
% 8.03/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 8.03/1.51  --abstr_ref_under                       []
% 8.03/1.51  
% 8.03/1.51  ------ SAT Options
% 8.03/1.51  
% 8.03/1.51  --sat_mode                              false
% 8.03/1.51  --sat_fm_restart_options                ""
% 8.03/1.51  --sat_gr_def                            false
% 8.03/1.51  --sat_epr_types                         true
% 8.03/1.51  --sat_non_cyclic_types                  false
% 8.03/1.51  --sat_finite_models                     false
% 8.03/1.51  --sat_fm_lemmas                         false
% 8.03/1.51  --sat_fm_prep                           false
% 8.03/1.51  --sat_fm_uc_incr                        true
% 8.03/1.51  --sat_out_model                         small
% 8.03/1.51  --sat_out_clauses                       false
% 8.03/1.51  
% 8.03/1.51  ------ QBF Options
% 8.03/1.51  
% 8.03/1.51  --qbf_mode                              false
% 8.03/1.51  --qbf_elim_univ                         false
% 8.03/1.51  --qbf_dom_inst                          none
% 8.03/1.51  --qbf_dom_pre_inst                      false
% 8.03/1.51  --qbf_sk_in                             false
% 8.03/1.51  --qbf_pred_elim                         true
% 8.03/1.51  --qbf_split                             512
% 8.03/1.51  
% 8.03/1.51  ------ BMC1 Options
% 8.03/1.51  
% 8.03/1.51  --bmc1_incremental                      false
% 8.03/1.51  --bmc1_axioms                           reachable_all
% 8.03/1.51  --bmc1_min_bound                        0
% 8.03/1.51  --bmc1_max_bound                        -1
% 8.03/1.51  --bmc1_max_bound_default                -1
% 8.03/1.51  --bmc1_symbol_reachability              true
% 8.03/1.51  --bmc1_property_lemmas                  false
% 8.03/1.51  --bmc1_k_induction                      false
% 8.03/1.51  --bmc1_non_equiv_states                 false
% 8.03/1.51  --bmc1_deadlock                         false
% 8.03/1.51  --bmc1_ucm                              false
% 8.03/1.51  --bmc1_add_unsat_core                   none
% 8.03/1.51  --bmc1_unsat_core_children              false
% 8.03/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 8.03/1.51  --bmc1_out_stat                         full
% 8.03/1.51  --bmc1_ground_init                      false
% 8.03/1.51  --bmc1_pre_inst_next_state              false
% 8.03/1.51  --bmc1_pre_inst_state                   false
% 8.03/1.51  --bmc1_pre_inst_reach_state             false
% 8.03/1.51  --bmc1_out_unsat_core                   false
% 8.03/1.51  --bmc1_aig_witness_out                  false
% 8.03/1.51  --bmc1_verbose                          false
% 8.03/1.51  --bmc1_dump_clauses_tptp                false
% 8.03/1.51  --bmc1_dump_unsat_core_tptp             false
% 8.03/1.51  --bmc1_dump_file                        -
% 8.03/1.51  --bmc1_ucm_expand_uc_limit              128
% 8.03/1.51  --bmc1_ucm_n_expand_iterations          6
% 8.03/1.51  --bmc1_ucm_extend_mode                  1
% 8.03/1.51  --bmc1_ucm_init_mode                    2
% 8.03/1.51  --bmc1_ucm_cone_mode                    none
% 8.03/1.51  --bmc1_ucm_reduced_relation_type        0
% 8.03/1.51  --bmc1_ucm_relax_model                  4
% 8.03/1.51  --bmc1_ucm_full_tr_after_sat            true
% 8.03/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 8.03/1.51  --bmc1_ucm_layered_model                none
% 8.03/1.51  --bmc1_ucm_max_lemma_size               10
% 8.03/1.51  
% 8.03/1.51  ------ AIG Options
% 8.03/1.51  
% 8.03/1.51  --aig_mode                              false
% 8.03/1.51  
% 8.03/1.51  ------ Instantiation Options
% 8.03/1.51  
% 8.03/1.51  --instantiation_flag                    true
% 8.03/1.51  --inst_sos_flag                         true
% 8.03/1.51  --inst_sos_phase                        true
% 8.03/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.03/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.03/1.51  --inst_lit_sel_side                     num_symb
% 8.03/1.51  --inst_solver_per_active                1400
% 8.03/1.51  --inst_solver_calls_frac                1.
% 8.03/1.51  --inst_passive_queue_type               priority_queues
% 8.03/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.03/1.51  --inst_passive_queues_freq              [25;2]
% 8.03/1.51  --inst_dismatching                      true
% 8.03/1.51  --inst_eager_unprocessed_to_passive     true
% 8.03/1.51  --inst_prop_sim_given                   true
% 8.03/1.51  --inst_prop_sim_new                     false
% 8.03/1.51  --inst_subs_new                         false
% 8.03/1.51  --inst_eq_res_simp                      false
% 8.03/1.51  --inst_subs_given                       false
% 8.03/1.51  --inst_orphan_elimination               true
% 8.03/1.51  --inst_learning_loop_flag               true
% 8.03/1.51  --inst_learning_start                   3000
% 8.03/1.51  --inst_learning_factor                  2
% 8.03/1.51  --inst_start_prop_sim_after_learn       3
% 8.03/1.51  --inst_sel_renew                        solver
% 8.03/1.51  --inst_lit_activity_flag                true
% 8.03/1.51  --inst_restr_to_given                   false
% 8.03/1.51  --inst_activity_threshold               500
% 8.03/1.51  --inst_out_proof                        true
% 8.03/1.51  
% 8.03/1.51  ------ Resolution Options
% 8.03/1.51  
% 8.03/1.51  --resolution_flag                       true
% 8.03/1.51  --res_lit_sel                           adaptive
% 8.03/1.51  --res_lit_sel_side                      none
% 8.03/1.51  --res_ordering                          kbo
% 8.03/1.51  --res_to_prop_solver                    active
% 8.03/1.51  --res_prop_simpl_new                    false
% 8.03/1.51  --res_prop_simpl_given                  true
% 8.03/1.51  --res_passive_queue_type                priority_queues
% 8.03/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.03/1.51  --res_passive_queues_freq               [15;5]
% 8.03/1.51  --res_forward_subs                      full
% 8.03/1.51  --res_backward_subs                     full
% 8.03/1.51  --res_forward_subs_resolution           true
% 8.03/1.51  --res_backward_subs_resolution          true
% 8.03/1.51  --res_orphan_elimination                true
% 8.03/1.51  --res_time_limit                        2.
% 8.03/1.51  --res_out_proof                         true
% 8.03/1.51  
% 8.03/1.51  ------ Superposition Options
% 8.03/1.51  
% 8.03/1.51  --superposition_flag                    true
% 8.03/1.51  --sup_passive_queue_type                priority_queues
% 8.03/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.03/1.51  --sup_passive_queues_freq               [8;1;4]
% 8.03/1.51  --demod_completeness_check              fast
% 8.03/1.51  --demod_use_ground                      true
% 8.03/1.51  --sup_to_prop_solver                    passive
% 8.03/1.51  --sup_prop_simpl_new                    true
% 8.03/1.51  --sup_prop_simpl_given                  true
% 8.03/1.51  --sup_fun_splitting                     true
% 8.03/1.51  --sup_smt_interval                      50000
% 8.03/1.51  
% 8.03/1.51  ------ Superposition Simplification Setup
% 8.03/1.51  
% 8.03/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.03/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.03/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.03/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.03/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 8.03/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.03/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.03/1.51  --sup_immed_triv                        [TrivRules]
% 8.03/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.51  --sup_immed_bw_main                     []
% 8.03/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.03/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 8.03/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.51  --sup_input_bw                          []
% 8.03/1.51  
% 8.03/1.51  ------ Combination Options
% 8.03/1.51  
% 8.03/1.51  --comb_res_mult                         3
% 8.03/1.51  --comb_sup_mult                         2
% 8.03/1.51  --comb_inst_mult                        10
% 8.03/1.51  
% 8.03/1.51  ------ Debug Options
% 8.03/1.51  
% 8.03/1.51  --dbg_backtrace                         false
% 8.03/1.51  --dbg_dump_prop_clauses                 false
% 8.03/1.51  --dbg_dump_prop_clauses_file            -
% 8.03/1.51  --dbg_out_stat                          false
% 8.03/1.51  ------ Parsing...
% 8.03/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.03/1.51  
% 8.03/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 8.03/1.51  
% 8.03/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.03/1.51  
% 8.03/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.51  ------ Proving...
% 8.03/1.51  ------ Problem Properties 
% 8.03/1.51  
% 8.03/1.51  
% 8.03/1.51  clauses                                 38
% 8.03/1.51  conjectures                             11
% 8.03/1.51  EPR                                     7
% 8.03/1.51  Horn                                    34
% 8.03/1.51  unary                                   17
% 8.03/1.51  binary                                  2
% 8.03/1.51  lits                                    137
% 8.03/1.51  lits eq                                 31
% 8.03/1.51  fd_pure                                 0
% 8.03/1.51  fd_pseudo                               0
% 8.03/1.51  fd_cond                                 4
% 8.03/1.51  fd_pseudo_cond                          1
% 8.03/1.51  AC symbols                              0
% 8.03/1.51  
% 8.03/1.51  ------ Schedule dynamic 5 is on 
% 8.03/1.51  
% 8.03/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.03/1.51  
% 8.03/1.51  
% 8.03/1.51  ------ 
% 8.03/1.51  Current options:
% 8.03/1.51  ------ 
% 8.03/1.51  
% 8.03/1.51  ------ Input Options
% 8.03/1.51  
% 8.03/1.51  --out_options                           all
% 8.03/1.51  --tptp_safe_out                         true
% 8.03/1.51  --problem_path                          ""
% 8.03/1.51  --include_path                          ""
% 8.03/1.51  --clausifier                            res/vclausify_rel
% 8.03/1.51  --clausifier_options                    ""
% 8.03/1.51  --stdin                                 false
% 8.03/1.51  --stats_out                             all
% 8.03/1.51  
% 8.03/1.51  ------ General Options
% 8.03/1.51  
% 8.03/1.51  --fof                                   false
% 8.03/1.51  --time_out_real                         305.
% 8.03/1.51  --time_out_virtual                      -1.
% 8.03/1.51  --symbol_type_check                     false
% 8.03/1.51  --clausify_out                          false
% 8.03/1.51  --sig_cnt_out                           false
% 8.03/1.51  --trig_cnt_out                          false
% 8.03/1.51  --trig_cnt_out_tolerance                1.
% 8.03/1.51  --trig_cnt_out_sk_spl                   false
% 8.03/1.51  --abstr_cl_out                          false
% 8.03/1.51  
% 8.03/1.51  ------ Global Options
% 8.03/1.51  
% 8.03/1.51  --schedule                              default
% 8.03/1.51  --add_important_lit                     false
% 8.03/1.51  --prop_solver_per_cl                    1000
% 8.03/1.51  --min_unsat_core                        false
% 8.03/1.51  --soft_assumptions                      false
% 8.03/1.51  --soft_lemma_size                       3
% 8.03/1.51  --prop_impl_unit_size                   0
% 8.03/1.51  --prop_impl_unit                        []
% 8.03/1.51  --share_sel_clauses                     true
% 8.03/1.51  --reset_solvers                         false
% 8.03/1.51  --bc_imp_inh                            [conj_cone]
% 8.03/1.51  --conj_cone_tolerance                   3.
% 8.03/1.51  --extra_neg_conj                        none
% 8.03/1.51  --large_theory_mode                     true
% 8.03/1.51  --prolific_symb_bound                   200
% 8.03/1.51  --lt_threshold                          2000
% 8.03/1.51  --clause_weak_htbl                      true
% 8.03/1.51  --gc_record_bc_elim                     false
% 8.03/1.51  
% 8.03/1.51  ------ Preprocessing Options
% 8.03/1.51  
% 8.03/1.51  --preprocessing_flag                    true
% 8.03/1.51  --time_out_prep_mult                    0.1
% 8.03/1.51  --splitting_mode                        input
% 8.03/1.51  --splitting_grd                         true
% 8.03/1.51  --splitting_cvd                         false
% 8.03/1.51  --splitting_cvd_svl                     false
% 8.03/1.51  --splitting_nvd                         32
% 8.03/1.51  --sub_typing                            true
% 8.03/1.51  --prep_gs_sim                           true
% 8.03/1.51  --prep_unflatten                        true
% 8.03/1.51  --prep_res_sim                          true
% 8.03/1.51  --prep_upred                            true
% 8.03/1.51  --prep_sem_filter                       exhaustive
% 8.03/1.51  --prep_sem_filter_out                   false
% 8.03/1.51  --pred_elim                             true
% 8.03/1.51  --res_sim_input                         true
% 8.03/1.51  --eq_ax_congr_red                       true
% 8.03/1.51  --pure_diseq_elim                       true
% 8.03/1.51  --brand_transform                       false
% 8.03/1.51  --non_eq_to_eq                          false
% 8.03/1.51  --prep_def_merge                        true
% 8.03/1.51  --prep_def_merge_prop_impl              false
% 8.03/1.51  --prep_def_merge_mbd                    true
% 8.03/1.51  --prep_def_merge_tr_red                 false
% 8.03/1.51  --prep_def_merge_tr_cl                  false
% 8.03/1.51  --smt_preprocessing                     true
% 8.03/1.51  --smt_ac_axioms                         fast
% 8.03/1.51  --preprocessed_out                      false
% 8.03/1.51  --preprocessed_stats                    false
% 8.03/1.51  
% 8.03/1.51  ------ Abstraction refinement Options
% 8.03/1.51  
% 8.03/1.51  --abstr_ref                             []
% 8.03/1.51  --abstr_ref_prep                        false
% 8.03/1.51  --abstr_ref_until_sat                   false
% 8.03/1.51  --abstr_ref_sig_restrict                funpre
% 8.03/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 8.03/1.51  --abstr_ref_under                       []
% 8.03/1.51  
% 8.03/1.51  ------ SAT Options
% 8.03/1.51  
% 8.03/1.51  --sat_mode                              false
% 8.03/1.51  --sat_fm_restart_options                ""
% 8.03/1.51  --sat_gr_def                            false
% 8.03/1.51  --sat_epr_types                         true
% 8.03/1.51  --sat_non_cyclic_types                  false
% 8.03/1.51  --sat_finite_models                     false
% 8.03/1.51  --sat_fm_lemmas                         false
% 8.03/1.51  --sat_fm_prep                           false
% 8.03/1.51  --sat_fm_uc_incr                        true
% 8.03/1.51  --sat_out_model                         small
% 8.03/1.51  --sat_out_clauses                       false
% 8.03/1.51  
% 8.03/1.51  ------ QBF Options
% 8.03/1.51  
% 8.03/1.51  --qbf_mode                              false
% 8.03/1.51  --qbf_elim_univ                         false
% 8.03/1.51  --qbf_dom_inst                          none
% 8.03/1.51  --qbf_dom_pre_inst                      false
% 8.03/1.51  --qbf_sk_in                             false
% 8.03/1.51  --qbf_pred_elim                         true
% 8.03/1.51  --qbf_split                             512
% 8.03/1.51  
% 8.03/1.51  ------ BMC1 Options
% 8.03/1.51  
% 8.03/1.51  --bmc1_incremental                      false
% 8.03/1.51  --bmc1_axioms                           reachable_all
% 8.03/1.51  --bmc1_min_bound                        0
% 8.03/1.51  --bmc1_max_bound                        -1
% 8.03/1.51  --bmc1_max_bound_default                -1
% 8.03/1.51  --bmc1_symbol_reachability              true
% 8.03/1.51  --bmc1_property_lemmas                  false
% 8.03/1.51  --bmc1_k_induction                      false
% 8.03/1.51  --bmc1_non_equiv_states                 false
% 8.03/1.51  --bmc1_deadlock                         false
% 8.03/1.51  --bmc1_ucm                              false
% 8.03/1.51  --bmc1_add_unsat_core                   none
% 8.03/1.51  --bmc1_unsat_core_children              false
% 8.03/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 8.03/1.51  --bmc1_out_stat                         full
% 8.03/1.51  --bmc1_ground_init                      false
% 8.03/1.51  --bmc1_pre_inst_next_state              false
% 8.03/1.51  --bmc1_pre_inst_state                   false
% 8.03/1.51  --bmc1_pre_inst_reach_state             false
% 8.03/1.51  --bmc1_out_unsat_core                   false
% 8.03/1.51  --bmc1_aig_witness_out                  false
% 8.03/1.51  --bmc1_verbose                          false
% 8.03/1.51  --bmc1_dump_clauses_tptp                false
% 8.03/1.51  --bmc1_dump_unsat_core_tptp             false
% 8.03/1.51  --bmc1_dump_file                        -
% 8.03/1.51  --bmc1_ucm_expand_uc_limit              128
% 8.03/1.51  --bmc1_ucm_n_expand_iterations          6
% 8.03/1.51  --bmc1_ucm_extend_mode                  1
% 8.03/1.51  --bmc1_ucm_init_mode                    2
% 8.03/1.51  --bmc1_ucm_cone_mode                    none
% 8.03/1.51  --bmc1_ucm_reduced_relation_type        0
% 8.03/1.51  --bmc1_ucm_relax_model                  4
% 8.03/1.51  --bmc1_ucm_full_tr_after_sat            true
% 8.03/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 8.03/1.51  --bmc1_ucm_layered_model                none
% 8.03/1.51  --bmc1_ucm_max_lemma_size               10
% 8.03/1.51  
% 8.03/1.51  ------ AIG Options
% 8.03/1.51  
% 8.03/1.51  --aig_mode                              false
% 8.03/1.51  
% 8.03/1.51  ------ Instantiation Options
% 8.03/1.51  
% 8.03/1.51  --instantiation_flag                    true
% 8.03/1.51  --inst_sos_flag                         true
% 8.03/1.51  --inst_sos_phase                        true
% 8.03/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.03/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.03/1.51  --inst_lit_sel_side                     none
% 8.03/1.51  --inst_solver_per_active                1400
% 8.03/1.51  --inst_solver_calls_frac                1.
% 8.03/1.51  --inst_passive_queue_type               priority_queues
% 8.03/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.03/1.51  --inst_passive_queues_freq              [25;2]
% 8.03/1.51  --inst_dismatching                      true
% 8.03/1.51  --inst_eager_unprocessed_to_passive     true
% 8.03/1.51  --inst_prop_sim_given                   true
% 8.03/1.51  --inst_prop_sim_new                     false
% 8.03/1.51  --inst_subs_new                         false
% 8.03/1.51  --inst_eq_res_simp                      false
% 8.03/1.51  --inst_subs_given                       false
% 8.03/1.51  --inst_orphan_elimination               true
% 8.03/1.51  --inst_learning_loop_flag               true
% 8.03/1.51  --inst_learning_start                   3000
% 8.03/1.51  --inst_learning_factor                  2
% 8.03/1.51  --inst_start_prop_sim_after_learn       3
% 8.03/1.51  --inst_sel_renew                        solver
% 8.03/1.51  --inst_lit_activity_flag                true
% 8.03/1.51  --inst_restr_to_given                   false
% 8.03/1.51  --inst_activity_threshold               500
% 8.03/1.51  --inst_out_proof                        true
% 8.03/1.51  
% 8.03/1.51  ------ Resolution Options
% 8.03/1.51  
% 8.03/1.51  --resolution_flag                       false
% 8.03/1.51  --res_lit_sel                           adaptive
% 8.03/1.51  --res_lit_sel_side                      none
% 8.03/1.51  --res_ordering                          kbo
% 8.03/1.51  --res_to_prop_solver                    active
% 8.03/1.51  --res_prop_simpl_new                    false
% 8.03/1.51  --res_prop_simpl_given                  true
% 8.03/1.51  --res_passive_queue_type                priority_queues
% 8.03/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.03/1.51  --res_passive_queues_freq               [15;5]
% 8.03/1.51  --res_forward_subs                      full
% 8.03/1.51  --res_backward_subs                     full
% 8.03/1.51  --res_forward_subs_resolution           true
% 8.03/1.51  --res_backward_subs_resolution          true
% 8.03/1.51  --res_orphan_elimination                true
% 8.03/1.51  --res_time_limit                        2.
% 8.03/1.51  --res_out_proof                         true
% 8.03/1.51  
% 8.03/1.51  ------ Superposition Options
% 8.03/1.51  
% 8.03/1.51  --superposition_flag                    true
% 8.03/1.51  --sup_passive_queue_type                priority_queues
% 8.03/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.03/1.51  --sup_passive_queues_freq               [8;1;4]
% 8.03/1.51  --demod_completeness_check              fast
% 8.03/1.51  --demod_use_ground                      true
% 8.03/1.51  --sup_to_prop_solver                    passive
% 8.03/1.51  --sup_prop_simpl_new                    true
% 8.03/1.51  --sup_prop_simpl_given                  true
% 8.03/1.51  --sup_fun_splitting                     true
% 8.03/1.51  --sup_smt_interval                      50000
% 8.03/1.51  
% 8.03/1.51  ------ Superposition Simplification Setup
% 8.03/1.51  
% 8.03/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.03/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.03/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.03/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.03/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 8.03/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.03/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.03/1.51  --sup_immed_triv                        [TrivRules]
% 8.03/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.51  --sup_immed_bw_main                     []
% 8.03/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.03/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 8.03/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.51  --sup_input_bw                          []
% 8.03/1.51  
% 8.03/1.51  ------ Combination Options
% 8.03/1.51  
% 8.03/1.51  --comb_res_mult                         3
% 8.03/1.51  --comb_sup_mult                         2
% 8.03/1.51  --comb_inst_mult                        10
% 8.03/1.51  
% 8.03/1.51  ------ Debug Options
% 8.03/1.51  
% 8.03/1.51  --dbg_backtrace                         false
% 8.03/1.51  --dbg_dump_prop_clauses                 false
% 8.03/1.51  --dbg_dump_prop_clauses_file            -
% 8.03/1.51  --dbg_out_stat                          false
% 8.03/1.51  
% 8.03/1.51  
% 8.03/1.51  
% 8.03/1.51  
% 8.03/1.51  ------ Proving...
% 8.03/1.51  
% 8.03/1.51  
% 8.03/1.51  % SZS status Theorem for theBenchmark.p
% 8.03/1.51  
% 8.03/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 8.03/1.51  
% 8.03/1.51  fof(f19,conjecture,(
% 8.03/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 8.03/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.51  
% 8.03/1.51  fof(f20,negated_conjecture,(
% 8.03/1.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 8.03/1.51    inference(negated_conjecture,[],[f19])).
% 8.03/1.51  
% 8.03/1.51  fof(f46,plain,(
% 8.03/1.51    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 8.03/1.51    inference(ennf_transformation,[],[f20])).
% 8.03/1.51  
% 8.03/1.51  fof(f47,plain,(
% 8.03/1.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 8.03/1.51    inference(flattening,[],[f46])).
% 8.03/1.51  
% 8.03/1.51  fof(f50,plain,(
% 8.03/1.51    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 8.03/1.51    introduced(choice_axiom,[])).
% 8.03/1.51  
% 8.03/1.51  fof(f49,plain,(
% 8.03/1.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 8.03/1.51    introduced(choice_axiom,[])).
% 8.03/1.51  
% 8.03/1.51  fof(f51,plain,(
% 8.03/1.51    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 8.03/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f50,f49])).
% 8.03/1.51  
% 8.03/1.51  fof(f84,plain,(
% 8.03/1.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 8.03/1.51    inference(cnf_transformation,[],[f51])).
% 8.03/1.51  
% 8.03/1.51  fof(f87,plain,(
% 8.03/1.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 8.03/1.51    inference(cnf_transformation,[],[f51])).
% 8.03/1.51  
% 8.03/1.51  fof(f14,axiom,(
% 8.03/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 8.03/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.51  
% 8.03/1.51  fof(f38,plain,(
% 8.03/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 8.03/1.51    inference(ennf_transformation,[],[f14])).
% 8.03/1.51  
% 8.03/1.51  fof(f39,plain,(
% 8.03/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 8.03/1.51    inference(flattening,[],[f38])).
% 8.03/1.51  
% 8.03/1.51  fof(f73,plain,(
% 8.03/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 8.03/1.51    inference(cnf_transformation,[],[f39])).
% 8.03/1.51  
% 8.03/1.51  fof(f85,plain,(
% 8.03/1.51    v1_funct_1(sK3)),
% 8.03/1.51    inference(cnf_transformation,[],[f51])).
% 8.03/1.51  
% 8.03/1.51  fof(f11,axiom,(
% 8.03/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 8.03/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.51  
% 8.03/1.51  fof(f34,plain,(
% 8.03/1.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 8.03/1.51    inference(ennf_transformation,[],[f11])).
% 8.03/1.51  
% 8.03/1.51  fof(f35,plain,(
% 8.03/1.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.03/1.51    inference(flattening,[],[f34])).
% 8.03/1.51  
% 8.03/1.51  fof(f48,plain,(
% 8.03/1.51    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.03/1.51    inference(nnf_transformation,[],[f35])).
% 8.03/1.51  
% 8.03/1.51  fof(f68,plain,(
% 8.03/1.51    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.03/1.51    inference(cnf_transformation,[],[f48])).
% 8.03/1.51  
% 8.03/1.51  fof(f89,plain,(
% 8.03/1.51    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 8.03/1.51    inference(cnf_transformation,[],[f51])).
% 8.03/1.51  
% 8.03/1.51  fof(f13,axiom,(
% 8.03/1.51    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 8.03/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.51  
% 8.03/1.51  fof(f21,plain,(
% 8.03/1.51    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 8.03/1.51    inference(pure_predicate_removal,[],[f13])).
% 8.03/1.51  
% 8.03/1.51  fof(f72,plain,(
% 8.03/1.51    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 8.03/1.51    inference(cnf_transformation,[],[f21])).
% 8.03/1.51  
% 8.03/1.51  fof(f82,plain,(
% 8.03/1.51    v1_funct_1(sK2)),
% 8.03/1.51    inference(cnf_transformation,[],[f51])).
% 8.03/1.51  
% 8.03/1.51  fof(f12,axiom,(
% 8.03/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 8.03/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.51  
% 8.03/1.51  fof(f36,plain,(
% 8.03/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 8.03/1.51    inference(ennf_transformation,[],[f12])).
% 8.03/1.51  
% 8.03/1.51  fof(f37,plain,(
% 8.03/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 8.03/1.51    inference(flattening,[],[f36])).
% 8.03/1.51  
% 8.03/1.51  fof(f71,plain,(
% 8.03/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 8.03/1.51    inference(cnf_transformation,[],[f37])).
% 8.03/1.51  
% 8.03/1.51  fof(f10,axiom,(
% 8.03/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 8.03/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.51  
% 8.03/1.51  fof(f32,plain,(
% 8.03/1.51    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.03/1.51    inference(ennf_transformation,[],[f10])).
% 8.03/1.51  
% 8.03/1.51  fof(f33,plain,(
% 8.03/1.51    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.03/1.51    inference(flattening,[],[f32])).
% 8.03/1.51  
% 8.03/1.51  fof(f67,plain,(
% 8.03/1.51    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.51    inference(cnf_transformation,[],[f33])).
% 8.03/1.51  
% 8.03/1.51  fof(f15,axiom,(
% 8.03/1.51    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 8.03/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.51  
% 8.03/1.51  fof(f74,plain,(
% 8.03/1.51    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 8.03/1.51    inference(cnf_transformation,[],[f15])).
% 8.03/1.51  
% 8.03/1.51  fof(f100,plain,(
% 8.03/1.51    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.51    inference(definition_unfolding,[],[f67,f74])).
% 8.03/1.51  
% 8.03/1.51  fof(f88,plain,(
% 8.03/1.51    k2_relset_1(sK0,sK1,sK2) = sK1),
% 8.03/1.51    inference(cnf_transformation,[],[f51])).
% 8.03/1.51  
% 8.03/1.51  fof(f18,axiom,(
% 8.03/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 8.03/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.51  
% 8.03/1.51  fof(f44,plain,(
% 8.03/1.51    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 8.03/1.51    inference(ennf_transformation,[],[f18])).
% 8.03/1.51  
% 8.03/1.51  fof(f45,plain,(
% 8.03/1.51    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 8.03/1.51    inference(flattening,[],[f44])).
% 8.03/1.51  
% 8.03/1.51  fof(f81,plain,(
% 8.03/1.51    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 8.03/1.51    inference(cnf_transformation,[],[f45])).
% 8.03/1.51  
% 8.03/1.51  fof(f5,axiom,(
% 8.03/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 8.03/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.51  
% 8.03/1.51  fof(f24,plain,(
% 8.03/1.51    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.03/1.51    inference(ennf_transformation,[],[f5])).
% 8.03/1.51  
% 8.03/1.51  fof(f25,plain,(
% 8.03/1.51    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.03/1.51    inference(flattening,[],[f24])).
% 8.03/1.51  
% 8.03/1.51  fof(f57,plain,(
% 8.03/1.51    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.51    inference(cnf_transformation,[],[f25])).
% 8.03/1.51  
% 8.03/1.51  fof(f90,plain,(
% 8.03/1.51    v2_funct_1(sK2)),
% 8.03/1.51    inference(cnf_transformation,[],[f51])).
% 8.03/1.51  
% 8.03/1.51  fof(f2,axiom,(
% 8.03/1.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 8.03/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.51  
% 8.03/1.51  fof(f53,plain,(
% 8.03/1.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 8.03/1.51    inference(cnf_transformation,[],[f2])).
% 8.03/1.51  
% 8.03/1.51  fof(f1,axiom,(
% 8.03/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 8.03/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.51  
% 8.03/1.51  fof(f22,plain,(
% 8.03/1.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 8.03/1.51    inference(ennf_transformation,[],[f1])).
% 8.03/1.51  
% 8.03/1.51  fof(f52,plain,(
% 8.03/1.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 8.03/1.51    inference(cnf_transformation,[],[f22])).
% 8.03/1.51  
% 8.03/1.51  fof(f83,plain,(
% 8.03/1.51    v1_funct_2(sK2,sK0,sK1)),
% 8.03/1.51    inference(cnf_transformation,[],[f51])).
% 8.03/1.51  
% 8.03/1.51  fof(f92,plain,(
% 8.03/1.51    k1_xboole_0 != sK1),
% 8.03/1.51    inference(cnf_transformation,[],[f51])).
% 8.03/1.51  
% 8.03/1.51  fof(f9,axiom,(
% 8.03/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 8.03/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.51  
% 8.03/1.51  fof(f30,plain,(
% 8.03/1.51    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.03/1.51    inference(ennf_transformation,[],[f9])).
% 8.03/1.51  
% 8.03/1.51  fof(f31,plain,(
% 8.03/1.51    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.03/1.51    inference(flattening,[],[f30])).
% 8.03/1.51  
% 8.03/1.51  fof(f66,plain,(
% 8.03/1.51    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.51    inference(cnf_transformation,[],[f31])).
% 8.03/1.51  
% 8.03/1.51  fof(f98,plain,(
% 8.03/1.51    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.51    inference(definition_unfolding,[],[f66,f74])).
% 8.03/1.51  
% 8.03/1.51  fof(f4,axiom,(
% 8.03/1.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 8.03/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.52  
% 8.03/1.52  fof(f56,plain,(
% 8.03/1.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 8.03/1.52    inference(cnf_transformation,[],[f4])).
% 8.03/1.52  
% 8.03/1.52  fof(f94,plain,(
% 8.03/1.52    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 8.03/1.52    inference(definition_unfolding,[],[f56,f74])).
% 8.03/1.52  
% 8.03/1.52  fof(f7,axiom,(
% 8.03/1.52    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 8.03/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.52  
% 8.03/1.52  fof(f61,plain,(
% 8.03/1.52    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 8.03/1.52    inference(cnf_transformation,[],[f7])).
% 8.03/1.52  
% 8.03/1.52  fof(f96,plain,(
% 8.03/1.52    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 8.03/1.52    inference(definition_unfolding,[],[f61,f74])).
% 8.03/1.52  
% 8.03/1.52  fof(f17,axiom,(
% 8.03/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 8.03/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.52  
% 8.03/1.52  fof(f42,plain,(
% 8.03/1.52    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 8.03/1.52    inference(ennf_transformation,[],[f17])).
% 8.03/1.52  
% 8.03/1.52  fof(f43,plain,(
% 8.03/1.52    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 8.03/1.52    inference(flattening,[],[f42])).
% 8.03/1.52  
% 8.03/1.52  fof(f78,plain,(
% 8.03/1.52    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 8.03/1.52    inference(cnf_transformation,[],[f43])).
% 8.03/1.52  
% 8.03/1.52  fof(f86,plain,(
% 8.03/1.52    v1_funct_2(sK3,sK1,sK0)),
% 8.03/1.52    inference(cnf_transformation,[],[f51])).
% 8.03/1.52  
% 8.03/1.52  fof(f91,plain,(
% 8.03/1.52    k1_xboole_0 != sK0),
% 8.03/1.52    inference(cnf_transformation,[],[f51])).
% 8.03/1.52  
% 8.03/1.52  fof(f16,axiom,(
% 8.03/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 8.03/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.52  
% 8.03/1.52  fof(f40,plain,(
% 8.03/1.52    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 8.03/1.52    inference(ennf_transformation,[],[f16])).
% 8.03/1.52  
% 8.03/1.52  fof(f41,plain,(
% 8.03/1.52    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 8.03/1.52    inference(flattening,[],[f40])).
% 8.03/1.52  
% 8.03/1.52  fof(f75,plain,(
% 8.03/1.52    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 8.03/1.52    inference(cnf_transformation,[],[f41])).
% 8.03/1.52  
% 8.03/1.52  fof(f80,plain,(
% 8.03/1.52    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 8.03/1.52    inference(cnf_transformation,[],[f45])).
% 8.03/1.52  
% 8.03/1.52  fof(f65,plain,(
% 8.03/1.52    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.52    inference(cnf_transformation,[],[f31])).
% 8.03/1.52  
% 8.03/1.52  fof(f99,plain,(
% 8.03/1.52    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.52    inference(definition_unfolding,[],[f65,f74])).
% 8.03/1.52  
% 8.03/1.52  fof(f6,axiom,(
% 8.03/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 8.03/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.52  
% 8.03/1.52  fof(f26,plain,(
% 8.03/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.03/1.52    inference(ennf_transformation,[],[f6])).
% 8.03/1.52  
% 8.03/1.52  fof(f27,plain,(
% 8.03/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.03/1.52    inference(flattening,[],[f26])).
% 8.03/1.52  
% 8.03/1.52  fof(f59,plain,(
% 8.03/1.52    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.52    inference(cnf_transformation,[],[f27])).
% 8.03/1.52  
% 8.03/1.52  fof(f58,plain,(
% 8.03/1.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.52    inference(cnf_transformation,[],[f27])).
% 8.03/1.52  
% 8.03/1.52  fof(f3,axiom,(
% 8.03/1.52    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 8.03/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.52  
% 8.03/1.52  fof(f23,plain,(
% 8.03/1.52    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 8.03/1.52    inference(ennf_transformation,[],[f3])).
% 8.03/1.52  
% 8.03/1.52  fof(f54,plain,(
% 8.03/1.52    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 8.03/1.52    inference(cnf_transformation,[],[f23])).
% 8.03/1.52  
% 8.03/1.52  fof(f8,axiom,(
% 8.03/1.52    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 8.03/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.52  
% 8.03/1.52  fof(f28,plain,(
% 8.03/1.52    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.03/1.52    inference(ennf_transformation,[],[f8])).
% 8.03/1.52  
% 8.03/1.52  fof(f29,plain,(
% 8.03/1.52    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.03/1.52    inference(flattening,[],[f28])).
% 8.03/1.52  
% 8.03/1.52  fof(f64,plain,(
% 8.03/1.52    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.52    inference(cnf_transformation,[],[f29])).
% 8.03/1.52  
% 8.03/1.52  fof(f93,plain,(
% 8.03/1.52    k2_funct_1(sK2) != sK3),
% 8.03/1.52    inference(cnf_transformation,[],[f51])).
% 8.03/1.52  
% 8.03/1.52  cnf(c_38,negated_conjecture,
% 8.03/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 8.03/1.52      inference(cnf_transformation,[],[f84]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1241,plain,
% 8.03/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_35,negated_conjecture,
% 8.03/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 8.03/1.52      inference(cnf_transformation,[],[f87]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1244,plain,
% 8.03/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_21,plain,
% 8.03/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 8.03/1.52      | ~ v1_funct_1(X0)
% 8.03/1.52      | ~ v1_funct_1(X3)
% 8.03/1.52      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 8.03/1.52      inference(cnf_transformation,[],[f73]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1252,plain,
% 8.03/1.52      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 8.03/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 8.03/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.03/1.52      | v1_funct_1(X5) != iProver_top
% 8.03/1.52      | v1_funct_1(X4) != iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_4769,plain,
% 8.03/1.52      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 8.03/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.03/1.52      | v1_funct_1(X2) != iProver_top
% 8.03/1.52      | v1_funct_1(sK3) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1244,c_1252]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_37,negated_conjecture,
% 8.03/1.52      ( v1_funct_1(sK3) ),
% 8.03/1.52      inference(cnf_transformation,[],[f85]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_44,plain,
% 8.03/1.52      ( v1_funct_1(sK3) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_4823,plain,
% 8.03/1.52      ( v1_funct_1(X2) != iProver_top
% 8.03/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.03/1.52      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_4769,c_44]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_4824,plain,
% 8.03/1.52      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 8.03/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.03/1.52      | v1_funct_1(X2) != iProver_top ),
% 8.03/1.52      inference(renaming,[status(thm)],[c_4823]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_4832,plain,
% 8.03/1.52      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 8.03/1.52      | v1_funct_1(sK2) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1241,c_4824]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_17,plain,
% 8.03/1.52      ( ~ r2_relset_1(X0,X1,X2,X3)
% 8.03/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.03/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.03/1.52      | X2 = X3 ),
% 8.03/1.52      inference(cnf_transformation,[],[f68]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_33,negated_conjecture,
% 8.03/1.52      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 8.03/1.52      inference(cnf_transformation,[],[f89]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_429,plain,
% 8.03/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.52      | X3 = X0
% 8.03/1.52      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 8.03/1.52      | k6_partfun1(sK0) != X3
% 8.03/1.52      | sK0 != X2
% 8.03/1.52      | sK0 != X1 ),
% 8.03/1.52      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_430,plain,
% 8.03/1.52      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.03/1.52      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.03/1.52      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.03/1.52      inference(unflattening,[status(thm)],[c_429]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_20,plain,
% 8.03/1.52      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 8.03/1.52      inference(cnf_transformation,[],[f72]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_438,plain,
% 8.03/1.52      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.03/1.52      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.03/1.52      inference(forward_subsumption_resolution,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_430,c_20]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1237,plain,
% 8.03/1.52      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.03/1.52      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_40,negated_conjecture,
% 8.03/1.52      ( v1_funct_1(sK2) ),
% 8.03/1.52      inference(cnf_transformation,[],[f82]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_18,plain,
% 8.03/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 8.03/1.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 8.03/1.52      | ~ v1_funct_1(X0)
% 8.03/1.52      | ~ v1_funct_1(X3) ),
% 8.03/1.52      inference(cnf_transformation,[],[f71]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1354,plain,
% 8.03/1.52      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.03/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 8.03/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 8.03/1.52      | ~ v1_funct_1(sK3)
% 8.03/1.52      | ~ v1_funct_1(sK2) ),
% 8.03/1.52      inference(instantiation,[status(thm)],[c_18]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1989,plain,
% 8.03/1.52      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_1237,c_40,c_38,c_37,c_35,c_438,c_1354]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_4833,plain,
% 8.03/1.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 8.03/1.52      | v1_funct_1(sK2) != iProver_top ),
% 8.03/1.52      inference(light_normalisation,[status(thm)],[c_4832,c_1989]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_41,plain,
% 8.03/1.52      ( v1_funct_1(sK2) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_5271,plain,
% 8.03/1.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_4833,c_41]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_15,plain,
% 8.03/1.52      ( ~ v1_funct_1(X0)
% 8.03/1.52      | ~ v1_funct_1(X1)
% 8.03/1.52      | ~ v2_funct_1(X0)
% 8.03/1.52      | ~ v1_relat_1(X0)
% 8.03/1.52      | ~ v1_relat_1(X1)
% 8.03/1.52      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 8.03/1.52      | k2_funct_1(X0) = X1
% 8.03/1.52      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 8.03/1.52      inference(cnf_transformation,[],[f100]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1256,plain,
% 8.03/1.52      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 8.03/1.52      | k2_funct_1(X1) = X0
% 8.03/1.52      | k1_relat_1(X1) != k2_relat_1(X0)
% 8.03/1.52      | v1_funct_1(X1) != iProver_top
% 8.03/1.52      | v1_funct_1(X0) != iProver_top
% 8.03/1.52      | v2_funct_1(X1) != iProver_top
% 8.03/1.52      | v1_relat_1(X1) != iProver_top
% 8.03/1.52      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_5273,plain,
% 8.03/1.52      ( k2_funct_1(sK3) = sK2
% 8.03/1.52      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 8.03/1.52      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 8.03/1.52      | v1_funct_1(sK3) != iProver_top
% 8.03/1.52      | v1_funct_1(sK2) != iProver_top
% 8.03/1.52      | v2_funct_1(sK3) != iProver_top
% 8.03/1.52      | v1_relat_1(sK3) != iProver_top
% 8.03/1.52      | v1_relat_1(sK2) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_5271,c_1256]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_34,negated_conjecture,
% 8.03/1.52      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 8.03/1.52      inference(cnf_transformation,[],[f88]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_27,plain,
% 8.03/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 8.03/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.52      | ~ v1_funct_1(X0)
% 8.03/1.52      | ~ v2_funct_1(X0)
% 8.03/1.52      | k2_relset_1(X1,X2,X0) != X2
% 8.03/1.52      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 8.03/1.52      | k1_xboole_0 = X2 ),
% 8.03/1.52      inference(cnf_transformation,[],[f81]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1247,plain,
% 8.03/1.52      ( k2_relset_1(X0,X1,X2) != X1
% 8.03/1.52      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 8.03/1.52      | k1_xboole_0 = X1
% 8.03/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 8.03/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.03/1.52      | v1_funct_1(X2) != iProver_top
% 8.03/1.52      | v2_funct_1(X2) != iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3600,plain,
% 8.03/1.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 8.03/1.52      | sK1 = k1_xboole_0
% 8.03/1.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 8.03/1.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 8.03/1.52      | v1_funct_1(sK2) != iProver_top
% 8.03/1.52      | v2_funct_1(sK2) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_34,c_1247]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1239,plain,
% 8.03/1.52      ( v1_funct_1(sK2) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_5,plain,
% 8.03/1.52      ( ~ v1_funct_1(X0)
% 8.03/1.52      | ~ v2_funct_1(X0)
% 8.03/1.52      | ~ v1_relat_1(X0)
% 8.03/1.52      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 8.03/1.52      inference(cnf_transformation,[],[f57]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1264,plain,
% 8.03/1.52      ( k2_funct_1(X0) = k4_relat_1(X0)
% 8.03/1.52      | v1_funct_1(X0) != iProver_top
% 8.03/1.52      | v2_funct_1(X0) != iProver_top
% 8.03/1.52      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3208,plain,
% 8.03/1.52      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 8.03/1.52      | v2_funct_1(sK2) != iProver_top
% 8.03/1.52      | v1_relat_1(sK2) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1239,c_1264]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_32,negated_conjecture,
% 8.03/1.52      ( v2_funct_1(sK2) ),
% 8.03/1.52      inference(cnf_transformation,[],[f90]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_48,plain,
% 8.03/1.52      ( v2_funct_1(sK2) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1,plain,
% 8.03/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 8.03/1.52      inference(cnf_transformation,[],[f53]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1266,plain,
% 8.03/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_0,plain,
% 8.03/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.03/1.52      | ~ v1_relat_1(X1)
% 8.03/1.52      | v1_relat_1(X0) ),
% 8.03/1.52      inference(cnf_transformation,[],[f52]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1267,plain,
% 8.03/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.03/1.52      | v1_relat_1(X1) != iProver_top
% 8.03/1.52      | v1_relat_1(X0) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_2262,plain,
% 8.03/1.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 8.03/1.52      | v1_relat_1(sK2) = iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1241,c_1267]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_2289,plain,
% 8.03/1.52      ( v1_relat_1(sK2) = iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1266,c_2262]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3310,plain,
% 8.03/1.52      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_3208,c_48,c_2289]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3602,plain,
% 8.03/1.52      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1)
% 8.03/1.52      | sK1 = k1_xboole_0
% 8.03/1.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 8.03/1.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 8.03/1.52      | v1_funct_1(sK2) != iProver_top
% 8.03/1.52      | v2_funct_1(sK2) != iProver_top ),
% 8.03/1.52      inference(light_normalisation,[status(thm)],[c_3600,c_3310]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_39,negated_conjecture,
% 8.03/1.52      ( v1_funct_2(sK2,sK0,sK1) ),
% 8.03/1.52      inference(cnf_transformation,[],[f83]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_42,plain,
% 8.03/1.52      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_43,plain,
% 8.03/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_30,negated_conjecture,
% 8.03/1.52      ( k1_xboole_0 != sK1 ),
% 8.03/1.52      inference(cnf_transformation,[],[f92]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_713,plain,( X0 = X0 ),theory(equality) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_746,plain,
% 8.03/1.52      ( k1_xboole_0 = k1_xboole_0 ),
% 8.03/1.52      inference(instantiation,[status(thm)],[c_713]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_714,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1332,plain,
% 8.03/1.52      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 8.03/1.52      inference(instantiation,[status(thm)],[c_714]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1333,plain,
% 8.03/1.52      ( sK1 != k1_xboole_0
% 8.03/1.52      | k1_xboole_0 = sK1
% 8.03/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 8.03/1.52      inference(instantiation,[status(thm)],[c_1332]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_5087,plain,
% 8.03/1.52      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_3602,c_41,c_42,c_43,c_48,c_30,c_746,c_1333]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_13,plain,
% 8.03/1.52      ( ~ v1_funct_1(X0)
% 8.03/1.52      | ~ v2_funct_1(X0)
% 8.03/1.52      | ~ v1_relat_1(X0)
% 8.03/1.52      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 8.03/1.52      inference(cnf_transformation,[],[f98]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1258,plain,
% 8.03/1.52      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 8.03/1.52      | v1_funct_1(X0) != iProver_top
% 8.03/1.52      | v2_funct_1(X0) != iProver_top
% 8.03/1.52      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3256,plain,
% 8.03/1.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 8.03/1.52      | v2_funct_1(sK2) != iProver_top
% 8.03/1.52      | v1_relat_1(sK2) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1239,c_1258]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_4819,plain,
% 8.03/1.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_3256,c_48,c_2289]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_4821,plain,
% 8.03/1.52      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 8.03/1.52      inference(light_normalisation,[status(thm)],[c_4819,c_3310]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_5089,plain,
% 8.03/1.52      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
% 8.03/1.52      inference(demodulation,[status(thm)],[c_5087,c_4821]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3,plain,
% 8.03/1.52      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 8.03/1.52      inference(cnf_transformation,[],[f94]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_5095,plain,
% 8.03/1.52      ( k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2) ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_5089,c_3]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_5096,plain,
% 8.03/1.52      ( k2_relat_1(sK2) = sK1 ),
% 8.03/1.52      inference(demodulation,[status(thm)],[c_5095,c_3]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_5274,plain,
% 8.03/1.52      ( k2_funct_1(sK3) = sK2
% 8.03/1.52      | k1_relat_1(sK3) != sK1
% 8.03/1.52      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 8.03/1.52      | v1_funct_1(sK3) != iProver_top
% 8.03/1.52      | v1_funct_1(sK2) != iProver_top
% 8.03/1.52      | v2_funct_1(sK3) != iProver_top
% 8.03/1.52      | v1_relat_1(sK3) != iProver_top
% 8.03/1.52      | v1_relat_1(sK2) != iProver_top ),
% 8.03/1.52      inference(light_normalisation,[status(thm)],[c_5273,c_5096]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_2261,plain,
% 8.03/1.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 8.03/1.52      | v1_relat_1(sK3) = iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1244,c_1267]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_2286,plain,
% 8.03/1.52      ( v1_relat_1(sK3) = iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1266,c_2261]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_8,plain,
% 8.03/1.52      ( v2_funct_1(k6_partfun1(X0)) ),
% 8.03/1.52      inference(cnf_transformation,[],[f96]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1261,plain,
% 8.03/1.52      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_24,plain,
% 8.03/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 8.03/1.52      | ~ v1_funct_2(X3,X4,X1)
% 8.03/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 8.03/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.52      | ~ v1_funct_1(X0)
% 8.03/1.52      | ~ v1_funct_1(X3)
% 8.03/1.52      | v2_funct_1(X0)
% 8.03/1.52      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 8.03/1.52      | k2_relset_1(X4,X1,X3) != X1
% 8.03/1.52      | k1_xboole_0 = X2 ),
% 8.03/1.52      inference(cnf_transformation,[],[f78]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1250,plain,
% 8.03/1.52      ( k2_relset_1(X0,X1,X2) != X1
% 8.03/1.52      | k1_xboole_0 = X3
% 8.03/1.52      | v1_funct_2(X4,X1,X3) != iProver_top
% 8.03/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 8.03/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 8.03/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.03/1.52      | v1_funct_1(X4) != iProver_top
% 8.03/1.52      | v1_funct_1(X2) != iProver_top
% 8.03/1.52      | v2_funct_1(X4) = iProver_top
% 8.03/1.52      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_5508,plain,
% 8.03/1.52      ( k1_xboole_0 = X0
% 8.03/1.52      | v1_funct_2(X1,sK1,X0) != iProver_top
% 8.03/1.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 8.03/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 8.03/1.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 8.03/1.52      | v1_funct_1(X1) != iProver_top
% 8.03/1.52      | v1_funct_1(sK2) != iProver_top
% 8.03/1.52      | v2_funct_1(X1) = iProver_top
% 8.03/1.52      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_34,c_1250]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_5570,plain,
% 8.03/1.52      ( v1_funct_1(X1) != iProver_top
% 8.03/1.52      | v1_funct_2(X1,sK1,X0) != iProver_top
% 8.03/1.52      | k1_xboole_0 = X0
% 8.03/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 8.03/1.52      | v2_funct_1(X1) = iProver_top
% 8.03/1.52      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_5508,c_41,c_42,c_43]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_5571,plain,
% 8.03/1.52      ( k1_xboole_0 = X0
% 8.03/1.52      | v1_funct_2(X1,sK1,X0) != iProver_top
% 8.03/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 8.03/1.52      | v1_funct_1(X1) != iProver_top
% 8.03/1.52      | v2_funct_1(X1) = iProver_top
% 8.03/1.52      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 8.03/1.52      inference(renaming,[status(thm)],[c_5570]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_5574,plain,
% 8.03/1.52      ( sK0 = k1_xboole_0
% 8.03/1.52      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 8.03/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 8.03/1.52      | v1_funct_1(sK3) != iProver_top
% 8.03/1.52      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 8.03/1.52      | v2_funct_1(sK3) = iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1989,c_5571]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_36,negated_conjecture,
% 8.03/1.52      ( v1_funct_2(sK3,sK1,sK0) ),
% 8.03/1.52      inference(cnf_transformation,[],[f86]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_45,plain,
% 8.03/1.52      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_46,plain,
% 8.03/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_31,negated_conjecture,
% 8.03/1.52      ( k1_xboole_0 != sK0 ),
% 8.03/1.52      inference(cnf_transformation,[],[f91]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1352,plain,
% 8.03/1.52      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 8.03/1.52      inference(instantiation,[status(thm)],[c_714]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1353,plain,
% 8.03/1.52      ( sK0 != k1_xboole_0
% 8.03/1.52      | k1_xboole_0 = sK0
% 8.03/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 8.03/1.52      inference(instantiation,[status(thm)],[c_1352]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_6068,plain,
% 8.03/1.52      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 8.03/1.52      | v2_funct_1(sK3) = iProver_top ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_5574,c_44,c_45,c_46,c_31,c_746,c_1353]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_6072,plain,
% 8.03/1.52      ( v2_funct_1(sK3) = iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1261,c_6068]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_22,plain,
% 8.03/1.52      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 8.03/1.52      | ~ v1_funct_2(X2,X0,X1)
% 8.03/1.52      | ~ v1_funct_2(X3,X1,X0)
% 8.03/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.03/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 8.03/1.52      | ~ v1_funct_1(X3)
% 8.03/1.52      | ~ v1_funct_1(X2)
% 8.03/1.52      | k2_relset_1(X1,X0,X3) = X0 ),
% 8.03/1.52      inference(cnf_transformation,[],[f75]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_442,plain,
% 8.03/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 8.03/1.52      | ~ v1_funct_2(X3,X2,X1)
% 8.03/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 8.03/1.52      | ~ v1_funct_1(X3)
% 8.03/1.52      | ~ v1_funct_1(X0)
% 8.03/1.52      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.03/1.52      | k2_relset_1(X2,X1,X3) = X1
% 8.03/1.52      | k6_partfun1(X1) != k6_partfun1(sK0)
% 8.03/1.52      | sK0 != X1 ),
% 8.03/1.52      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_443,plain,
% 8.03/1.52      ( ~ v1_funct_2(X0,X1,sK0)
% 8.03/1.52      | ~ v1_funct_2(X2,sK0,X1)
% 8.03/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 8.03/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 8.03/1.52      | ~ v1_funct_1(X2)
% 8.03/1.52      | ~ v1_funct_1(X0)
% 8.03/1.52      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.03/1.52      | k2_relset_1(X1,sK0,X0) = sK0
% 8.03/1.52      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 8.03/1.52      inference(unflattening,[status(thm)],[c_442]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_529,plain,
% 8.03/1.52      ( ~ v1_funct_2(X0,X1,sK0)
% 8.03/1.52      | ~ v1_funct_2(X2,sK0,X1)
% 8.03/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 8.03/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 8.03/1.52      | ~ v1_funct_1(X0)
% 8.03/1.52      | ~ v1_funct_1(X2)
% 8.03/1.52      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.03/1.52      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 8.03/1.52      inference(equality_resolution_simp,[status(thm)],[c_443]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1236,plain,
% 8.03/1.52      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.03/1.52      | k2_relset_1(X0,sK0,X2) = sK0
% 8.03/1.52      | v1_funct_2(X2,X0,sK0) != iProver_top
% 8.03/1.52      | v1_funct_2(X1,sK0,X0) != iProver_top
% 8.03/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 8.03/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 8.03/1.52      | v1_funct_1(X2) != iProver_top
% 8.03/1.52      | v1_funct_1(X1) != iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1792,plain,
% 8.03/1.52      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 8.03/1.52      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 8.03/1.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 8.03/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 8.03/1.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 8.03/1.52      | v1_funct_1(sK3) != iProver_top
% 8.03/1.52      | v1_funct_1(sK2) != iProver_top ),
% 8.03/1.52      inference(equality_resolution,[status(thm)],[c_1236]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1996,plain,
% 8.03/1.52      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_1792,c_41,c_42,c_43,c_44,c_45,c_46]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_28,plain,
% 8.03/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 8.03/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.52      | ~ v1_funct_1(X0)
% 8.03/1.52      | ~ v2_funct_1(X0)
% 8.03/1.52      | k2_relset_1(X1,X2,X0) != X2
% 8.03/1.52      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 8.03/1.52      | k1_xboole_0 = X2 ),
% 8.03/1.52      inference(cnf_transformation,[],[f80]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1246,plain,
% 8.03/1.52      ( k2_relset_1(X0,X1,X2) != X1
% 8.03/1.52      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 8.03/1.52      | k1_xboole_0 = X1
% 8.03/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 8.03/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.03/1.52      | v1_funct_1(X2) != iProver_top
% 8.03/1.52      | v2_funct_1(X2) != iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_2920,plain,
% 8.03/1.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 8.03/1.52      | sK0 = k1_xboole_0
% 8.03/1.52      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 8.03/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 8.03/1.52      | v1_funct_1(sK3) != iProver_top
% 8.03/1.52      | v2_funct_1(sK3) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1996,c_1246]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_6847,plain,
% 8.03/1.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_2920,c_44,c_45,c_46,c_31,c_746,c_1353,c_6072]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1242,plain,
% 8.03/1.52      ( v1_funct_1(sK3) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3207,plain,
% 8.03/1.52      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 8.03/1.52      | v2_funct_1(sK3) != iProver_top
% 8.03/1.52      | v1_relat_1(sK3) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1242,c_1264]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3305,plain,
% 8.03/1.52      ( v2_funct_1(sK3) != iProver_top
% 8.03/1.52      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_3207,c_2286]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3306,plain,
% 8.03/1.52      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 8.03/1.52      | v2_funct_1(sK3) != iProver_top ),
% 8.03/1.52      inference(renaming,[status(thm)],[c_3305]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_6077,plain,
% 8.03/1.52      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_6072,c_3306]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_14,plain,
% 8.03/1.52      ( ~ v1_funct_1(X0)
% 8.03/1.52      | ~ v2_funct_1(X0)
% 8.03/1.52      | ~ v1_relat_1(X0)
% 8.03/1.52      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 8.03/1.52      inference(cnf_transformation,[],[f99]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1257,plain,
% 8.03/1.52      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 8.03/1.52      | v1_funct_1(X0) != iProver_top
% 8.03/1.52      | v2_funct_1(X0) != iProver_top
% 8.03/1.52      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3216,plain,
% 8.03/1.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 8.03/1.52      | v2_funct_1(sK3) != iProver_top
% 8.03/1.52      | v1_relat_1(sK3) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1242,c_1257]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3435,plain,
% 8.03/1.52      ( v2_funct_1(sK3) != iProver_top
% 8.03/1.52      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_3216,c_2286]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3436,plain,
% 8.03/1.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 8.03/1.52      | v2_funct_1(sK3) != iProver_top ),
% 8.03/1.52      inference(renaming,[status(thm)],[c_3435]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_6076,plain,
% 8.03/1.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_6072,c_3436]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_6078,plain,
% 8.03/1.52      ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 8.03/1.52      inference(demodulation,[status(thm)],[c_6076,c_6077]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_6849,plain,
% 8.03/1.52      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
% 8.03/1.52      inference(light_normalisation,[status(thm)],[c_6847,c_6077,c_6078]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_6857,plain,
% 8.03/1.52      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_6849,c_3]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_6858,plain,
% 8.03/1.52      ( k1_relat_1(sK3) = sK1 ),
% 8.03/1.52      inference(demodulation,[status(thm)],[c_6857,c_3]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3601,plain,
% 8.03/1.52      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
% 8.03/1.52      | sK0 = k1_xboole_0
% 8.03/1.52      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 8.03/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 8.03/1.52      | v1_funct_1(sK3) != iProver_top
% 8.03/1.52      | v2_funct_1(sK3) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1996,c_1247]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_10274,plain,
% 8.03/1.52      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_3601,c_44,c_45,c_46,c_31,c_746,c_1353,c_6072]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3255,plain,
% 8.03/1.52      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3))
% 8.03/1.52      | v2_funct_1(sK3) != iProver_top
% 8.03/1.52      | v1_relat_1(sK3) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1242,c_1258]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3591,plain,
% 8.03/1.52      ( v2_funct_1(sK3) != iProver_top
% 8.03/1.52      | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3)) ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_3255,c_2286]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3592,plain,
% 8.03/1.52      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3))
% 8.03/1.52      | v2_funct_1(sK3) != iProver_top ),
% 8.03/1.52      inference(renaming,[status(thm)],[c_3591]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_6075,plain,
% 8.03/1.52      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3)) ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_6072,c_3592]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_6079,plain,
% 8.03/1.52      ( k5_relat_1(k4_relat_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3)) ),
% 8.03/1.52      inference(demodulation,[status(thm)],[c_6075,c_6077]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_10276,plain,
% 8.03/1.52      ( k6_partfun1(k2_relat_1(sK3)) = k6_partfun1(sK0) ),
% 8.03/1.52      inference(light_normalisation,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_10274,c_6077,c_6079]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_16665,plain,
% 8.03/1.52      ( k2_funct_1(sK3) = sK2 ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_5274,c_41,c_44,c_2286,c_2289,c_6072,c_6858,c_10276]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_16667,plain,
% 8.03/1.52      ( k4_relat_1(sK3) = sK2 ),
% 8.03/1.52      inference(demodulation,[status(thm)],[c_16665,c_6077]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_6,plain,
% 8.03/1.52      ( ~ v1_funct_1(X0)
% 8.03/1.52      | v1_funct_1(k2_funct_1(X0))
% 8.03/1.52      | ~ v1_relat_1(X0) ),
% 8.03/1.52      inference(cnf_transformation,[],[f59]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1263,plain,
% 8.03/1.52      ( v1_funct_1(X0) != iProver_top
% 8.03/1.52      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 8.03/1.52      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_3206,plain,
% 8.03/1.52      ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
% 8.03/1.52      | v1_funct_1(X0) != iProver_top
% 8.03/1.52      | v2_funct_1(k2_funct_1(X0)) != iProver_top
% 8.03/1.52      | v1_relat_1(X0) != iProver_top
% 8.03/1.52      | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_1263,c_1264]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_7,plain,
% 8.03/1.52      ( ~ v1_funct_1(X0)
% 8.03/1.52      | ~ v1_relat_1(X0)
% 8.03/1.52      | v1_relat_1(k2_funct_1(X0)) ),
% 8.03/1.52      inference(cnf_transformation,[],[f58]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_108,plain,
% 8.03/1.52      ( v1_funct_1(X0) != iProver_top
% 8.03/1.52      | v1_relat_1(X0) != iProver_top
% 8.03/1.52      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_7604,plain,
% 8.03/1.52      ( v1_relat_1(X0) != iProver_top
% 8.03/1.52      | v2_funct_1(k2_funct_1(X0)) != iProver_top
% 8.03/1.52      | v1_funct_1(X0) != iProver_top
% 8.03/1.52      | k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0)) ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_3206,c_108]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_7605,plain,
% 8.03/1.52      ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
% 8.03/1.52      | v1_funct_1(X0) != iProver_top
% 8.03/1.52      | v2_funct_1(k2_funct_1(X0)) != iProver_top
% 8.03/1.52      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.52      inference(renaming,[status(thm)],[c_7604]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_7612,plain,
% 8.03/1.52      ( k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3))
% 8.03/1.52      | v1_funct_1(sK3) != iProver_top
% 8.03/1.52      | v2_funct_1(k4_relat_1(sK3)) != iProver_top
% 8.03/1.52      | v1_relat_1(sK3) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_6077,c_7605]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_2,plain,
% 8.03/1.52      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 8.03/1.52      inference(cnf_transformation,[],[f54]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1265,plain,
% 8.03/1.52      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_2488,plain,
% 8.03/1.52      ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_2286,c_1265]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_7613,plain,
% 8.03/1.52      ( k2_funct_1(k4_relat_1(sK3)) = sK3
% 8.03/1.52      | v1_funct_1(sK3) != iProver_top
% 8.03/1.52      | v2_funct_1(k4_relat_1(sK3)) != iProver_top
% 8.03/1.52      | v1_relat_1(sK3) != iProver_top ),
% 8.03/1.52      inference(light_normalisation,[status(thm)],[c_7612,c_2488,c_6077]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_10,plain,
% 8.03/1.52      ( ~ v1_funct_1(X0)
% 8.03/1.52      | ~ v2_funct_1(X0)
% 8.03/1.52      | v2_funct_1(k2_funct_1(X0))
% 8.03/1.52      | ~ v1_relat_1(X0) ),
% 8.03/1.52      inference(cnf_transformation,[],[f64]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_1259,plain,
% 8.03/1.52      ( v1_funct_1(X0) != iProver_top
% 8.03/1.52      | v2_funct_1(X0) != iProver_top
% 8.03/1.52      | v2_funct_1(k2_funct_1(X0)) = iProver_top
% 8.03/1.52      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_6520,plain,
% 8.03/1.52      ( v1_funct_1(sK3) != iProver_top
% 8.03/1.52      | v2_funct_1(k4_relat_1(sK3)) = iProver_top
% 8.03/1.52      | v2_funct_1(sK3) != iProver_top
% 8.03/1.52      | v1_relat_1(sK3) != iProver_top ),
% 8.03/1.52      inference(superposition,[status(thm)],[c_6077,c_1259]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_8619,plain,
% 8.03/1.52      ( k2_funct_1(k4_relat_1(sK3)) = sK3 ),
% 8.03/1.52      inference(global_propositional_subsumption,
% 8.03/1.52                [status(thm)],
% 8.03/1.52                [c_7613,c_44,c_2286,c_6072,c_6520]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_22966,plain,
% 8.03/1.52      ( k2_funct_1(sK2) = sK3 ),
% 8.03/1.52      inference(demodulation,[status(thm)],[c_16667,c_8619]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(c_29,negated_conjecture,
% 8.03/1.52      ( k2_funct_1(sK2) != sK3 ),
% 8.03/1.52      inference(cnf_transformation,[],[f93]) ).
% 8.03/1.52  
% 8.03/1.52  cnf(contradiction,plain,
% 8.03/1.52      ( $false ),
% 8.03/1.52      inference(minisat,[status(thm)],[c_22966,c_29]) ).
% 8.03/1.52  
% 8.03/1.52  
% 8.03/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 8.03/1.52  
% 8.03/1.52  ------                               Statistics
% 8.03/1.52  
% 8.03/1.52  ------ General
% 8.03/1.52  
% 8.03/1.52  abstr_ref_over_cycles:                  0
% 8.03/1.52  abstr_ref_under_cycles:                 0
% 8.03/1.52  gc_basic_clause_elim:                   0
% 8.03/1.52  forced_gc_time:                         0
% 8.03/1.52  parsing_time:                           0.007
% 8.03/1.52  unif_index_cands_time:                  0.
% 8.03/1.52  unif_index_add_time:                    0.
% 8.03/1.52  orderings_time:                         0.
% 8.03/1.52  out_proof_time:                         0.016
% 8.03/1.52  total_time:                             0.846
% 8.03/1.52  num_of_symbols:                         52
% 8.03/1.52  num_of_terms:                           32901
% 8.03/1.52  
% 8.03/1.52  ------ Preprocessing
% 8.03/1.52  
% 8.03/1.52  num_of_splits:                          0
% 8.03/1.52  num_of_split_atoms:                     0
% 8.03/1.52  num_of_reused_defs:                     0
% 8.03/1.52  num_eq_ax_congr_red:                    0
% 8.03/1.52  num_of_sem_filtered_clauses:            1
% 8.03/1.52  num_of_subtypes:                        0
% 8.03/1.52  monotx_restored_types:                  0
% 8.03/1.52  sat_num_of_epr_types:                   0
% 8.03/1.52  sat_num_of_non_cyclic_types:            0
% 8.03/1.52  sat_guarded_non_collapsed_types:        0
% 8.03/1.52  num_pure_diseq_elim:                    0
% 8.03/1.52  simp_replaced_by:                       0
% 8.03/1.52  res_preprocessed:                       188
% 8.03/1.52  prep_upred:                             0
% 8.03/1.52  prep_unflattend:                        12
% 8.03/1.52  smt_new_axioms:                         0
% 8.03/1.52  pred_elim_cands:                        5
% 8.03/1.52  pred_elim:                              1
% 8.03/1.52  pred_elim_cl:                           1
% 8.03/1.52  pred_elim_cycles:                       3
% 8.03/1.52  merged_defs:                            0
% 8.03/1.52  merged_defs_ncl:                        0
% 8.03/1.52  bin_hyper_res:                          0
% 8.03/1.52  prep_cycles:                            4
% 8.03/1.52  pred_elim_time:                         0.003
% 8.03/1.52  splitting_time:                         0.
% 8.03/1.52  sem_filter_time:                        0.
% 8.03/1.52  monotx_time:                            0.
% 8.03/1.52  subtype_inf_time:                       0.
% 8.03/1.52  
% 8.03/1.52  ------ Problem properties
% 8.03/1.52  
% 8.03/1.52  clauses:                                38
% 8.03/1.52  conjectures:                            11
% 8.03/1.52  epr:                                    7
% 8.03/1.52  horn:                                   34
% 8.03/1.52  ground:                                 12
% 8.03/1.52  unary:                                  17
% 8.03/1.52  binary:                                 2
% 8.03/1.52  lits:                                   137
% 8.03/1.52  lits_eq:                                31
% 8.03/1.52  fd_pure:                                0
% 8.03/1.52  fd_pseudo:                              0
% 8.03/1.52  fd_cond:                                4
% 8.03/1.52  fd_pseudo_cond:                         1
% 8.03/1.52  ac_symbols:                             0
% 8.03/1.52  
% 8.03/1.52  ------ Propositional Solver
% 8.03/1.52  
% 8.03/1.52  prop_solver_calls:                      33
% 8.03/1.52  prop_fast_solver_calls:                 3014
% 8.03/1.52  smt_solver_calls:                       0
% 8.03/1.52  smt_fast_solver_calls:                  0
% 8.03/1.52  prop_num_of_clauses:                    11603
% 8.03/1.52  prop_preprocess_simplified:             20701
% 8.03/1.52  prop_fo_subsumed:                       569
% 8.03/1.52  prop_solver_time:                       0.
% 8.03/1.52  smt_solver_time:                        0.
% 8.03/1.52  smt_fast_solver_time:                   0.
% 8.03/1.52  prop_fast_solver_time:                  0.
% 8.03/1.52  prop_unsat_core_time:                   0.001
% 8.03/1.52  
% 8.03/1.52  ------ QBF
% 8.03/1.52  
% 8.03/1.52  qbf_q_res:                              0
% 8.03/1.52  qbf_num_tautologies:                    0
% 8.03/1.52  qbf_prep_cycles:                        0
% 8.03/1.52  
% 8.03/1.52  ------ BMC1
% 8.03/1.52  
% 8.03/1.52  bmc1_current_bound:                     -1
% 8.03/1.52  bmc1_last_solved_bound:                 -1
% 8.03/1.52  bmc1_unsat_core_size:                   -1
% 8.03/1.52  bmc1_unsat_core_parents_size:           -1
% 8.03/1.52  bmc1_merge_next_fun:                    0
% 8.03/1.52  bmc1_unsat_core_clauses_time:           0.
% 8.03/1.52  
% 8.03/1.52  ------ Instantiation
% 8.03/1.52  
% 8.03/1.52  inst_num_of_clauses:                    2864
% 8.03/1.52  inst_num_in_passive:                    865
% 8.03/1.52  inst_num_in_active:                     1523
% 8.03/1.52  inst_num_in_unprocessed:                477
% 8.03/1.52  inst_num_of_loops:                      1620
% 8.03/1.52  inst_num_of_learning_restarts:          0
% 8.03/1.52  inst_num_moves_active_passive:          94
% 8.03/1.52  inst_lit_activity:                      0
% 8.03/1.52  inst_lit_activity_moves:                1
% 8.03/1.52  inst_num_tautologies:                   0
% 8.03/1.52  inst_num_prop_implied:                  0
% 8.03/1.52  inst_num_existing_simplified:           0
% 8.03/1.52  inst_num_eq_res_simplified:             0
% 8.03/1.52  inst_num_child_elim:                    0
% 8.03/1.52  inst_num_of_dismatching_blockings:      291
% 8.03/1.52  inst_num_of_non_proper_insts:           2496
% 8.03/1.52  inst_num_of_duplicates:                 0
% 8.03/1.52  inst_inst_num_from_inst_to_res:         0
% 8.03/1.52  inst_dismatching_checking_time:         0.
% 8.03/1.52  
% 8.03/1.52  ------ Resolution
% 8.03/1.52  
% 8.03/1.52  res_num_of_clauses:                     0
% 8.03/1.52  res_num_in_passive:                     0
% 8.03/1.52  res_num_in_active:                      0
% 8.03/1.52  res_num_of_loops:                       192
% 8.03/1.52  res_forward_subset_subsumed:            145
% 8.03/1.52  res_backward_subset_subsumed:           4
% 8.03/1.52  res_forward_subsumed:                   0
% 8.03/1.52  res_backward_subsumed:                  0
% 8.03/1.52  res_forward_subsumption_resolution:     2
% 8.03/1.52  res_backward_subsumption_resolution:    0
% 8.03/1.52  res_clause_to_clause_subsumption:       2018
% 8.03/1.52  res_orphan_elimination:                 0
% 8.03/1.52  res_tautology_del:                      169
% 8.03/1.52  res_num_eq_res_simplified:              1
% 8.03/1.52  res_num_sel_changes:                    0
% 8.03/1.52  res_moves_from_active_to_pass:          0
% 8.03/1.52  
% 8.03/1.52  ------ Superposition
% 8.03/1.52  
% 8.03/1.52  sup_time_total:                         0.
% 8.03/1.52  sup_time_generating:                    0.
% 8.03/1.52  sup_time_sim_full:                      0.
% 8.03/1.52  sup_time_sim_immed:                     0.
% 8.03/1.52  
% 8.03/1.52  sup_num_of_clauses:                     857
% 8.03/1.52  sup_num_in_active:                      273
% 8.03/1.52  sup_num_in_passive:                     584
% 8.03/1.52  sup_num_of_loops:                       322
% 8.03/1.52  sup_fw_superposition:                   393
% 8.03/1.52  sup_bw_superposition:                   689
% 8.03/1.52  sup_immediate_simplified:               451
% 8.03/1.52  sup_given_eliminated:                   8
% 8.03/1.52  comparisons_done:                       0
% 8.03/1.52  comparisons_avoided:                    0
% 8.03/1.52  
% 8.03/1.52  ------ Simplifications
% 8.03/1.52  
% 8.03/1.52  
% 8.03/1.52  sim_fw_subset_subsumed:                 31
% 8.03/1.52  sim_bw_subset_subsumed:                 60
% 8.03/1.52  sim_fw_subsumed:                        60
% 8.03/1.52  sim_bw_subsumed:                        3
% 8.03/1.52  sim_fw_subsumption_res:                 0
% 8.03/1.52  sim_bw_subsumption_res:                 0
% 8.03/1.52  sim_tautology_del:                      0
% 8.03/1.52  sim_eq_tautology_del:                   62
% 8.03/1.52  sim_eq_res_simp:                        0
% 8.03/1.52  sim_fw_demodulated:                     44
% 8.03/1.52  sim_bw_demodulated:                     29
% 8.03/1.52  sim_light_normalised:                   350
% 8.03/1.52  sim_joinable_taut:                      0
% 8.03/1.52  sim_joinable_simp:                      0
% 8.03/1.52  sim_ac_normalised:                      0
% 8.03/1.52  sim_smt_subsumption:                    0
% 8.03/1.52  
%------------------------------------------------------------------------------
