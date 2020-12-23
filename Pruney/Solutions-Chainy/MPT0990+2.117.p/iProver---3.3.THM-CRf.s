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
% DateTime   : Thu Dec  3 12:03:21 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  228 (2018 expanded)
%              Number of clauses        :  132 ( 657 expanded)
%              Number of leaves         :   25 ( 451 expanded)
%              Depth                    :   24
%              Number of atoms          :  643 (13035 expanded)
%              Number of equality atoms :  286 (4996 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f25,plain,(
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
    inference(pure_predicate_removal,[],[f24])).

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
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f58,plain,(
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

fof(f57,plain,
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

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f58,f57])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f59])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f81,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f22,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f81,f90])).

fof(f97,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f93,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f96,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f107,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f86,f90])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f102,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f90])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f103,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f73,f90])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f104,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f74,f90])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1176,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1192,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2877,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_1192])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1512,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2088,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_2089,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2088])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2210,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2211,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2210])).

cnf(c_3034,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2877,c_43,c_2089,c_2211])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1174,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2878,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1174,c_1192])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1253,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1307,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1253])).

cnf(c_1479,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_1480,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1479])).

cnf(c_1545,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1546,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1545])).

cnf(c_3042,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2878,c_41,c_1480,c_1546])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1173,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1183,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1187,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3903,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1187])).

cnf(c_17329,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_3903])).

cnf(c_17447,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17329,c_41,c_1480,c_1546])).

cnf(c_17448,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_17447])).

cnf(c_17455,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_17448])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1181,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2064,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1174,c_1181])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2065,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2064,c_35])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_441,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_33])).

cnf(c_442,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_444,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_442,c_39])).

cnf(c_1169,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_1636,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1169,c_39,c_38,c_442,c_1479,c_1545])).

cnf(c_2068,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2065,c_1636])).

cnf(c_17462,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17455,c_2068])).

cnf(c_17494,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_3034,c_17462])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1177,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4538,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_1177])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4719,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4538,c_42])).

cnf(c_4720,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4719])).

cnf(c_4728,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1174,c_4720])).

cnf(c_25,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_411,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_56,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_413,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_56])).

cnf(c_1171,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1245,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1763,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1171,c_39,c_38,c_37,c_36,c_56,c_411,c_1245])).

cnf(c_4729,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4728,c_1763])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_5305,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4729,c_40])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1188,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3805,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_1188])).

cnf(c_4435,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3034,c_3805])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_5])).

cnf(c_1172,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_1885,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_1172])).

cnf(c_2263,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1885,c_43,c_2089,c_2211])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1182,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3884,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2065,c_1182])).

cnf(c_4058,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3884,c_40,c_41,c_1480,c_1546])).

cnf(c_4065,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2263,c_4058])).

cnf(c_5301,plain,
    ( k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_4435,c_4065])).

cnf(c_10042,plain,
    ( k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_5301,c_5301,c_5305])).

cnf(c_12,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_5307,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(demodulation,[status(thm)],[c_5305,c_4435])).

cnf(c_5308,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = sK0 ),
    inference(demodulation,[status(thm)],[c_5307,c_12])).

cnf(c_7,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1190,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5453,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5308,c_1190])).

cnf(c_6408,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5453,c_41,c_1480,c_1546])).

cnf(c_1886,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1174,c_1172])).

cnf(c_2396,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1886,c_41,c_1480,c_1546])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1194,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2861,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2396,c_1194])).

cnf(c_6414,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_6408,c_2861])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1193,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4064,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1193,c_4058])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1189,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3046,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3042,c_1189])).

cnf(c_3051,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3046,c_2065])).

cnf(c_4068,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4064,c_3051])).

cnf(c_8746,plain,
    ( k9_relat_1(sK2,sK0) = sK1 ),
    inference(demodulation,[status(thm)],[c_6414,c_4068])).

cnf(c_10043,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_10042,c_12,c_8746])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1186,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3039,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_3034,c_1186])).

cnf(c_10047,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_10043,c_3039])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1185,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2683,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1185])).

cnf(c_7810,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_2683])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_469,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_470,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_472,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_39])).

cnf(c_1167,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_3049,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3042,c_1167])).

cnf(c_7814,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7810,c_3049])).

cnf(c_7815,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7814,c_6414])).

cnf(c_14119,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7815,c_41,c_1480,c_1546])).

cnf(c_17500,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_17494,c_5305,c_10047,c_14119])).

cnf(c_30,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f100])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17500,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:40:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 7.33/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.33/1.49  
% 7.33/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.33/1.49  
% 7.33/1.49  ------  iProver source info
% 7.33/1.49  
% 7.33/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.33/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.33/1.49  git: non_committed_changes: false
% 7.33/1.49  git: last_make_outside_of_git: false
% 7.33/1.49  
% 7.33/1.49  ------ 
% 7.33/1.49  
% 7.33/1.49  ------ Input Options
% 7.33/1.49  
% 7.33/1.49  --out_options                           all
% 7.33/1.49  --tptp_safe_out                         true
% 7.33/1.49  --problem_path                          ""
% 7.33/1.49  --include_path                          ""
% 7.33/1.49  --clausifier                            res/vclausify_rel
% 7.33/1.49  --clausifier_options                    ""
% 7.33/1.49  --stdin                                 false
% 7.33/1.49  --stats_out                             all
% 7.33/1.49  
% 7.33/1.49  ------ General Options
% 7.33/1.49  
% 7.33/1.49  --fof                                   false
% 7.33/1.49  --time_out_real                         305.
% 7.33/1.49  --time_out_virtual                      -1.
% 7.33/1.49  --symbol_type_check                     false
% 7.33/1.49  --clausify_out                          false
% 7.33/1.49  --sig_cnt_out                           false
% 7.33/1.49  --trig_cnt_out                          false
% 7.33/1.49  --trig_cnt_out_tolerance                1.
% 7.33/1.49  --trig_cnt_out_sk_spl                   false
% 7.33/1.49  --abstr_cl_out                          false
% 7.33/1.49  
% 7.33/1.49  ------ Global Options
% 7.33/1.49  
% 7.33/1.49  --schedule                              default
% 7.33/1.49  --add_important_lit                     false
% 7.33/1.49  --prop_solver_per_cl                    1000
% 7.33/1.49  --min_unsat_core                        false
% 7.33/1.49  --soft_assumptions                      false
% 7.33/1.49  --soft_lemma_size                       3
% 7.33/1.49  --prop_impl_unit_size                   0
% 7.33/1.49  --prop_impl_unit                        []
% 7.33/1.49  --share_sel_clauses                     true
% 7.33/1.49  --reset_solvers                         false
% 7.33/1.49  --bc_imp_inh                            [conj_cone]
% 7.33/1.49  --conj_cone_tolerance                   3.
% 7.33/1.49  --extra_neg_conj                        none
% 7.33/1.49  --large_theory_mode                     true
% 7.33/1.49  --prolific_symb_bound                   200
% 7.33/1.49  --lt_threshold                          2000
% 7.33/1.49  --clause_weak_htbl                      true
% 7.33/1.49  --gc_record_bc_elim                     false
% 7.33/1.49  
% 7.33/1.49  ------ Preprocessing Options
% 7.33/1.49  
% 7.33/1.49  --preprocessing_flag                    true
% 7.33/1.49  --time_out_prep_mult                    0.1
% 7.33/1.49  --splitting_mode                        input
% 7.33/1.49  --splitting_grd                         true
% 7.33/1.49  --splitting_cvd                         false
% 7.33/1.49  --splitting_cvd_svl                     false
% 7.33/1.49  --splitting_nvd                         32
% 7.33/1.49  --sub_typing                            true
% 7.33/1.49  --prep_gs_sim                           true
% 7.33/1.49  --prep_unflatten                        true
% 7.33/1.49  --prep_res_sim                          true
% 7.33/1.49  --prep_upred                            true
% 7.33/1.49  --prep_sem_filter                       exhaustive
% 7.33/1.49  --prep_sem_filter_out                   false
% 7.33/1.49  --pred_elim                             true
% 7.33/1.49  --res_sim_input                         true
% 7.33/1.49  --eq_ax_congr_red                       true
% 7.33/1.49  --pure_diseq_elim                       true
% 7.33/1.49  --brand_transform                       false
% 7.33/1.49  --non_eq_to_eq                          false
% 7.33/1.49  --prep_def_merge                        true
% 7.33/1.49  --prep_def_merge_prop_impl              false
% 7.33/1.49  --prep_def_merge_mbd                    true
% 7.33/1.49  --prep_def_merge_tr_red                 false
% 7.33/1.49  --prep_def_merge_tr_cl                  false
% 7.33/1.49  --smt_preprocessing                     true
% 7.33/1.49  --smt_ac_axioms                         fast
% 7.33/1.49  --preprocessed_out                      false
% 7.33/1.49  --preprocessed_stats                    false
% 7.33/1.49  
% 7.33/1.49  ------ Abstraction refinement Options
% 7.33/1.49  
% 7.33/1.49  --abstr_ref                             []
% 7.33/1.49  --abstr_ref_prep                        false
% 7.33/1.49  --abstr_ref_until_sat                   false
% 7.33/1.49  --abstr_ref_sig_restrict                funpre
% 7.33/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.33/1.49  --abstr_ref_under                       []
% 7.33/1.49  
% 7.33/1.49  ------ SAT Options
% 7.33/1.49  
% 7.33/1.49  --sat_mode                              false
% 7.33/1.49  --sat_fm_restart_options                ""
% 7.33/1.49  --sat_gr_def                            false
% 7.33/1.49  --sat_epr_types                         true
% 7.33/1.49  --sat_non_cyclic_types                  false
% 7.33/1.49  --sat_finite_models                     false
% 7.33/1.49  --sat_fm_lemmas                         false
% 7.33/1.49  --sat_fm_prep                           false
% 7.33/1.49  --sat_fm_uc_incr                        true
% 7.33/1.49  --sat_out_model                         small
% 7.33/1.49  --sat_out_clauses                       false
% 7.33/1.49  
% 7.33/1.49  ------ QBF Options
% 7.33/1.49  
% 7.33/1.49  --qbf_mode                              false
% 7.33/1.49  --qbf_elim_univ                         false
% 7.33/1.49  --qbf_dom_inst                          none
% 7.33/1.49  --qbf_dom_pre_inst                      false
% 7.33/1.49  --qbf_sk_in                             false
% 7.33/1.49  --qbf_pred_elim                         true
% 7.33/1.49  --qbf_split                             512
% 7.33/1.49  
% 7.33/1.49  ------ BMC1 Options
% 7.33/1.49  
% 7.33/1.49  --bmc1_incremental                      false
% 7.33/1.49  --bmc1_axioms                           reachable_all
% 7.33/1.49  --bmc1_min_bound                        0
% 7.33/1.49  --bmc1_max_bound                        -1
% 7.33/1.49  --bmc1_max_bound_default                -1
% 7.33/1.49  --bmc1_symbol_reachability              true
% 7.33/1.49  --bmc1_property_lemmas                  false
% 7.33/1.49  --bmc1_k_induction                      false
% 7.33/1.49  --bmc1_non_equiv_states                 false
% 7.33/1.49  --bmc1_deadlock                         false
% 7.33/1.49  --bmc1_ucm                              false
% 7.33/1.49  --bmc1_add_unsat_core                   none
% 7.59/1.49  --bmc1_unsat_core_children              false
% 7.59/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.49  --bmc1_out_stat                         full
% 7.59/1.49  --bmc1_ground_init                      false
% 7.59/1.49  --bmc1_pre_inst_next_state              false
% 7.59/1.49  --bmc1_pre_inst_state                   false
% 7.59/1.49  --bmc1_pre_inst_reach_state             false
% 7.59/1.49  --bmc1_out_unsat_core                   false
% 7.59/1.49  --bmc1_aig_witness_out                  false
% 7.59/1.49  --bmc1_verbose                          false
% 7.59/1.49  --bmc1_dump_clauses_tptp                false
% 7.59/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.49  --bmc1_dump_file                        -
% 7.59/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.49  --bmc1_ucm_extend_mode                  1
% 7.59/1.49  --bmc1_ucm_init_mode                    2
% 7.59/1.49  --bmc1_ucm_cone_mode                    none
% 7.59/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.49  --bmc1_ucm_relax_model                  4
% 7.59/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.49  --bmc1_ucm_layered_model                none
% 7.59/1.49  --bmc1_ucm_max_lemma_size               10
% 7.59/1.49  
% 7.59/1.49  ------ AIG Options
% 7.59/1.49  
% 7.59/1.49  --aig_mode                              false
% 7.59/1.49  
% 7.59/1.49  ------ Instantiation Options
% 7.59/1.49  
% 7.59/1.49  --instantiation_flag                    true
% 7.59/1.49  --inst_sos_flag                         true
% 7.59/1.49  --inst_sos_phase                        true
% 7.59/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.49  --inst_lit_sel_side                     num_symb
% 7.59/1.49  --inst_solver_per_active                1400
% 7.59/1.49  --inst_solver_calls_frac                1.
% 7.59/1.49  --inst_passive_queue_type               priority_queues
% 7.59/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.49  --inst_passive_queues_freq              [25;2]
% 7.59/1.49  --inst_dismatching                      true
% 7.59/1.49  --inst_eager_unprocessed_to_passive     true
% 7.59/1.49  --inst_prop_sim_given                   true
% 7.59/1.49  --inst_prop_sim_new                     false
% 7.59/1.49  --inst_subs_new                         false
% 7.59/1.49  --inst_eq_res_simp                      false
% 7.59/1.49  --inst_subs_given                       false
% 7.59/1.49  --inst_orphan_elimination               true
% 7.59/1.49  --inst_learning_loop_flag               true
% 7.59/1.49  --inst_learning_start                   3000
% 7.59/1.49  --inst_learning_factor                  2
% 7.59/1.49  --inst_start_prop_sim_after_learn       3
% 7.59/1.49  --inst_sel_renew                        solver
% 7.59/1.49  --inst_lit_activity_flag                true
% 7.59/1.49  --inst_restr_to_given                   false
% 7.59/1.49  --inst_activity_threshold               500
% 7.59/1.49  --inst_out_proof                        true
% 7.59/1.49  
% 7.59/1.49  ------ Resolution Options
% 7.59/1.49  
% 7.59/1.49  --resolution_flag                       true
% 7.59/1.49  --res_lit_sel                           adaptive
% 7.59/1.49  --res_lit_sel_side                      none
% 7.59/1.49  --res_ordering                          kbo
% 7.59/1.49  --res_to_prop_solver                    active
% 7.59/1.49  --res_prop_simpl_new                    false
% 7.59/1.49  --res_prop_simpl_given                  true
% 7.59/1.49  --res_passive_queue_type                priority_queues
% 7.59/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.49  --res_passive_queues_freq               [15;5]
% 7.59/1.49  --res_forward_subs                      full
% 7.59/1.49  --res_backward_subs                     full
% 7.59/1.49  --res_forward_subs_resolution           true
% 7.59/1.49  --res_backward_subs_resolution          true
% 7.59/1.49  --res_orphan_elimination                true
% 7.59/1.49  --res_time_limit                        2.
% 7.59/1.49  --res_out_proof                         true
% 7.59/1.49  
% 7.59/1.49  ------ Superposition Options
% 7.59/1.49  
% 7.59/1.49  --superposition_flag                    true
% 7.59/1.49  --sup_passive_queue_type                priority_queues
% 7.59/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.59/1.49  --demod_completeness_check              fast
% 7.59/1.49  --demod_use_ground                      true
% 7.59/1.49  --sup_to_prop_solver                    passive
% 7.59/1.49  --sup_prop_simpl_new                    true
% 7.59/1.49  --sup_prop_simpl_given                  true
% 7.59/1.49  --sup_fun_splitting                     true
% 7.59/1.49  --sup_smt_interval                      50000
% 7.59/1.49  
% 7.59/1.49  ------ Superposition Simplification Setup
% 7.59/1.49  
% 7.59/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.59/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.59/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.59/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.59/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.59/1.49  --sup_immed_triv                        [TrivRules]
% 7.59/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_immed_bw_main                     []
% 7.59/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.59/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_input_bw                          []
% 7.59/1.49  
% 7.59/1.49  ------ Combination Options
% 7.59/1.49  
% 7.59/1.49  --comb_res_mult                         3
% 7.59/1.49  --comb_sup_mult                         2
% 7.59/1.49  --comb_inst_mult                        10
% 7.59/1.49  
% 7.59/1.49  ------ Debug Options
% 7.59/1.49  
% 7.59/1.49  --dbg_backtrace                         false
% 7.59/1.49  --dbg_dump_prop_clauses                 false
% 7.59/1.49  --dbg_dump_prop_clauses_file            -
% 7.59/1.49  --dbg_out_stat                          false
% 7.59/1.49  ------ Parsing...
% 7.59/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.59/1.49  ------ Proving...
% 7.59/1.49  ------ Problem Properties 
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  clauses                                 34
% 7.59/1.49  conjectures                             8
% 7.59/1.49  EPR                                     6
% 7.59/1.49  Horn                                    34
% 7.59/1.49  unary                                   13
% 7.59/1.49  binary                                  10
% 7.59/1.49  lits                                    74
% 7.59/1.49  lits eq                                 20
% 7.59/1.49  fd_pure                                 0
% 7.59/1.49  fd_pseudo                               0
% 7.59/1.49  fd_cond                                 0
% 7.59/1.49  fd_pseudo_cond                          1
% 7.59/1.49  AC symbols                              0
% 7.59/1.49  
% 7.59/1.49  ------ Schedule dynamic 5 is on 
% 7.59/1.49  
% 7.59/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  ------ 
% 7.59/1.49  Current options:
% 7.59/1.49  ------ 
% 7.59/1.49  
% 7.59/1.49  ------ Input Options
% 7.59/1.49  
% 7.59/1.49  --out_options                           all
% 7.59/1.49  --tptp_safe_out                         true
% 7.59/1.49  --problem_path                          ""
% 7.59/1.49  --include_path                          ""
% 7.59/1.49  --clausifier                            res/vclausify_rel
% 7.59/1.49  --clausifier_options                    ""
% 7.59/1.49  --stdin                                 false
% 7.59/1.49  --stats_out                             all
% 7.59/1.49  
% 7.59/1.49  ------ General Options
% 7.59/1.49  
% 7.59/1.49  --fof                                   false
% 7.59/1.49  --time_out_real                         305.
% 7.59/1.49  --time_out_virtual                      -1.
% 7.59/1.49  --symbol_type_check                     false
% 7.59/1.49  --clausify_out                          false
% 7.59/1.49  --sig_cnt_out                           false
% 7.59/1.49  --trig_cnt_out                          false
% 7.59/1.49  --trig_cnt_out_tolerance                1.
% 7.59/1.49  --trig_cnt_out_sk_spl                   false
% 7.59/1.49  --abstr_cl_out                          false
% 7.59/1.49  
% 7.59/1.49  ------ Global Options
% 7.59/1.49  
% 7.59/1.49  --schedule                              default
% 7.59/1.49  --add_important_lit                     false
% 7.59/1.49  --prop_solver_per_cl                    1000
% 7.59/1.49  --min_unsat_core                        false
% 7.59/1.49  --soft_assumptions                      false
% 7.59/1.49  --soft_lemma_size                       3
% 7.59/1.49  --prop_impl_unit_size                   0
% 7.59/1.49  --prop_impl_unit                        []
% 7.59/1.49  --share_sel_clauses                     true
% 7.59/1.49  --reset_solvers                         false
% 7.59/1.49  --bc_imp_inh                            [conj_cone]
% 7.59/1.49  --conj_cone_tolerance                   3.
% 7.59/1.49  --extra_neg_conj                        none
% 7.59/1.49  --large_theory_mode                     true
% 7.59/1.49  --prolific_symb_bound                   200
% 7.59/1.49  --lt_threshold                          2000
% 7.59/1.49  --clause_weak_htbl                      true
% 7.59/1.49  --gc_record_bc_elim                     false
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing Options
% 7.59/1.49  
% 7.59/1.49  --preprocessing_flag                    true
% 7.59/1.49  --time_out_prep_mult                    0.1
% 7.59/1.49  --splitting_mode                        input
% 7.59/1.49  --splitting_grd                         true
% 7.59/1.49  --splitting_cvd                         false
% 7.59/1.49  --splitting_cvd_svl                     false
% 7.59/1.49  --splitting_nvd                         32
% 7.59/1.49  --sub_typing                            true
% 7.59/1.49  --prep_gs_sim                           true
% 7.59/1.49  --prep_unflatten                        true
% 7.59/1.49  --prep_res_sim                          true
% 7.59/1.49  --prep_upred                            true
% 7.59/1.49  --prep_sem_filter                       exhaustive
% 7.59/1.49  --prep_sem_filter_out                   false
% 7.59/1.49  --pred_elim                             true
% 7.59/1.49  --res_sim_input                         true
% 7.59/1.49  --eq_ax_congr_red                       true
% 7.59/1.49  --pure_diseq_elim                       true
% 7.59/1.49  --brand_transform                       false
% 7.59/1.49  --non_eq_to_eq                          false
% 7.59/1.49  --prep_def_merge                        true
% 7.59/1.49  --prep_def_merge_prop_impl              false
% 7.59/1.49  --prep_def_merge_mbd                    true
% 7.59/1.49  --prep_def_merge_tr_red                 false
% 7.59/1.49  --prep_def_merge_tr_cl                  false
% 7.59/1.49  --smt_preprocessing                     true
% 7.59/1.49  --smt_ac_axioms                         fast
% 7.59/1.49  --preprocessed_out                      false
% 7.59/1.49  --preprocessed_stats                    false
% 7.59/1.49  
% 7.59/1.49  ------ Abstraction refinement Options
% 7.59/1.49  
% 7.59/1.49  --abstr_ref                             []
% 7.59/1.49  --abstr_ref_prep                        false
% 7.59/1.49  --abstr_ref_until_sat                   false
% 7.59/1.49  --abstr_ref_sig_restrict                funpre
% 7.59/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.59/1.49  --abstr_ref_under                       []
% 7.59/1.49  
% 7.59/1.49  ------ SAT Options
% 7.59/1.49  
% 7.59/1.49  --sat_mode                              false
% 7.59/1.49  --sat_fm_restart_options                ""
% 7.59/1.49  --sat_gr_def                            false
% 7.59/1.49  --sat_epr_types                         true
% 7.59/1.49  --sat_non_cyclic_types                  false
% 7.59/1.49  --sat_finite_models                     false
% 7.59/1.49  --sat_fm_lemmas                         false
% 7.59/1.49  --sat_fm_prep                           false
% 7.59/1.49  --sat_fm_uc_incr                        true
% 7.59/1.49  --sat_out_model                         small
% 7.59/1.49  --sat_out_clauses                       false
% 7.59/1.49  
% 7.59/1.49  ------ QBF Options
% 7.59/1.49  
% 7.59/1.49  --qbf_mode                              false
% 7.59/1.49  --qbf_elim_univ                         false
% 7.59/1.49  --qbf_dom_inst                          none
% 7.59/1.49  --qbf_dom_pre_inst                      false
% 7.59/1.49  --qbf_sk_in                             false
% 7.59/1.49  --qbf_pred_elim                         true
% 7.59/1.49  --qbf_split                             512
% 7.59/1.49  
% 7.59/1.49  ------ BMC1 Options
% 7.59/1.49  
% 7.59/1.49  --bmc1_incremental                      false
% 7.59/1.49  --bmc1_axioms                           reachable_all
% 7.59/1.49  --bmc1_min_bound                        0
% 7.59/1.49  --bmc1_max_bound                        -1
% 7.59/1.49  --bmc1_max_bound_default                -1
% 7.59/1.49  --bmc1_symbol_reachability              true
% 7.59/1.49  --bmc1_property_lemmas                  false
% 7.59/1.49  --bmc1_k_induction                      false
% 7.59/1.49  --bmc1_non_equiv_states                 false
% 7.59/1.49  --bmc1_deadlock                         false
% 7.59/1.49  --bmc1_ucm                              false
% 7.59/1.49  --bmc1_add_unsat_core                   none
% 7.59/1.49  --bmc1_unsat_core_children              false
% 7.59/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.49  --bmc1_out_stat                         full
% 7.59/1.49  --bmc1_ground_init                      false
% 7.59/1.49  --bmc1_pre_inst_next_state              false
% 7.59/1.49  --bmc1_pre_inst_state                   false
% 7.59/1.49  --bmc1_pre_inst_reach_state             false
% 7.59/1.49  --bmc1_out_unsat_core                   false
% 7.59/1.49  --bmc1_aig_witness_out                  false
% 7.59/1.49  --bmc1_verbose                          false
% 7.59/1.49  --bmc1_dump_clauses_tptp                false
% 7.59/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.49  --bmc1_dump_file                        -
% 7.59/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.49  --bmc1_ucm_extend_mode                  1
% 7.59/1.49  --bmc1_ucm_init_mode                    2
% 7.59/1.49  --bmc1_ucm_cone_mode                    none
% 7.59/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.49  --bmc1_ucm_relax_model                  4
% 7.59/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.49  --bmc1_ucm_layered_model                none
% 7.59/1.49  --bmc1_ucm_max_lemma_size               10
% 7.59/1.49  
% 7.59/1.49  ------ AIG Options
% 7.59/1.49  
% 7.59/1.49  --aig_mode                              false
% 7.59/1.49  
% 7.59/1.49  ------ Instantiation Options
% 7.59/1.49  
% 7.59/1.49  --instantiation_flag                    true
% 7.59/1.49  --inst_sos_flag                         true
% 7.59/1.49  --inst_sos_phase                        true
% 7.59/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.49  --inst_lit_sel_side                     none
% 7.59/1.49  --inst_solver_per_active                1400
% 7.59/1.49  --inst_solver_calls_frac                1.
% 7.59/1.49  --inst_passive_queue_type               priority_queues
% 7.59/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.49  --inst_passive_queues_freq              [25;2]
% 7.59/1.49  --inst_dismatching                      true
% 7.59/1.49  --inst_eager_unprocessed_to_passive     true
% 7.59/1.49  --inst_prop_sim_given                   true
% 7.59/1.49  --inst_prop_sim_new                     false
% 7.59/1.49  --inst_subs_new                         false
% 7.59/1.49  --inst_eq_res_simp                      false
% 7.59/1.49  --inst_subs_given                       false
% 7.59/1.49  --inst_orphan_elimination               true
% 7.59/1.49  --inst_learning_loop_flag               true
% 7.59/1.49  --inst_learning_start                   3000
% 7.59/1.49  --inst_learning_factor                  2
% 7.59/1.49  --inst_start_prop_sim_after_learn       3
% 7.59/1.49  --inst_sel_renew                        solver
% 7.59/1.49  --inst_lit_activity_flag                true
% 7.59/1.49  --inst_restr_to_given                   false
% 7.59/1.49  --inst_activity_threshold               500
% 7.59/1.49  --inst_out_proof                        true
% 7.59/1.49  
% 7.59/1.49  ------ Resolution Options
% 7.59/1.49  
% 7.59/1.49  --resolution_flag                       false
% 7.59/1.49  --res_lit_sel                           adaptive
% 7.59/1.49  --res_lit_sel_side                      none
% 7.59/1.49  --res_ordering                          kbo
% 7.59/1.49  --res_to_prop_solver                    active
% 7.59/1.49  --res_prop_simpl_new                    false
% 7.59/1.49  --res_prop_simpl_given                  true
% 7.59/1.49  --res_passive_queue_type                priority_queues
% 7.59/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.49  --res_passive_queues_freq               [15;5]
% 7.59/1.49  --res_forward_subs                      full
% 7.59/1.49  --res_backward_subs                     full
% 7.59/1.49  --res_forward_subs_resolution           true
% 7.59/1.49  --res_backward_subs_resolution          true
% 7.59/1.49  --res_orphan_elimination                true
% 7.59/1.49  --res_time_limit                        2.
% 7.59/1.49  --res_out_proof                         true
% 7.59/1.49  
% 7.59/1.49  ------ Superposition Options
% 7.59/1.49  
% 7.59/1.49  --superposition_flag                    true
% 7.59/1.49  --sup_passive_queue_type                priority_queues
% 7.59/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.59/1.49  --demod_completeness_check              fast
% 7.59/1.49  --demod_use_ground                      true
% 7.59/1.49  --sup_to_prop_solver                    passive
% 7.59/1.49  --sup_prop_simpl_new                    true
% 7.59/1.49  --sup_prop_simpl_given                  true
% 7.59/1.49  --sup_fun_splitting                     true
% 7.59/1.49  --sup_smt_interval                      50000
% 7.59/1.49  
% 7.59/1.49  ------ Superposition Simplification Setup
% 7.59/1.49  
% 7.59/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.59/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.59/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.59/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.59/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.59/1.49  --sup_immed_triv                        [TrivRules]
% 7.59/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_immed_bw_main                     []
% 7.59/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.59/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_input_bw                          []
% 7.59/1.49  
% 7.59/1.49  ------ Combination Options
% 7.59/1.49  
% 7.59/1.49  --comb_res_mult                         3
% 7.59/1.49  --comb_sup_mult                         2
% 7.59/1.49  --comb_inst_mult                        10
% 7.59/1.49  
% 7.59/1.49  ------ Debug Options
% 7.59/1.49  
% 7.59/1.49  --dbg_backtrace                         false
% 7.59/1.49  --dbg_dump_prop_clauses                 false
% 7.59/1.49  --dbg_dump_prop_clauses_file            -
% 7.59/1.49  --dbg_out_stat                          false
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  ------ Proving...
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  % SZS status Theorem for theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  fof(f23,conjecture,(
% 7.59/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f24,negated_conjecture,(
% 7.59/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.59/1.49    inference(negated_conjecture,[],[f23])).
% 7.59/1.49  
% 7.59/1.49  fof(f25,plain,(
% 7.59/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.59/1.49    inference(pure_predicate_removal,[],[f24])).
% 7.59/1.49  
% 7.59/1.49  fof(f51,plain,(
% 7.59/1.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 7.59/1.49    inference(ennf_transformation,[],[f25])).
% 7.59/1.49  
% 7.59/1.49  fof(f52,plain,(
% 7.59/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 7.59/1.49    inference(flattening,[],[f51])).
% 7.59/1.49  
% 7.59/1.49  fof(f58,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 7.59/1.49    introduced(choice_axiom,[])).
% 7.59/1.49  
% 7.59/1.49  fof(f57,plain,(
% 7.59/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 7.59/1.49    introduced(choice_axiom,[])).
% 7.59/1.49  
% 7.59/1.49  fof(f59,plain,(
% 7.59/1.49    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 7.59/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f58,f57])).
% 7.59/1.49  
% 7.59/1.49  fof(f94,plain,(
% 7.59/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.59/1.49    inference(cnf_transformation,[],[f59])).
% 7.59/1.49  
% 7.59/1.49  fof(f2,axiom,(
% 7.59/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f27,plain,(
% 7.59/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.59/1.49    inference(ennf_transformation,[],[f2])).
% 7.59/1.49  
% 7.59/1.49  fof(f63,plain,(
% 7.59/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f27])).
% 7.59/1.49  
% 7.59/1.49  fof(f4,axiom,(
% 7.59/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f66,plain,(
% 7.59/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.59/1.49    inference(cnf_transformation,[],[f4])).
% 7.59/1.49  
% 7.59/1.49  fof(f92,plain,(
% 7.59/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.59/1.49    inference(cnf_transformation,[],[f59])).
% 7.59/1.49  
% 7.59/1.49  fof(f91,plain,(
% 7.59/1.49    v1_funct_1(sK2)),
% 7.59/1.49    inference(cnf_transformation,[],[f59])).
% 7.59/1.49  
% 7.59/1.49  fof(f12,axiom,(
% 7.59/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f35,plain,(
% 7.59/1.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.59/1.49    inference(ennf_transformation,[],[f12])).
% 7.59/1.49  
% 7.59/1.49  fof(f36,plain,(
% 7.59/1.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.59/1.49    inference(flattening,[],[f35])).
% 7.59/1.49  
% 7.59/1.49  fof(f75,plain,(
% 7.59/1.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f36])).
% 7.59/1.49  
% 7.59/1.49  fof(f8,axiom,(
% 7.59/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f32,plain,(
% 7.59/1.49    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.59/1.49    inference(ennf_transformation,[],[f8])).
% 7.59/1.49  
% 7.59/1.49  fof(f70,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f32])).
% 7.59/1.49  
% 7.59/1.49  fof(f17,axiom,(
% 7.59/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f44,plain,(
% 7.59/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.59/1.49    inference(ennf_transformation,[],[f17])).
% 7.59/1.49  
% 7.59/1.49  fof(f83,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.59/1.49    inference(cnf_transformation,[],[f44])).
% 7.59/1.49  
% 7.59/1.49  fof(f95,plain,(
% 7.59/1.49    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.59/1.49    inference(cnf_transformation,[],[f59])).
% 7.59/1.49  
% 7.59/1.49  fof(f15,axiom,(
% 7.59/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f41,plain,(
% 7.59/1.49    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.59/1.49    inference(ennf_transformation,[],[f15])).
% 7.59/1.49  
% 7.59/1.49  fof(f42,plain,(
% 7.59/1.49    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.59/1.49    inference(flattening,[],[f41])).
% 7.59/1.49  
% 7.59/1.49  fof(f81,plain,(
% 7.59/1.49    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f42])).
% 7.59/1.49  
% 7.59/1.49  fof(f22,axiom,(
% 7.59/1.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f90,plain,(
% 7.59/1.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f22])).
% 7.59/1.49  
% 7.59/1.49  fof(f105,plain,(
% 7.59/1.49    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f81,f90])).
% 7.59/1.49  
% 7.59/1.49  fof(f97,plain,(
% 7.59/1.49    v2_funct_1(sK2)),
% 7.59/1.49    inference(cnf_transformation,[],[f59])).
% 7.59/1.49  
% 7.59/1.49  fof(f21,axiom,(
% 7.59/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f49,plain,(
% 7.59/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.59/1.49    inference(ennf_transformation,[],[f21])).
% 7.59/1.49  
% 7.59/1.49  fof(f50,plain,(
% 7.59/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.59/1.49    inference(flattening,[],[f49])).
% 7.59/1.49  
% 7.59/1.49  fof(f89,plain,(
% 7.59/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f50])).
% 7.59/1.49  
% 7.59/1.49  fof(f93,plain,(
% 7.59/1.49    v1_funct_1(sK3)),
% 7.59/1.49    inference(cnf_transformation,[],[f59])).
% 7.59/1.49  
% 7.59/1.49  fof(f18,axiom,(
% 7.59/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f45,plain,(
% 7.59/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.59/1.49    inference(ennf_transformation,[],[f18])).
% 7.59/1.49  
% 7.59/1.49  fof(f46,plain,(
% 7.59/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.59/1.49    inference(flattening,[],[f45])).
% 7.59/1.49  
% 7.59/1.49  fof(f56,plain,(
% 7.59/1.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.59/1.49    inference(nnf_transformation,[],[f46])).
% 7.59/1.49  
% 7.59/1.49  fof(f84,plain,(
% 7.59/1.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.59/1.49    inference(cnf_transformation,[],[f56])).
% 7.59/1.49  
% 7.59/1.49  fof(f96,plain,(
% 7.59/1.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.59/1.49    inference(cnf_transformation,[],[f59])).
% 7.59/1.49  
% 7.59/1.49  fof(f19,axiom,(
% 7.59/1.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f86,plain,(
% 7.59/1.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.59/1.49    inference(cnf_transformation,[],[f19])).
% 7.59/1.49  
% 7.59/1.49  fof(f107,plain,(
% 7.59/1.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.59/1.49    inference(definition_unfolding,[],[f86,f90])).
% 7.59/1.49  
% 7.59/1.49  fof(f20,axiom,(
% 7.59/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f47,plain,(
% 7.59/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.59/1.49    inference(ennf_transformation,[],[f20])).
% 7.59/1.49  
% 7.59/1.49  fof(f48,plain,(
% 7.59/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.59/1.49    inference(flattening,[],[f47])).
% 7.59/1.49  
% 7.59/1.49  fof(f88,plain,(
% 7.59/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f48])).
% 7.59/1.49  
% 7.59/1.49  fof(f7,axiom,(
% 7.59/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f31,plain,(
% 7.59/1.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.59/1.49    inference(ennf_transformation,[],[f7])).
% 7.59/1.49  
% 7.59/1.49  fof(f69,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f31])).
% 7.59/1.49  
% 7.59/1.49  fof(f16,axiom,(
% 7.59/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f26,plain,(
% 7.59/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.59/1.49    inference(pure_predicate_removal,[],[f16])).
% 7.59/1.49  
% 7.59/1.49  fof(f43,plain,(
% 7.59/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.59/1.49    inference(ennf_transformation,[],[f26])).
% 7.59/1.49  
% 7.59/1.49  fof(f82,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.59/1.49    inference(cnf_transformation,[],[f43])).
% 7.59/1.49  
% 7.59/1.49  fof(f3,axiom,(
% 7.59/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f28,plain,(
% 7.59/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.59/1.49    inference(ennf_transformation,[],[f3])).
% 7.59/1.49  
% 7.59/1.49  fof(f55,plain,(
% 7.59/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.59/1.49    inference(nnf_transformation,[],[f28])).
% 7.59/1.49  
% 7.59/1.49  fof(f64,plain,(
% 7.59/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f55])).
% 7.59/1.49  
% 7.59/1.49  fof(f13,axiom,(
% 7.59/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f37,plain,(
% 7.59/1.49    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.59/1.49    inference(ennf_transformation,[],[f13])).
% 7.59/1.49  
% 7.59/1.49  fof(f38,plain,(
% 7.59/1.49    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.59/1.49    inference(flattening,[],[f37])).
% 7.59/1.49  
% 7.59/1.49  fof(f77,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f38])).
% 7.59/1.49  
% 7.59/1.49  fof(f9,axiom,(
% 7.59/1.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f71,plain,(
% 7.59/1.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.59/1.49    inference(cnf_transformation,[],[f9])).
% 7.59/1.49  
% 7.59/1.49  fof(f102,plain,(
% 7.59/1.49    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 7.59/1.49    inference(definition_unfolding,[],[f71,f90])).
% 7.59/1.49  
% 7.59/1.49  fof(f5,axiom,(
% 7.59/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f29,plain,(
% 7.59/1.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.59/1.49    inference(ennf_transformation,[],[f5])).
% 7.59/1.49  
% 7.59/1.49  fof(f67,plain,(
% 7.59/1.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f29])).
% 7.59/1.49  
% 7.59/1.49  fof(f1,axiom,(
% 7.59/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f53,plain,(
% 7.59/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.59/1.49    inference(nnf_transformation,[],[f1])).
% 7.59/1.49  
% 7.59/1.49  fof(f54,plain,(
% 7.59/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.59/1.49    inference(flattening,[],[f53])).
% 7.59/1.49  
% 7.59/1.49  fof(f62,plain,(
% 7.59/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f54])).
% 7.59/1.49  
% 7.59/1.49  fof(f61,plain,(
% 7.59/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.59/1.49    inference(cnf_transformation,[],[f54])).
% 7.59/1.49  
% 7.59/1.49  fof(f108,plain,(
% 7.59/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.59/1.49    inference(equality_resolution,[],[f61])).
% 7.59/1.49  
% 7.59/1.49  fof(f6,axiom,(
% 7.59/1.49    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f30,plain,(
% 7.59/1.49    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.59/1.49    inference(ennf_transformation,[],[f6])).
% 7.59/1.49  
% 7.59/1.49  fof(f68,plain,(
% 7.59/1.49    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f30])).
% 7.59/1.49  
% 7.59/1.49  fof(f10,axiom,(
% 7.59/1.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f33,plain,(
% 7.59/1.49    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 7.59/1.49    inference(ennf_transformation,[],[f10])).
% 7.59/1.49  
% 7.59/1.49  fof(f73,plain,(
% 7.59/1.49    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f33])).
% 7.59/1.49  
% 7.59/1.49  fof(f103,plain,(
% 7.59/1.49    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f73,f90])).
% 7.59/1.49  
% 7.59/1.49  fof(f11,axiom,(
% 7.59/1.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f34,plain,(
% 7.59/1.49    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 7.59/1.49    inference(ennf_transformation,[],[f11])).
% 7.59/1.49  
% 7.59/1.49  fof(f74,plain,(
% 7.59/1.49    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f34])).
% 7.59/1.49  
% 7.59/1.49  fof(f104,plain,(
% 7.59/1.49    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f74,f90])).
% 7.59/1.49  
% 7.59/1.49  fof(f14,axiom,(
% 7.59/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f39,plain,(
% 7.59/1.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.59/1.49    inference(ennf_transformation,[],[f14])).
% 7.59/1.49  
% 7.59/1.49  fof(f40,plain,(
% 7.59/1.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.59/1.49    inference(flattening,[],[f39])).
% 7.59/1.49  
% 7.59/1.49  fof(f79,plain,(
% 7.59/1.49    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f40])).
% 7.59/1.49  
% 7.59/1.49  fof(f100,plain,(
% 7.59/1.49    k2_funct_1(sK2) != sK3),
% 7.59/1.49    inference(cnf_transformation,[],[f59])).
% 7.59/1.49  
% 7.59/1.49  cnf(c_36,negated_conjecture,
% 7.59/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.59/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1176,plain,
% 7.59/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.59/1.49      | ~ v1_relat_1(X1)
% 7.59/1.49      | v1_relat_1(X0) ),
% 7.59/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1192,plain,
% 7.59/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.59/1.49      | v1_relat_1(X1) != iProver_top
% 7.59/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2877,plain,
% 7.59/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.59/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1176,c_1192]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_43,plain,
% 7.59/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1512,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.49      | v1_relat_1(X0)
% 7.59/1.49      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2088,plain,
% 7.59/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.59/1.49      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 7.59/1.49      | v1_relat_1(sK3) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1512]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2089,plain,
% 7.59/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.59/1.49      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.59/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_2088]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_6,plain,
% 7.59/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.59/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2210,plain,
% 7.59/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2211,plain,
% 7.59/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_2210]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3034,plain,
% 7.59/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_2877,c_43,c_2089,c_2211]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_38,negated_conjecture,
% 7.59/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.59/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1174,plain,
% 7.59/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2878,plain,
% 7.59/1.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.59/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1174,c_1192]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_41,plain,
% 7.59/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1253,plain,
% 7.59/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 7.59/1.49      | ~ v1_relat_1(X0)
% 7.59/1.49      | v1_relat_1(sK2) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1307,plain,
% 7.59/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.59/1.49      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 7.59/1.49      | v1_relat_1(sK2) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1253]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1479,plain,
% 7.59/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.59/1.49      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.59/1.49      | v1_relat_1(sK2) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1307]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1480,plain,
% 7.59/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.59/1.49      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.59/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_1479]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1545,plain,
% 7.59/1.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1546,plain,
% 7.59/1.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_1545]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3042,plain,
% 7.59/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_2878,c_41,c_1480,c_1546]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_39,negated_conjecture,
% 7.59/1.49      ( v1_funct_1(sK2) ),
% 7.59/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1173,plain,
% 7.59/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_16,plain,
% 7.59/1.49      ( ~ v1_funct_1(X0)
% 7.59/1.49      | ~ v1_relat_1(X0)
% 7.59/1.49      | v1_relat_1(k2_funct_1(X0)) ),
% 7.59/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1183,plain,
% 7.59/1.49      ( v1_funct_1(X0) != iProver_top
% 7.59/1.49      | v1_relat_1(X0) != iProver_top
% 7.59/1.49      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_10,plain,
% 7.59/1.49      ( ~ v1_relat_1(X0)
% 7.59/1.49      | ~ v1_relat_1(X1)
% 7.59/1.49      | ~ v1_relat_1(X2)
% 7.59/1.49      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 7.59/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1187,plain,
% 7.59/1.49      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.59/1.49      | v1_relat_1(X0) != iProver_top
% 7.59/1.49      | v1_relat_1(X1) != iProver_top
% 7.59/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3903,plain,
% 7.59/1.49      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 7.59/1.49      | v1_funct_1(X0) != iProver_top
% 7.59/1.49      | v1_relat_1(X0) != iProver_top
% 7.59/1.49      | v1_relat_1(X1) != iProver_top
% 7.59/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1183,c_1187]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_17329,plain,
% 7.59/1.49      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.59/1.49      | v1_relat_1(X0) != iProver_top
% 7.59/1.49      | v1_relat_1(X1) != iProver_top
% 7.59/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1173,c_3903]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_17447,plain,
% 7.59/1.49      ( v1_relat_1(X1) != iProver_top
% 7.59/1.49      | v1_relat_1(X0) != iProver_top
% 7.59/1.49      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_17329,c_41,c_1480,c_1546]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_17448,plain,
% 7.59/1.49      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.59/1.49      | v1_relat_1(X0) != iProver_top
% 7.59/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.59/1.49      inference(renaming,[status(thm)],[c_17447]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_17455,plain,
% 7.59/1.49      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 7.59/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_3042,c_17448]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_23,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.59/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1181,plain,
% 7.59/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.59/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2064,plain,
% 7.59/1.49      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1174,c_1181]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_35,negated_conjecture,
% 7.59/1.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.59/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2065,plain,
% 7.59/1.49      ( k2_relat_1(sK2) = sK1 ),
% 7.59/1.49      inference(light_normalisation,[status(thm)],[c_2064,c_35]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_20,plain,
% 7.59/1.49      ( ~ v2_funct_1(X0)
% 7.59/1.49      | ~ v1_funct_1(X0)
% 7.59/1.49      | ~ v1_relat_1(X0)
% 7.59/1.49      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 7.59/1.49      inference(cnf_transformation,[],[f105]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_33,negated_conjecture,
% 7.59/1.49      ( v2_funct_1(sK2) ),
% 7.59/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_441,plain,
% 7.59/1.49      ( ~ v1_funct_1(X0)
% 7.59/1.49      | ~ v1_relat_1(X0)
% 7.59/1.49      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 7.59/1.49      | sK2 != X0 ),
% 7.59/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_33]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_442,plain,
% 7.59/1.49      ( ~ v1_funct_1(sK2)
% 7.59/1.49      | ~ v1_relat_1(sK2)
% 7.59/1.49      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.59/1.49      inference(unflattening,[status(thm)],[c_441]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_444,plain,
% 7.59/1.49      ( ~ v1_relat_1(sK2)
% 7.59/1.49      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_442,c_39]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1169,plain,
% 7.59/1.49      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 7.59/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1636,plain,
% 7.59/1.49      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_1169,c_39,c_38,c_442,c_1479,c_1545]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2068,plain,
% 7.59/1.49      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_2065,c_1636]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_17462,plain,
% 7.59/1.49      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.59/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.49      inference(light_normalisation,[status(thm)],[c_17455,c_2068]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_17494,plain,
% 7.59/1.49      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_3034,c_17462]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_29,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.59/1.49      | ~ v1_funct_1(X0)
% 7.59/1.49      | ~ v1_funct_1(X3)
% 7.59/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.59/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1177,plain,
% 7.59/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.59/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.59/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.59/1.49      | v1_funct_1(X5) != iProver_top
% 7.59/1.49      | v1_funct_1(X4) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_4538,plain,
% 7.59/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.59/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.59/1.49      | v1_funct_1(X2) != iProver_top
% 7.59/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1176,c_1177]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_37,negated_conjecture,
% 7.59/1.49      ( v1_funct_1(sK3) ),
% 7.59/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_42,plain,
% 7.59/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_4719,plain,
% 7.59/1.49      ( v1_funct_1(X2) != iProver_top
% 7.59/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.59/1.49      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_4538,c_42]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_4720,plain,
% 7.59/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.59/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.59/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.59/1.49      inference(renaming,[status(thm)],[c_4719]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_4728,plain,
% 7.59/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.59/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1174,c_4720]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_25,plain,
% 7.59/1.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.59/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.59/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.59/1.49      | X3 = X2 ),
% 7.59/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_34,negated_conjecture,
% 7.59/1.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.59/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_410,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.49      | X3 = X0
% 7.59/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.59/1.49      | k6_partfun1(sK0) != X3
% 7.59/1.49      | sK0 != X2
% 7.59/1.49      | sK0 != X1 ),
% 7.59/1.49      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_411,plain,
% 7.59/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.59/1.49      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.59/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.59/1.49      inference(unflattening,[status(thm)],[c_410]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_26,plain,
% 7.59/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.59/1.49      inference(cnf_transformation,[],[f107]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_56,plain,
% 7.59/1.49      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_26]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_413,plain,
% 7.59/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.59/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_411,c_56]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1171,plain,
% 7.59/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.59/1.49      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_27,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.59/1.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.59/1.49      | ~ v1_funct_1(X0)
% 7.59/1.49      | ~ v1_funct_1(X3) ),
% 7.59/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1245,plain,
% 7.59/1.49      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.59/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.59/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.59/1.49      | ~ v1_funct_1(sK3)
% 7.59/1.49      | ~ v1_funct_1(sK2) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_27]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1763,plain,
% 7.59/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_1171,c_39,c_38,c_37,c_36,c_56,c_411,c_1245]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_4729,plain,
% 7.59/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.59/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.59/1.49      inference(light_normalisation,[status(thm)],[c_4728,c_1763]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_40,plain,
% 7.59/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_5305,plain,
% 7.59/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_4729,c_40]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_9,plain,
% 7.59/1.49      ( ~ v1_relat_1(X0)
% 7.59/1.49      | ~ v1_relat_1(X1)
% 7.59/1.49      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 7.59/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1188,plain,
% 7.59/1.49      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 7.59/1.49      | v1_relat_1(X0) != iProver_top
% 7.59/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3805,plain,
% 7.59/1.49      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 7.59/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_3042,c_1188]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_4435,plain,
% 7.59/1.49      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_3034,c_3805]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_22,plain,
% 7.59/1.49      ( v4_relat_1(X0,X1)
% 7.59/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.59/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_5,plain,
% 7.59/1.49      ( ~ v4_relat_1(X0,X1)
% 7.59/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.59/1.49      | ~ v1_relat_1(X0) ),
% 7.59/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_389,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.59/1.49      | ~ v1_relat_1(X0) ),
% 7.59/1.49      inference(resolution,[status(thm)],[c_22,c_5]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1172,plain,
% 7.59/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.59/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.59/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1885,plain,
% 7.59/1.49      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
% 7.59/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1176,c_1172]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2263,plain,
% 7.59/1.49      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_1885,c_43,c_2089,c_2211]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_17,plain,
% 7.59/1.49      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 7.59/1.49      | ~ v1_funct_1(X1)
% 7.59/1.49      | ~ v1_relat_1(X1)
% 7.59/1.49      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 7.59/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1182,plain,
% 7.59/1.49      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 7.59/1.49      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 7.59/1.49      | v1_funct_1(X0) != iProver_top
% 7.59/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3884,plain,
% 7.59/1.49      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 7.59/1.49      | r1_tarski(X0,sK1) != iProver_top
% 7.59/1.49      | v1_funct_1(sK2) != iProver_top
% 7.59/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_2065,c_1182]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_4058,plain,
% 7.59/1.49      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 7.59/1.49      | r1_tarski(X0,sK1) != iProver_top ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_3884,c_40,c_41,c_1480,c_1546]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_4065,plain,
% 7.59/1.49      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_2263,c_4058]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_5301,plain,
% 7.59/1.49      ( k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(sK3) ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_4435,c_4065]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_10042,plain,
% 7.59/1.49      ( k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) = k1_relat_1(sK3) ),
% 7.59/1.49      inference(light_normalisation,[status(thm)],[c_5301,c_5301,c_5305]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_12,plain,
% 7.59/1.49      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.59/1.49      inference(cnf_transformation,[],[f102]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_5307,plain,
% 7.59/1.49      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_5305,c_4435]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_5308,plain,
% 7.59/1.49      ( k10_relat_1(sK2,k1_relat_1(sK3)) = sK0 ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_5307,c_12]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_7,plain,
% 7.59/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.59/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1190,plain,
% 7.59/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.59/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_5453,plain,
% 7.59/1.49      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 7.59/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_5308,c_1190]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_6408,plain,
% 7.59/1.49      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_5453,c_41,c_1480,c_1546]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1886,plain,
% 7.59/1.49      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 7.59/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1174,c_1172]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2396,plain,
% 7.59/1.49      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_1886,c_41,c_1480,c_1546]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_0,plain,
% 7.59/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.59/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1194,plain,
% 7.59/1.49      ( X0 = X1
% 7.59/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.59/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2861,plain,
% 7.59/1.49      ( k1_relat_1(sK2) = sK0
% 7.59/1.49      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_2396,c_1194]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_6414,plain,
% 7.59/1.49      ( k1_relat_1(sK2) = sK0 ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_6408,c_2861]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1,plain,
% 7.59/1.49      ( r1_tarski(X0,X0) ),
% 7.59/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1193,plain,
% 7.59/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_4064,plain,
% 7.59/1.49      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1193,c_4058]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_8,plain,
% 7.59/1.49      ( ~ v1_relat_1(X0)
% 7.59/1.49      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 7.59/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1189,plain,
% 7.59/1.49      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 7.59/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3046,plain,
% 7.59/1.49      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_3042,c_1189]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3051,plain,
% 7.59/1.49      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 7.59/1.49      inference(light_normalisation,[status(thm)],[c_3046,c_2065]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_4068,plain,
% 7.59/1.49      ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK1 ),
% 7.59/1.49      inference(light_normalisation,[status(thm)],[c_4064,c_3051]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_8746,plain,
% 7.59/1.49      ( k9_relat_1(sK2,sK0) = sK1 ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_6414,c_4068]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_10043,plain,
% 7.59/1.49      ( k1_relat_1(sK3) = sK1 ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_10042,c_12,c_8746]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_13,plain,
% 7.59/1.49      ( ~ v1_relat_1(X0)
% 7.59/1.49      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 7.59/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1186,plain,
% 7.59/1.49      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 7.59/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3039,plain,
% 7.59/1.49      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_3034,c_1186]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_10047,plain,
% 7.59/1.49      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_10043,c_3039]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_14,plain,
% 7.59/1.49      ( ~ v1_relat_1(X0)
% 7.59/1.49      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 7.59/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1185,plain,
% 7.59/1.49      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 7.59/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2683,plain,
% 7.59/1.49      ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 7.59/1.49      | v1_funct_1(X0) != iProver_top
% 7.59/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1183,c_1185]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_7810,plain,
% 7.59/1.49      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
% 7.59/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1173,c_2683]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_18,plain,
% 7.59/1.49      ( ~ v2_funct_1(X0)
% 7.59/1.49      | ~ v1_funct_1(X0)
% 7.59/1.49      | ~ v1_relat_1(X0)
% 7.59/1.49      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.59/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_469,plain,
% 7.59/1.49      ( ~ v1_funct_1(X0)
% 7.59/1.49      | ~ v1_relat_1(X0)
% 7.59/1.49      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.59/1.49      | sK2 != X0 ),
% 7.59/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_470,plain,
% 7.59/1.49      ( ~ v1_funct_1(sK2)
% 7.59/1.49      | ~ v1_relat_1(sK2)
% 7.59/1.49      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.59/1.49      inference(unflattening,[status(thm)],[c_469]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_472,plain,
% 7.59/1.49      ( ~ v1_relat_1(sK2)
% 7.59/1.49      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_470,c_39]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1167,plain,
% 7.59/1.49      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.59/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_472]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3049,plain,
% 7.59/1.49      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_3042,c_1167]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_7814,plain,
% 7.59/1.49      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
% 7.59/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.59/1.49      inference(light_normalisation,[status(thm)],[c_7810,c_3049]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_7815,plain,
% 7.59/1.49      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
% 7.59/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_7814,c_6414]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_14119,plain,
% 7.59/1.49      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_7815,c_41,c_1480,c_1546]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_17500,plain,
% 7.59/1.49      ( k2_funct_1(sK2) = sK3 ),
% 7.59/1.49      inference(light_normalisation,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_17494,c_5305,c_10047,c_14119]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_30,negated_conjecture,
% 7.59/1.49      ( k2_funct_1(sK2) != sK3 ),
% 7.59/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(contradiction,plain,
% 7.59/1.49      ( $false ),
% 7.59/1.49      inference(minisat,[status(thm)],[c_17500,c_30]) ).
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  ------                               Statistics
% 7.59/1.49  
% 7.59/1.49  ------ General
% 7.59/1.49  
% 7.59/1.49  abstr_ref_over_cycles:                  0
% 7.59/1.49  abstr_ref_under_cycles:                 0
% 7.59/1.49  gc_basic_clause_elim:                   0
% 7.59/1.49  forced_gc_time:                         0
% 7.59/1.49  parsing_time:                           0.013
% 7.59/1.49  unif_index_cands_time:                  0.
% 7.59/1.49  unif_index_add_time:                    0.
% 7.59/1.49  orderings_time:                         0.
% 7.59/1.49  out_proof_time:                         0.031
% 7.59/1.49  total_time:                             0.596
% 7.59/1.49  num_of_symbols:                         54
% 7.59/1.49  num_of_terms:                           24087
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing
% 7.59/1.49  
% 7.59/1.49  num_of_splits:                          0
% 7.59/1.49  num_of_split_atoms:                     0
% 7.59/1.49  num_of_reused_defs:                     0
% 7.59/1.49  num_eq_ax_congr_red:                    8
% 7.59/1.49  num_of_sem_filtered_clauses:            1
% 7.59/1.49  num_of_subtypes:                        0
% 7.59/1.49  monotx_restored_types:                  0
% 7.59/1.49  sat_num_of_epr_types:                   0
% 7.59/1.49  sat_num_of_non_cyclic_types:            0
% 7.59/1.49  sat_guarded_non_collapsed_types:        0
% 7.59/1.49  num_pure_diseq_elim:                    0
% 7.59/1.49  simp_replaced_by:                       0
% 7.59/1.49  res_preprocessed:                       176
% 7.59/1.49  prep_upred:                             0
% 7.59/1.49  prep_unflattend:                        12
% 7.59/1.49  smt_new_axioms:                         0
% 7.59/1.49  pred_elim_cands:                        4
% 7.59/1.49  pred_elim:                              3
% 7.59/1.49  pred_elim_cl:                           5
% 7.59/1.49  pred_elim_cycles:                       5
% 7.59/1.49  merged_defs:                            0
% 7.59/1.49  merged_defs_ncl:                        0
% 7.59/1.49  bin_hyper_res:                          0
% 7.59/1.49  prep_cycles:                            4
% 7.59/1.49  pred_elim_time:                         0.003
% 7.59/1.49  splitting_time:                         0.
% 7.59/1.49  sem_filter_time:                        0.
% 7.59/1.49  monotx_time:                            0.001
% 7.59/1.49  subtype_inf_time:                       0.
% 7.59/1.49  
% 7.59/1.49  ------ Problem properties
% 7.59/1.49  
% 7.59/1.49  clauses:                                34
% 7.59/1.49  conjectures:                            8
% 7.59/1.49  epr:                                    6
% 7.59/1.49  horn:                                   34
% 7.59/1.49  ground:                                 13
% 7.59/1.49  unary:                                  13
% 7.59/1.49  binary:                                 10
% 7.59/1.49  lits:                                   74
% 7.59/1.49  lits_eq:                                20
% 7.59/1.49  fd_pure:                                0
% 7.59/1.49  fd_pseudo:                              0
% 7.59/1.49  fd_cond:                                0
% 7.59/1.49  fd_pseudo_cond:                         1
% 7.59/1.49  ac_symbols:                             0
% 7.59/1.49  
% 7.59/1.49  ------ Propositional Solver
% 7.59/1.49  
% 7.59/1.49  prop_solver_calls:                      35
% 7.59/1.49  prop_fast_solver_calls:                 1608
% 7.59/1.49  smt_solver_calls:                       0
% 7.59/1.49  smt_fast_solver_calls:                  0
% 7.59/1.49  prop_num_of_clauses:                    9009
% 7.59/1.49  prop_preprocess_simplified:             17830
% 7.59/1.49  prop_fo_subsumed:                       146
% 7.59/1.49  prop_solver_time:                       0.
% 7.59/1.49  smt_solver_time:                        0.
% 7.59/1.49  smt_fast_solver_time:                   0.
% 7.59/1.49  prop_fast_solver_time:                  0.
% 7.59/1.49  prop_unsat_core_time:                   0.001
% 7.59/1.49  
% 7.59/1.49  ------ QBF
% 7.59/1.49  
% 7.59/1.49  qbf_q_res:                              0
% 7.59/1.49  qbf_num_tautologies:                    0
% 7.59/1.49  qbf_prep_cycles:                        0
% 7.59/1.49  
% 7.59/1.49  ------ BMC1
% 7.59/1.49  
% 7.59/1.49  bmc1_current_bound:                     -1
% 7.59/1.49  bmc1_last_solved_bound:                 -1
% 7.59/1.49  bmc1_unsat_core_size:                   -1
% 7.59/1.49  bmc1_unsat_core_parents_size:           -1
% 7.59/1.49  bmc1_merge_next_fun:                    0
% 7.59/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.59/1.49  
% 7.59/1.49  ------ Instantiation
% 7.59/1.49  
% 7.59/1.49  inst_num_of_clauses:                    2352
% 7.59/1.49  inst_num_in_passive:                    708
% 7.59/1.49  inst_num_in_active:                     1254
% 7.59/1.49  inst_num_in_unprocessed:                390
% 7.59/1.49  inst_num_of_loops:                      1350
% 7.59/1.49  inst_num_of_learning_restarts:          0
% 7.59/1.49  inst_num_moves_active_passive:          92
% 7.59/1.49  inst_lit_activity:                      0
% 7.59/1.49  inst_lit_activity_moves:                2
% 7.59/1.49  inst_num_tautologies:                   0
% 7.59/1.49  inst_num_prop_implied:                  0
% 7.59/1.49  inst_num_existing_simplified:           0
% 7.59/1.49  inst_num_eq_res_simplified:             0
% 7.59/1.49  inst_num_child_elim:                    0
% 7.59/1.49  inst_num_of_dismatching_blockings:      889
% 7.59/1.49  inst_num_of_non_proper_insts:           2712
% 7.59/1.49  inst_num_of_duplicates:                 0
% 7.59/1.49  inst_inst_num_from_inst_to_res:         0
% 7.59/1.49  inst_dismatching_checking_time:         0.
% 7.59/1.49  
% 7.59/1.49  ------ Resolution
% 7.59/1.49  
% 7.59/1.49  res_num_of_clauses:                     0
% 7.59/1.49  res_num_in_passive:                     0
% 7.59/1.49  res_num_in_active:                      0
% 7.59/1.49  res_num_of_loops:                       180
% 7.59/1.49  res_forward_subset_subsumed:            144
% 7.59/1.49  res_backward_subset_subsumed:           0
% 7.59/1.49  res_forward_subsumed:                   0
% 7.59/1.49  res_backward_subsumed:                  0
% 7.59/1.49  res_forward_subsumption_resolution:     0
% 7.59/1.49  res_backward_subsumption_resolution:    0
% 7.59/1.49  res_clause_to_clause_subsumption:       1670
% 7.59/1.49  res_orphan_elimination:                 0
% 7.59/1.49  res_tautology_del:                      265
% 7.59/1.49  res_num_eq_res_simplified:              0
% 7.59/1.49  res_num_sel_changes:                    0
% 7.59/1.49  res_moves_from_active_to_pass:          0
% 7.59/1.49  
% 7.59/1.49  ------ Superposition
% 7.59/1.49  
% 7.59/1.49  sup_time_total:                         0.
% 7.59/1.49  sup_time_generating:                    0.
% 7.59/1.49  sup_time_sim_full:                      0.
% 7.59/1.49  sup_time_sim_immed:                     0.
% 7.59/1.49  
% 7.59/1.49  sup_num_of_clauses:                     597
% 7.59/1.49  sup_num_in_active:                      226
% 7.59/1.49  sup_num_in_passive:                     371
% 7.59/1.49  sup_num_of_loops:                       269
% 7.59/1.49  sup_fw_superposition:                   507
% 7.59/1.49  sup_bw_superposition:                   220
% 7.59/1.49  sup_immediate_simplified:               293
% 7.59/1.49  sup_given_eliminated:                   6
% 7.59/1.49  comparisons_done:                       0
% 7.59/1.49  comparisons_avoided:                    0
% 7.59/1.49  
% 7.59/1.49  ------ Simplifications
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  sim_fw_subset_subsumed:                 13
% 7.59/1.49  sim_bw_subset_subsumed:                 50
% 7.59/1.49  sim_fw_subsumed:                        34
% 7.59/1.49  sim_bw_subsumed:                        5
% 7.59/1.49  sim_fw_subsumption_res:                 0
% 7.59/1.49  sim_bw_subsumption_res:                 0
% 7.59/1.49  sim_tautology_del:                      2
% 7.59/1.49  sim_eq_tautology_del:                   46
% 7.59/1.49  sim_eq_res_simp:                        0
% 7.59/1.49  sim_fw_demodulated:                     56
% 7.59/1.49  sim_bw_demodulated:                     29
% 7.59/1.49  sim_light_normalised:                   307
% 7.59/1.49  sim_joinable_taut:                      0
% 7.59/1.49  sim_joinable_simp:                      0
% 7.59/1.49  sim_ac_normalised:                      0
% 7.59/1.49  sim_smt_subsumption:                    0
% 7.59/1.49  
%------------------------------------------------------------------------------
