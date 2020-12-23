%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:36 EST 2020

% Result     : Theorem 8.18s
% Output     : CNFRefutation 8.18s
% Verified   : 
% Statistics : Number of formulae       :  236 (1697 expanded)
%              Number of clauses        :  155 ( 528 expanded)
%              Number of leaves         :   25 ( 432 expanded)
%              Depth                    :   25
%              Number of atoms          :  883 (13713 expanded)
%              Number of equality atoms :  405 (4754 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f48,f47])).

fof(f84,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f65,f69])).

fof(f77,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f49])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f91,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f54,f69])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_30,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_416,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_424,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_416,c_15])).

cnf(c_706,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_424])).

cnf(c_1345,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_727,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1415,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_2044,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1345,c_37,c_35,c_34,c_32,c_706,c_1415])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_428,plain,
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
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_429,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_516,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_429])).

cnf(c_705,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK0)
    | ~ v1_funct_2(X1_48,sK0,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_516])).

cnf(c_1346,plain,
    ( k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_2155,plain,
    ( k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k6_partfun1(sK0)
    | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1346,c_2044])).

cnf(c_2159,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2044,c_2155])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1423,plain,
    ( ~ v1_funct_2(X0_48,sK0,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,X0_48,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_1425,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1423])).

cnf(c_743,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1467,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_2418,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2159,c_37,c_36,c_35,c_34,c_33,c_32,c_1425,c_1467])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_719,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1336,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49)
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_4165,plain,
    ( sK0 = k1_xboole_0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2418,c_1336])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_716,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_714,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1389,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,sK0,X0_48) != sK0
    | k1_xboole_0 = sK0
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_1459,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) != sK0
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_746,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1481,plain,
    ( X0_48 != X1_48
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_48
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48 ),
    inference(instantiation,[status(thm)],[c_746])).

cnf(c_1536,plain,
    ( X0_48 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1481])).

cnf(c_1693,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_723,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ v1_funct_2(X1_48,X1_49,X2_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | v2_funct_1(X1_48)
    | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,X1_48))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X2_49 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1497,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ v1_funct_2(sK3,X1_49,X2_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X2_49 ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_1655,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ v1_funct_2(sK3,X1_49,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,sK0)))
    | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,sK0,X0_48,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1497])).

cnf(c_1771,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1655])).

cnf(c_758,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_1877,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0_48 ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_2387,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v2_funct_1(k6_partfun1(sK0))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1877])).

cnf(c_7,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_734,plain,
    ( v2_funct_1(k6_partfun1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2991,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_23064,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4165,c_37,c_36,c_35,c_34,c_33,c_32,c_716,c_714,c_706,c_1415,c_1425,c_1459,c_1467,c_1693,c_1771,c_2387,c_2991])).

cnf(c_711,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1340,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_735,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | v1_relat_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1320,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(k2_funct_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_740,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1315,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_713,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1338,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_741,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ v1_relat_1(X1_48)
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1314,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_1717,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1338,c_1314])).

cnf(c_1813,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_1717])).

cnf(c_710,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1341,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_1810,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1341,c_1314])).

cnf(c_1935,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_1810])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_739,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_relat_1(X1_48)
    | ~ v1_relat_1(X2_48)
    | k5_relat_1(k5_relat_1(X0_48,X2_48),X1_48) = k5_relat_1(X0_48,k5_relat_1(X2_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1316,plain,
    ( k5_relat_1(k5_relat_1(X0_48,X1_48),X2_48) = k5_relat_1(X0_48,k5_relat_1(X1_48,X2_48))
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_3392,plain,
    ( k5_relat_1(sK2,k5_relat_1(X0_48,X1_48)) = k5_relat_1(k5_relat_1(sK2,X0_48),X1_48)
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1935,c_1316])).

cnf(c_5760,plain,
    ( k5_relat_1(k5_relat_1(sK2,sK3),X0_48) = k5_relat_1(sK2,k5_relat_1(sK3,X0_48))
    | v1_relat_1(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_3392])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_725,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1330,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_3501,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1338,c_1330])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3670,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3501,c_41])).

cnf(c_3671,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3670])).

cnf(c_3677,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1341,c_3671])).

cnf(c_3680,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3677,c_2044])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4049,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3680,c_38])).

cnf(c_5762,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,X0_48)) = k5_relat_1(k6_partfun1(sK0),X0_48)
    | v1_relat_1(X0_48) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5760,c_4049])).

cnf(c_5781,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(X0_48))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(X0_48))
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1320,c_5762])).

cnf(c_11969,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_5781])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_738,plain,
    ( ~ v1_relat_1(X0_48)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0_48)),X0_48) = X0_48 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1317,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0_48)),X0_48) = X0_48
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_2247,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0_48))),k2_funct_1(X0_48)) = k2_funct_1(X0_48)
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1320,c_1317])).

cnf(c_6864,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) = k2_funct_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_2247])).

cnf(c_1332,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X2_49
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | v1_funct_2(X1_48,X1_49,X2_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
    | v2_funct_1(X1_48) = iProver_top
    | v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,X1_48)) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_4211,plain,
    ( k1_xboole_0 = X0_49
    | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_1332])).

cnf(c_39,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4218,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
    | k1_xboole_0 = X0_49
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4211,c_38,c_39,c_40])).

cnf(c_4219,plain,
    ( k1_xboole_0 = X0_49
    | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_4218])).

cnf(c_4222,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2044,c_4219])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1772,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1771])).

cnf(c_2388,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0)
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) = iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2387])).

cnf(c_2992,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2991])).

cnf(c_4259,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4222,c_37,c_38,c_39,c_35,c_40,c_34,c_41,c_42,c_32,c_43,c_716,c_714,c_706,c_1415,c_1467,c_1693,c_1772,c_2388,c_2992])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_731,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k1_relat_1(k2_funct_1(X0_48)) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1324,plain,
    ( k1_relat_1(k2_funct_1(X0_48)) = k2_relat_1(X0_48)
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_4263,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4259,c_1324])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_729,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1326,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_2622,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1338,c_1326])).

cnf(c_2626,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2622,c_2418])).

cnf(c_4266,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4263,c_2626])).

cnf(c_5611,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4266,c_41,c_1813])).

cnf(c_6872,plain,
    ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k2_funct_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6864,c_5611])).

cnf(c_7228,plain,
    ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6872,c_1813])).

cnf(c_11976,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k2_funct_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11969,c_7228])).

cnf(c_12346,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11976,c_1813])).

cnf(c_23066,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = k2_funct_1(sK3) ),
    inference(demodulation,[status(thm)],[c_23064,c_12346])).

cnf(c_2623,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1341,c_1326])).

cnf(c_2625,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2623,c_714])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_737,plain,
    ( ~ v1_relat_1(X0_48)
    | k5_relat_1(X0_48,k6_partfun1(k2_relat_1(X0_48))) = X0_48 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1318,plain,
    ( k5_relat_1(X0_48,k6_partfun1(k2_relat_1(X0_48))) = X0_48
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_2221,plain,
    ( k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_1935,c_1318])).

cnf(c_2783,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2625,c_2221])).

cnf(c_23067,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_23066,c_2783])).

cnf(c_18308,plain,
    ( k2_funct_1(sK3) != X0_48
    | sK2 != X0_48
    | sK2 = k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_746])).

cnf(c_18309,plain,
    ( k2_funct_1(sK3) != sK2
    | sK2 = k2_funct_1(sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_18308])).

cnf(c_756,plain,
    ( X0_48 != X1_48
    | k2_funct_1(X0_48) = k2_funct_1(X1_48) ),
    theory(equality)).

cnf(c_7773,plain,
    ( k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
    | sK2 != k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_1413,plain,
    ( k2_funct_1(sK2) != X0_48
    | k2_funct_1(sK2) = sK3
    | sK3 != X0_48 ),
    inference(instantiation,[status(thm)],[c_746])).

cnf(c_5585,plain,
    ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3
    | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1413])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_730,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1930,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_1814,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1813])).

cnf(c_1438,plain,
    ( X0_48 != X1_48
    | sK3 != X1_48
    | sK3 = X0_48 ),
    inference(instantiation,[status(thm)],[c_746])).

cnf(c_1476,plain,
    ( X0_48 != sK3
    | sK3 = X0_48
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1438])).

cnf(c_1688,plain,
    ( k2_funct_1(k2_funct_1(sK3)) != sK3
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_1530,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_26,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_718,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_777,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23067,c_18309,c_7773,c_5585,c_2991,c_2387,c_1930,c_1814,c_1771,c_1693,c_1688,c_1530,c_1467,c_1415,c_706,c_714,c_716,c_718,c_777,c_32,c_33,c_34,c_35,c_36,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:42:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.89/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.89/1.49  
% 7.89/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.89/1.49  
% 7.89/1.49  ------  iProver source info
% 7.89/1.49  
% 7.89/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.89/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.89/1.49  git: non_committed_changes: false
% 7.89/1.49  git: last_make_outside_of_git: false
% 7.89/1.49  
% 7.89/1.49  ------ 
% 7.89/1.49  
% 7.89/1.49  ------ Input Options
% 7.89/1.49  
% 7.89/1.49  --out_options                           all
% 7.89/1.49  --tptp_safe_out                         true
% 7.89/1.49  --problem_path                          ""
% 7.89/1.49  --include_path                          ""
% 7.89/1.49  --clausifier                            res/vclausify_rel
% 7.89/1.49  --clausifier_options                    ""
% 7.89/1.49  --stdin                                 false
% 7.89/1.49  --stats_out                             all
% 7.89/1.49  
% 7.89/1.49  ------ General Options
% 7.89/1.49  
% 7.89/1.49  --fof                                   false
% 7.89/1.49  --time_out_real                         305.
% 7.89/1.49  --time_out_virtual                      -1.
% 7.89/1.49  --symbol_type_check                     false
% 7.89/1.49  --clausify_out                          false
% 7.89/1.49  --sig_cnt_out                           false
% 7.89/1.49  --trig_cnt_out                          false
% 7.89/1.49  --trig_cnt_out_tolerance                1.
% 7.89/1.49  --trig_cnt_out_sk_spl                   false
% 7.89/1.49  --abstr_cl_out                          false
% 7.89/1.49  
% 7.89/1.49  ------ Global Options
% 7.89/1.49  
% 7.89/1.49  --schedule                              default
% 7.89/1.49  --add_important_lit                     false
% 7.89/1.49  --prop_solver_per_cl                    1000
% 7.89/1.49  --min_unsat_core                        false
% 7.89/1.49  --soft_assumptions                      false
% 7.89/1.49  --soft_lemma_size                       3
% 7.89/1.49  --prop_impl_unit_size                   0
% 7.89/1.49  --prop_impl_unit                        []
% 7.89/1.49  --share_sel_clauses                     true
% 7.89/1.49  --reset_solvers                         false
% 7.89/1.49  --bc_imp_inh                            [conj_cone]
% 7.89/1.49  --conj_cone_tolerance                   3.
% 7.89/1.49  --extra_neg_conj                        none
% 7.89/1.49  --large_theory_mode                     true
% 7.89/1.49  --prolific_symb_bound                   200
% 7.89/1.49  --lt_threshold                          2000
% 7.89/1.49  --clause_weak_htbl                      true
% 7.89/1.49  --gc_record_bc_elim                     false
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing Options
% 7.89/1.49  
% 7.89/1.49  --preprocessing_flag                    true
% 7.89/1.49  --time_out_prep_mult                    0.1
% 7.89/1.49  --splitting_mode                        input
% 7.89/1.49  --splitting_grd                         true
% 7.89/1.49  --splitting_cvd                         false
% 7.89/1.49  --splitting_cvd_svl                     false
% 7.89/1.49  --splitting_nvd                         32
% 7.89/1.49  --sub_typing                            true
% 7.89/1.49  --prep_gs_sim                           true
% 7.89/1.49  --prep_unflatten                        true
% 7.89/1.49  --prep_res_sim                          true
% 7.89/1.49  --prep_upred                            true
% 7.89/1.49  --prep_sem_filter                       exhaustive
% 7.89/1.49  --prep_sem_filter_out                   false
% 7.89/1.49  --pred_elim                             true
% 7.89/1.49  --res_sim_input                         true
% 7.89/1.49  --eq_ax_congr_red                       true
% 7.89/1.49  --pure_diseq_elim                       true
% 7.89/1.49  --brand_transform                       false
% 7.89/1.49  --non_eq_to_eq                          false
% 7.89/1.49  --prep_def_merge                        true
% 7.89/1.49  --prep_def_merge_prop_impl              false
% 7.89/1.49  --prep_def_merge_mbd                    true
% 7.89/1.49  --prep_def_merge_tr_red                 false
% 7.89/1.49  --prep_def_merge_tr_cl                  false
% 7.89/1.49  --smt_preprocessing                     true
% 7.89/1.49  --smt_ac_axioms                         fast
% 7.89/1.49  --preprocessed_out                      false
% 7.89/1.49  --preprocessed_stats                    false
% 7.89/1.49  
% 7.89/1.49  ------ Abstraction refinement Options
% 7.89/1.49  
% 7.89/1.49  --abstr_ref                             []
% 7.89/1.49  --abstr_ref_prep                        false
% 7.89/1.49  --abstr_ref_until_sat                   false
% 7.89/1.49  --abstr_ref_sig_restrict                funpre
% 7.89/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.89/1.49  --abstr_ref_under                       []
% 7.89/1.49  
% 7.89/1.49  ------ SAT Options
% 7.89/1.49  
% 7.89/1.49  --sat_mode                              false
% 7.89/1.49  --sat_fm_restart_options                ""
% 7.89/1.49  --sat_gr_def                            false
% 7.89/1.49  --sat_epr_types                         true
% 7.89/1.49  --sat_non_cyclic_types                  false
% 7.89/1.49  --sat_finite_models                     false
% 7.89/1.49  --sat_fm_lemmas                         false
% 7.89/1.49  --sat_fm_prep                           false
% 7.89/1.49  --sat_fm_uc_incr                        true
% 7.89/1.49  --sat_out_model                         small
% 7.89/1.49  --sat_out_clauses                       false
% 7.89/1.49  
% 7.89/1.49  ------ QBF Options
% 7.89/1.49  
% 7.89/1.49  --qbf_mode                              false
% 7.89/1.49  --qbf_elim_univ                         false
% 7.89/1.49  --qbf_dom_inst                          none
% 7.89/1.49  --qbf_dom_pre_inst                      false
% 7.89/1.49  --qbf_sk_in                             false
% 7.89/1.49  --qbf_pred_elim                         true
% 7.89/1.49  --qbf_split                             512
% 7.89/1.49  
% 7.89/1.49  ------ BMC1 Options
% 7.89/1.49  
% 7.89/1.49  --bmc1_incremental                      false
% 7.89/1.49  --bmc1_axioms                           reachable_all
% 7.89/1.49  --bmc1_min_bound                        0
% 7.89/1.49  --bmc1_max_bound                        -1
% 7.89/1.49  --bmc1_max_bound_default                -1
% 7.89/1.49  --bmc1_symbol_reachability              true
% 7.89/1.49  --bmc1_property_lemmas                  false
% 7.89/1.49  --bmc1_k_induction                      false
% 7.89/1.49  --bmc1_non_equiv_states                 false
% 7.89/1.49  --bmc1_deadlock                         false
% 7.89/1.49  --bmc1_ucm                              false
% 7.89/1.49  --bmc1_add_unsat_core                   none
% 7.89/1.49  --bmc1_unsat_core_children              false
% 7.89/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.89/1.49  --bmc1_out_stat                         full
% 7.89/1.49  --bmc1_ground_init                      false
% 7.89/1.49  --bmc1_pre_inst_next_state              false
% 7.89/1.49  --bmc1_pre_inst_state                   false
% 7.89/1.49  --bmc1_pre_inst_reach_state             false
% 7.89/1.49  --bmc1_out_unsat_core                   false
% 7.89/1.49  --bmc1_aig_witness_out                  false
% 7.89/1.49  --bmc1_verbose                          false
% 7.89/1.49  --bmc1_dump_clauses_tptp                false
% 7.89/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.89/1.49  --bmc1_dump_file                        -
% 7.89/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.89/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.89/1.49  --bmc1_ucm_extend_mode                  1
% 7.89/1.49  --bmc1_ucm_init_mode                    2
% 7.89/1.49  --bmc1_ucm_cone_mode                    none
% 7.89/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.89/1.49  --bmc1_ucm_relax_model                  4
% 7.89/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.89/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.89/1.49  --bmc1_ucm_layered_model                none
% 7.89/1.49  --bmc1_ucm_max_lemma_size               10
% 7.89/1.49  
% 7.89/1.49  ------ AIG Options
% 7.89/1.49  
% 7.89/1.49  --aig_mode                              false
% 7.89/1.49  
% 7.89/1.49  ------ Instantiation Options
% 7.89/1.49  
% 7.89/1.49  --instantiation_flag                    true
% 7.89/1.49  --inst_sos_flag                         true
% 7.89/1.49  --inst_sos_phase                        true
% 7.89/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.89/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.89/1.49  --inst_lit_sel_side                     num_symb
% 7.89/1.49  --inst_solver_per_active                1400
% 7.89/1.49  --inst_solver_calls_frac                1.
% 7.89/1.49  --inst_passive_queue_type               priority_queues
% 7.89/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.89/1.49  --inst_passive_queues_freq              [25;2]
% 7.89/1.49  --inst_dismatching                      true
% 7.89/1.49  --inst_eager_unprocessed_to_passive     true
% 7.89/1.49  --inst_prop_sim_given                   true
% 7.89/1.49  --inst_prop_sim_new                     false
% 7.89/1.49  --inst_subs_new                         false
% 7.89/1.49  --inst_eq_res_simp                      false
% 7.89/1.49  --inst_subs_given                       false
% 7.89/1.49  --inst_orphan_elimination               true
% 7.89/1.49  --inst_learning_loop_flag               true
% 7.89/1.49  --inst_learning_start                   3000
% 7.89/1.49  --inst_learning_factor                  2
% 7.89/1.49  --inst_start_prop_sim_after_learn       3
% 7.89/1.49  --inst_sel_renew                        solver
% 7.89/1.49  --inst_lit_activity_flag                true
% 7.89/1.49  --inst_restr_to_given                   false
% 7.89/1.49  --inst_activity_threshold               500
% 7.89/1.49  --inst_out_proof                        true
% 7.89/1.49  
% 7.89/1.49  ------ Resolution Options
% 7.89/1.49  
% 7.89/1.49  --resolution_flag                       true
% 7.89/1.49  --res_lit_sel                           adaptive
% 7.89/1.49  --res_lit_sel_side                      none
% 7.89/1.49  --res_ordering                          kbo
% 7.89/1.49  --res_to_prop_solver                    active
% 7.89/1.49  --res_prop_simpl_new                    false
% 7.89/1.49  --res_prop_simpl_given                  true
% 7.89/1.49  --res_passive_queue_type                priority_queues
% 7.89/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.89/1.49  --res_passive_queues_freq               [15;5]
% 7.89/1.49  --res_forward_subs                      full
% 7.89/1.49  --res_backward_subs                     full
% 7.89/1.49  --res_forward_subs_resolution           true
% 7.89/1.49  --res_backward_subs_resolution          true
% 7.89/1.49  --res_orphan_elimination                true
% 7.89/1.49  --res_time_limit                        2.
% 7.89/1.49  --res_out_proof                         true
% 7.89/1.49  
% 7.89/1.49  ------ Superposition Options
% 7.89/1.49  
% 7.89/1.49  --superposition_flag                    true
% 7.89/1.49  --sup_passive_queue_type                priority_queues
% 7.89/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.89/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.89/1.49  --demod_completeness_check              fast
% 7.89/1.49  --demod_use_ground                      true
% 7.89/1.49  --sup_to_prop_solver                    passive
% 7.89/1.49  --sup_prop_simpl_new                    true
% 7.89/1.49  --sup_prop_simpl_given                  true
% 7.89/1.49  --sup_fun_splitting                     true
% 7.89/1.49  --sup_smt_interval                      50000
% 7.89/1.49  
% 7.89/1.49  ------ Superposition Simplification Setup
% 7.89/1.49  
% 7.89/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.89/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.89/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.89/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.89/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.89/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.89/1.49  --sup_immed_triv                        [TrivRules]
% 7.89/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.49  --sup_immed_bw_main                     []
% 7.89/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.89/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.89/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.49  --sup_input_bw                          []
% 7.89/1.49  
% 7.89/1.49  ------ Combination Options
% 7.89/1.49  
% 7.89/1.49  --comb_res_mult                         3
% 7.89/1.49  --comb_sup_mult                         2
% 7.89/1.49  --comb_inst_mult                        10
% 7.89/1.49  
% 7.89/1.49  ------ Debug Options
% 7.89/1.49  
% 7.89/1.49  --dbg_backtrace                         false
% 7.89/1.49  --dbg_dump_prop_clauses                 false
% 7.89/1.49  --dbg_dump_prop_clauses_file            -
% 7.89/1.49  --dbg_out_stat                          false
% 7.89/1.49  ------ Parsing...
% 7.89/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.49  ------ Proving...
% 7.89/1.49  ------ Problem Properties 
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  clauses                                 37
% 7.89/1.49  conjectures                             11
% 7.89/1.49  EPR                                     7
% 7.89/1.49  Horn                                    33
% 7.89/1.49  unary                                   15
% 7.89/1.49  binary                                  4
% 7.89/1.49  lits                                    131
% 7.89/1.49  lits eq                                 29
% 7.89/1.49  fd_pure                                 0
% 7.89/1.49  fd_pseudo                               0
% 7.89/1.49  fd_cond                                 4
% 7.89/1.49  fd_pseudo_cond                          0
% 7.89/1.49  AC symbols                              0
% 7.89/1.49  
% 7.89/1.49  ------ Schedule dynamic 5 is on 
% 7.89/1.49  
% 7.89/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  ------ 
% 7.89/1.49  Current options:
% 7.89/1.49  ------ 
% 7.89/1.49  
% 7.89/1.49  ------ Input Options
% 7.89/1.49  
% 7.89/1.49  --out_options                           all
% 7.89/1.49  --tptp_safe_out                         true
% 7.89/1.49  --problem_path                          ""
% 7.89/1.49  --include_path                          ""
% 7.89/1.49  --clausifier                            res/vclausify_rel
% 7.89/1.49  --clausifier_options                    ""
% 7.89/1.49  --stdin                                 false
% 7.89/1.49  --stats_out                             all
% 7.89/1.49  
% 7.89/1.49  ------ General Options
% 7.89/1.49  
% 7.89/1.49  --fof                                   false
% 7.89/1.49  --time_out_real                         305.
% 7.89/1.49  --time_out_virtual                      -1.
% 7.89/1.49  --symbol_type_check                     false
% 7.89/1.49  --clausify_out                          false
% 7.89/1.49  --sig_cnt_out                           false
% 7.89/1.49  --trig_cnt_out                          false
% 7.89/1.49  --trig_cnt_out_tolerance                1.
% 7.89/1.49  --trig_cnt_out_sk_spl                   false
% 7.89/1.49  --abstr_cl_out                          false
% 7.89/1.49  
% 7.89/1.49  ------ Global Options
% 7.89/1.49  
% 7.89/1.49  --schedule                              default
% 7.89/1.49  --add_important_lit                     false
% 7.89/1.49  --prop_solver_per_cl                    1000
% 7.89/1.49  --min_unsat_core                        false
% 7.89/1.49  --soft_assumptions                      false
% 7.89/1.49  --soft_lemma_size                       3
% 7.89/1.49  --prop_impl_unit_size                   0
% 7.89/1.49  --prop_impl_unit                        []
% 7.89/1.49  --share_sel_clauses                     true
% 7.89/1.49  --reset_solvers                         false
% 7.89/1.49  --bc_imp_inh                            [conj_cone]
% 7.89/1.49  --conj_cone_tolerance                   3.
% 7.89/1.49  --extra_neg_conj                        none
% 7.89/1.49  --large_theory_mode                     true
% 7.89/1.49  --prolific_symb_bound                   200
% 7.89/1.49  --lt_threshold                          2000
% 7.89/1.49  --clause_weak_htbl                      true
% 7.89/1.49  --gc_record_bc_elim                     false
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing Options
% 7.89/1.49  
% 7.89/1.49  --preprocessing_flag                    true
% 7.89/1.49  --time_out_prep_mult                    0.1
% 7.89/1.49  --splitting_mode                        input
% 7.89/1.49  --splitting_grd                         true
% 7.89/1.49  --splitting_cvd                         false
% 7.89/1.49  --splitting_cvd_svl                     false
% 7.89/1.49  --splitting_nvd                         32
% 7.89/1.49  --sub_typing                            true
% 7.89/1.49  --prep_gs_sim                           true
% 7.89/1.49  --prep_unflatten                        true
% 7.89/1.49  --prep_res_sim                          true
% 7.89/1.49  --prep_upred                            true
% 7.89/1.49  --prep_sem_filter                       exhaustive
% 7.89/1.49  --prep_sem_filter_out                   false
% 7.89/1.49  --pred_elim                             true
% 7.89/1.49  --res_sim_input                         true
% 7.89/1.49  --eq_ax_congr_red                       true
% 7.89/1.49  --pure_diseq_elim                       true
% 7.89/1.49  --brand_transform                       false
% 7.89/1.49  --non_eq_to_eq                          false
% 7.89/1.49  --prep_def_merge                        true
% 7.89/1.49  --prep_def_merge_prop_impl              false
% 7.89/1.49  --prep_def_merge_mbd                    true
% 7.89/1.49  --prep_def_merge_tr_red                 false
% 7.89/1.49  --prep_def_merge_tr_cl                  false
% 7.89/1.49  --smt_preprocessing                     true
% 7.89/1.49  --smt_ac_axioms                         fast
% 7.89/1.49  --preprocessed_out                      false
% 7.89/1.49  --preprocessed_stats                    false
% 7.89/1.49  
% 7.89/1.49  ------ Abstraction refinement Options
% 7.89/1.49  
% 7.89/1.49  --abstr_ref                             []
% 7.89/1.49  --abstr_ref_prep                        false
% 7.89/1.49  --abstr_ref_until_sat                   false
% 7.89/1.49  --abstr_ref_sig_restrict                funpre
% 7.89/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.89/1.49  --abstr_ref_under                       []
% 7.89/1.49  
% 7.89/1.49  ------ SAT Options
% 7.89/1.49  
% 7.89/1.49  --sat_mode                              false
% 7.89/1.49  --sat_fm_restart_options                ""
% 7.89/1.49  --sat_gr_def                            false
% 7.89/1.49  --sat_epr_types                         true
% 7.89/1.49  --sat_non_cyclic_types                  false
% 8.18/1.49  --sat_finite_models                     false
% 8.18/1.49  --sat_fm_lemmas                         false
% 8.18/1.49  --sat_fm_prep                           false
% 8.18/1.49  --sat_fm_uc_incr                        true
% 8.18/1.49  --sat_out_model                         small
% 8.18/1.49  --sat_out_clauses                       false
% 8.18/1.49  
% 8.18/1.49  ------ QBF Options
% 8.18/1.49  
% 8.18/1.49  --qbf_mode                              false
% 8.18/1.49  --qbf_elim_univ                         false
% 8.18/1.49  --qbf_dom_inst                          none
% 8.18/1.49  --qbf_dom_pre_inst                      false
% 8.18/1.49  --qbf_sk_in                             false
% 8.18/1.49  --qbf_pred_elim                         true
% 8.18/1.49  --qbf_split                             512
% 8.18/1.49  
% 8.18/1.49  ------ BMC1 Options
% 8.18/1.49  
% 8.18/1.49  --bmc1_incremental                      false
% 8.18/1.49  --bmc1_axioms                           reachable_all
% 8.18/1.49  --bmc1_min_bound                        0
% 8.18/1.49  --bmc1_max_bound                        -1
% 8.18/1.49  --bmc1_max_bound_default                -1
% 8.18/1.49  --bmc1_symbol_reachability              true
% 8.18/1.49  --bmc1_property_lemmas                  false
% 8.18/1.49  --bmc1_k_induction                      false
% 8.18/1.49  --bmc1_non_equiv_states                 false
% 8.18/1.49  --bmc1_deadlock                         false
% 8.18/1.49  --bmc1_ucm                              false
% 8.18/1.49  --bmc1_add_unsat_core                   none
% 8.18/1.49  --bmc1_unsat_core_children              false
% 8.18/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.18/1.49  --bmc1_out_stat                         full
% 8.18/1.49  --bmc1_ground_init                      false
% 8.18/1.49  --bmc1_pre_inst_next_state              false
% 8.18/1.49  --bmc1_pre_inst_state                   false
% 8.18/1.49  --bmc1_pre_inst_reach_state             false
% 8.18/1.49  --bmc1_out_unsat_core                   false
% 8.18/1.49  --bmc1_aig_witness_out                  false
% 8.18/1.49  --bmc1_verbose                          false
% 8.18/1.49  --bmc1_dump_clauses_tptp                false
% 8.18/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.18/1.49  --bmc1_dump_file                        -
% 8.18/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.18/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.18/1.49  --bmc1_ucm_extend_mode                  1
% 8.18/1.49  --bmc1_ucm_init_mode                    2
% 8.18/1.49  --bmc1_ucm_cone_mode                    none
% 8.18/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.18/1.49  --bmc1_ucm_relax_model                  4
% 8.18/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.18/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.18/1.49  --bmc1_ucm_layered_model                none
% 8.18/1.49  --bmc1_ucm_max_lemma_size               10
% 8.18/1.49  
% 8.18/1.49  ------ AIG Options
% 8.18/1.49  
% 8.18/1.49  --aig_mode                              false
% 8.18/1.49  
% 8.18/1.49  ------ Instantiation Options
% 8.18/1.49  
% 8.18/1.49  --instantiation_flag                    true
% 8.18/1.49  --inst_sos_flag                         true
% 8.18/1.49  --inst_sos_phase                        true
% 8.18/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.18/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.18/1.49  --inst_lit_sel_side                     none
% 8.18/1.49  --inst_solver_per_active                1400
% 8.18/1.49  --inst_solver_calls_frac                1.
% 8.18/1.49  --inst_passive_queue_type               priority_queues
% 8.18/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.18/1.49  --inst_passive_queues_freq              [25;2]
% 8.18/1.49  --inst_dismatching                      true
% 8.18/1.49  --inst_eager_unprocessed_to_passive     true
% 8.18/1.49  --inst_prop_sim_given                   true
% 8.18/1.49  --inst_prop_sim_new                     false
% 8.18/1.49  --inst_subs_new                         false
% 8.18/1.49  --inst_eq_res_simp                      false
% 8.18/1.49  --inst_subs_given                       false
% 8.18/1.49  --inst_orphan_elimination               true
% 8.18/1.49  --inst_learning_loop_flag               true
% 8.18/1.49  --inst_learning_start                   3000
% 8.18/1.49  --inst_learning_factor                  2
% 8.18/1.49  --inst_start_prop_sim_after_learn       3
% 8.18/1.49  --inst_sel_renew                        solver
% 8.18/1.49  --inst_lit_activity_flag                true
% 8.18/1.49  --inst_restr_to_given                   false
% 8.18/1.49  --inst_activity_threshold               500
% 8.18/1.49  --inst_out_proof                        true
% 8.18/1.49  
% 8.18/1.49  ------ Resolution Options
% 8.18/1.49  
% 8.18/1.49  --resolution_flag                       false
% 8.18/1.49  --res_lit_sel                           adaptive
% 8.18/1.49  --res_lit_sel_side                      none
% 8.18/1.49  --res_ordering                          kbo
% 8.18/1.49  --res_to_prop_solver                    active
% 8.18/1.49  --res_prop_simpl_new                    false
% 8.18/1.49  --res_prop_simpl_given                  true
% 8.18/1.49  --res_passive_queue_type                priority_queues
% 8.18/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.18/1.49  --res_passive_queues_freq               [15;5]
% 8.18/1.49  --res_forward_subs                      full
% 8.18/1.49  --res_backward_subs                     full
% 8.18/1.49  --res_forward_subs_resolution           true
% 8.18/1.49  --res_backward_subs_resolution          true
% 8.18/1.49  --res_orphan_elimination                true
% 8.18/1.49  --res_time_limit                        2.
% 8.18/1.49  --res_out_proof                         true
% 8.18/1.49  
% 8.18/1.49  ------ Superposition Options
% 8.18/1.49  
% 8.18/1.49  --superposition_flag                    true
% 8.18/1.49  --sup_passive_queue_type                priority_queues
% 8.18/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.18/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.18/1.49  --demod_completeness_check              fast
% 8.18/1.49  --demod_use_ground                      true
% 8.18/1.49  --sup_to_prop_solver                    passive
% 8.18/1.49  --sup_prop_simpl_new                    true
% 8.18/1.49  --sup_prop_simpl_given                  true
% 8.18/1.49  --sup_fun_splitting                     true
% 8.18/1.49  --sup_smt_interval                      50000
% 8.18/1.49  
% 8.18/1.49  ------ Superposition Simplification Setup
% 8.18/1.49  
% 8.18/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.18/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.18/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.18/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.18/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.18/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.18/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.18/1.49  --sup_immed_triv                        [TrivRules]
% 8.18/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.49  --sup_immed_bw_main                     []
% 8.18/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.18/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.18/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.49  --sup_input_bw                          []
% 8.18/1.49  
% 8.18/1.49  ------ Combination Options
% 8.18/1.49  
% 8.18/1.49  --comb_res_mult                         3
% 8.18/1.49  --comb_sup_mult                         2
% 8.18/1.49  --comb_inst_mult                        10
% 8.18/1.49  
% 8.18/1.49  ------ Debug Options
% 8.18/1.49  
% 8.18/1.49  --dbg_backtrace                         false
% 8.18/1.49  --dbg_dump_prop_clauses                 false
% 8.18/1.49  --dbg_dump_prop_clauses_file            -
% 8.18/1.49  --dbg_out_stat                          false
% 8.18/1.49  
% 8.18/1.49  
% 8.18/1.49  
% 8.18/1.49  
% 8.18/1.49  ------ Proving...
% 8.18/1.49  
% 8.18/1.49  
% 8.18/1.49  % SZS status Theorem for theBenchmark.p
% 8.18/1.49  
% 8.18/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.18/1.49  
% 8.18/1.49  fof(f11,axiom,(
% 8.18/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f32,plain,(
% 8.18/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 8.18/1.49    inference(ennf_transformation,[],[f11])).
% 8.18/1.49  
% 8.18/1.49  fof(f33,plain,(
% 8.18/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.18/1.49    inference(flattening,[],[f32])).
% 8.18/1.49  
% 8.18/1.49  fof(f46,plain,(
% 8.18/1.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.18/1.49    inference(nnf_transformation,[],[f33])).
% 8.18/1.49  
% 8.18/1.49  fof(f63,plain,(
% 8.18/1.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.18/1.49    inference(cnf_transformation,[],[f46])).
% 8.18/1.49  
% 8.18/1.49  fof(f19,conjecture,(
% 8.18/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f20,negated_conjecture,(
% 8.18/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 8.18/1.49    inference(negated_conjecture,[],[f19])).
% 8.18/1.49  
% 8.18/1.49  fof(f44,plain,(
% 8.18/1.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 8.18/1.49    inference(ennf_transformation,[],[f20])).
% 8.18/1.49  
% 8.18/1.49  fof(f45,plain,(
% 8.18/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 8.18/1.49    inference(flattening,[],[f44])).
% 8.18/1.49  
% 8.18/1.49  fof(f48,plain,(
% 8.18/1.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 8.18/1.49    introduced(choice_axiom,[])).
% 8.18/1.49  
% 8.18/1.49  fof(f47,plain,(
% 8.18/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 8.18/1.49    introduced(choice_axiom,[])).
% 8.18/1.49  
% 8.18/1.49  fof(f49,plain,(
% 8.18/1.49    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 8.18/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f48,f47])).
% 8.18/1.49  
% 8.18/1.49  fof(f84,plain,(
% 8.18/1.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 8.18/1.49    inference(cnf_transformation,[],[f49])).
% 8.18/1.49  
% 8.18/1.49  fof(f12,axiom,(
% 8.18/1.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f65,plain,(
% 8.18/1.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 8.18/1.49    inference(cnf_transformation,[],[f12])).
% 8.18/1.49  
% 8.18/1.49  fof(f15,axiom,(
% 8.18/1.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f69,plain,(
% 8.18/1.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 8.18/1.49    inference(cnf_transformation,[],[f15])).
% 8.18/1.49  
% 8.18/1.49  fof(f93,plain,(
% 8.18/1.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 8.18/1.49    inference(definition_unfolding,[],[f65,f69])).
% 8.18/1.49  
% 8.18/1.49  fof(f77,plain,(
% 8.18/1.49    v1_funct_1(sK2)),
% 8.18/1.49    inference(cnf_transformation,[],[f49])).
% 8.18/1.49  
% 8.18/1.49  fof(f79,plain,(
% 8.18/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 8.18/1.49    inference(cnf_transformation,[],[f49])).
% 8.18/1.49  
% 8.18/1.49  fof(f80,plain,(
% 8.18/1.49    v1_funct_1(sK3)),
% 8.18/1.49    inference(cnf_transformation,[],[f49])).
% 8.18/1.49  
% 8.18/1.49  fof(f82,plain,(
% 8.18/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 8.18/1.49    inference(cnf_transformation,[],[f49])).
% 8.18/1.49  
% 8.18/1.49  fof(f13,axiom,(
% 8.18/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f34,plain,(
% 8.18/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 8.18/1.49    inference(ennf_transformation,[],[f13])).
% 8.18/1.49  
% 8.18/1.49  fof(f35,plain,(
% 8.18/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 8.18/1.49    inference(flattening,[],[f34])).
% 8.18/1.49  
% 8.18/1.49  fof(f67,plain,(
% 8.18/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 8.18/1.49    inference(cnf_transformation,[],[f35])).
% 8.18/1.49  
% 8.18/1.49  fof(f16,axiom,(
% 8.18/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f38,plain,(
% 8.18/1.49    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 8.18/1.49    inference(ennf_transformation,[],[f16])).
% 8.18/1.49  
% 8.18/1.49  fof(f39,plain,(
% 8.18/1.49    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 8.18/1.49    inference(flattening,[],[f38])).
% 8.18/1.49  
% 8.18/1.49  fof(f70,plain,(
% 8.18/1.49    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 8.18/1.49    inference(cnf_transformation,[],[f39])).
% 8.18/1.49  
% 8.18/1.49  fof(f78,plain,(
% 8.18/1.49    v1_funct_2(sK2,sK0,sK1)),
% 8.18/1.49    inference(cnf_transformation,[],[f49])).
% 8.18/1.49  
% 8.18/1.49  fof(f81,plain,(
% 8.18/1.49    v1_funct_2(sK3,sK1,sK0)),
% 8.18/1.49    inference(cnf_transformation,[],[f49])).
% 8.18/1.49  
% 8.18/1.49  fof(f18,axiom,(
% 8.18/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f42,plain,(
% 8.18/1.49    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 8.18/1.49    inference(ennf_transformation,[],[f18])).
% 8.18/1.49  
% 8.18/1.49  fof(f43,plain,(
% 8.18/1.49    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 8.18/1.49    inference(flattening,[],[f42])).
% 8.18/1.49  
% 8.18/1.49  fof(f75,plain,(
% 8.18/1.49    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 8.18/1.49    inference(cnf_transformation,[],[f43])).
% 8.18/1.49  
% 8.18/1.49  fof(f86,plain,(
% 8.18/1.49    k1_xboole_0 != sK0),
% 8.18/1.49    inference(cnf_transformation,[],[f49])).
% 8.18/1.49  
% 8.18/1.49  fof(f83,plain,(
% 8.18/1.49    k2_relset_1(sK0,sK1,sK2) = sK1),
% 8.18/1.49    inference(cnf_transformation,[],[f49])).
% 8.18/1.49  
% 8.18/1.49  fof(f17,axiom,(
% 8.18/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f40,plain,(
% 8.18/1.49    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 8.18/1.49    inference(ennf_transformation,[],[f17])).
% 8.18/1.49  
% 8.18/1.49  fof(f41,plain,(
% 8.18/1.49    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 8.18/1.49    inference(flattening,[],[f40])).
% 8.18/1.49  
% 8.18/1.49  fof(f73,plain,(
% 8.18/1.49    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 8.18/1.49    inference(cnf_transformation,[],[f41])).
% 8.18/1.49  
% 8.18/1.49  fof(f7,axiom,(
% 8.18/1.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f58,plain,(
% 8.18/1.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 8.18/1.49    inference(cnf_transformation,[],[f7])).
% 8.18/1.49  
% 8.18/1.49  fof(f91,plain,(
% 8.18/1.49    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 8.18/1.49    inference(definition_unfolding,[],[f58,f69])).
% 8.18/1.49  
% 8.18/1.49  fof(f6,axiom,(
% 8.18/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f25,plain,(
% 8.18/1.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.18/1.49    inference(ennf_transformation,[],[f6])).
% 8.18/1.49  
% 8.18/1.49  fof(f26,plain,(
% 8.18/1.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.18/1.49    inference(flattening,[],[f25])).
% 8.18/1.49  
% 8.18/1.49  fof(f55,plain,(
% 8.18/1.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.18/1.49    inference(cnf_transformation,[],[f26])).
% 8.18/1.49  
% 8.18/1.49  fof(f2,axiom,(
% 8.18/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f51,plain,(
% 8.18/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 8.18/1.49    inference(cnf_transformation,[],[f2])).
% 8.18/1.49  
% 8.18/1.49  fof(f1,axiom,(
% 8.18/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f21,plain,(
% 8.18/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 8.18/1.49    inference(ennf_transformation,[],[f1])).
% 8.18/1.49  
% 8.18/1.49  fof(f50,plain,(
% 8.18/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 8.18/1.49    inference(cnf_transformation,[],[f21])).
% 8.18/1.49  
% 8.18/1.49  fof(f3,axiom,(
% 8.18/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f22,plain,(
% 8.18/1.49    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 8.18/1.49    inference(ennf_transformation,[],[f3])).
% 8.18/1.49  
% 8.18/1.49  fof(f52,plain,(
% 8.18/1.49    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 8.18/1.49    inference(cnf_transformation,[],[f22])).
% 8.18/1.49  
% 8.18/1.49  fof(f14,axiom,(
% 8.18/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f36,plain,(
% 8.18/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 8.18/1.49    inference(ennf_transformation,[],[f14])).
% 8.18/1.49  
% 8.18/1.49  fof(f37,plain,(
% 8.18/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 8.18/1.49    inference(flattening,[],[f36])).
% 8.18/1.49  
% 8.18/1.49  fof(f68,plain,(
% 8.18/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 8.18/1.49    inference(cnf_transformation,[],[f37])).
% 8.18/1.49  
% 8.18/1.49  fof(f4,axiom,(
% 8.18/1.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f23,plain,(
% 8.18/1.49    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 8.18/1.49    inference(ennf_transformation,[],[f4])).
% 8.18/1.49  
% 8.18/1.49  fof(f53,plain,(
% 8.18/1.49    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 8.18/1.49    inference(cnf_transformation,[],[f23])).
% 8.18/1.49  
% 8.18/1.49  fof(f89,plain,(
% 8.18/1.49    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 8.18/1.49    inference(definition_unfolding,[],[f53,f69])).
% 8.18/1.49  
% 8.18/1.49  fof(f8,axiom,(
% 8.18/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f27,plain,(
% 8.18/1.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.18/1.49    inference(ennf_transformation,[],[f8])).
% 8.18/1.49  
% 8.18/1.49  fof(f28,plain,(
% 8.18/1.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.18/1.49    inference(flattening,[],[f27])).
% 8.18/1.49  
% 8.18/1.49  fof(f59,plain,(
% 8.18/1.49    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.18/1.49    inference(cnf_transformation,[],[f28])).
% 8.18/1.49  
% 8.18/1.49  fof(f10,axiom,(
% 8.18/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f31,plain,(
% 8.18/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.18/1.49    inference(ennf_transformation,[],[f10])).
% 8.18/1.49  
% 8.18/1.49  fof(f62,plain,(
% 8.18/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.18/1.49    inference(cnf_transformation,[],[f31])).
% 8.18/1.49  
% 8.18/1.49  fof(f5,axiom,(
% 8.18/1.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f24,plain,(
% 8.18/1.49    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 8.18/1.49    inference(ennf_transformation,[],[f5])).
% 8.18/1.49  
% 8.18/1.49  fof(f54,plain,(
% 8.18/1.49    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 8.18/1.49    inference(cnf_transformation,[],[f24])).
% 8.18/1.49  
% 8.18/1.49  fof(f90,plain,(
% 8.18/1.49    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 8.18/1.49    inference(definition_unfolding,[],[f54,f69])).
% 8.18/1.49  
% 8.18/1.49  fof(f9,axiom,(
% 8.18/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 8.18/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.18/1.49  
% 8.18/1.49  fof(f29,plain,(
% 8.18/1.49    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.18/1.49    inference(ennf_transformation,[],[f9])).
% 8.18/1.49  
% 8.18/1.49  fof(f30,plain,(
% 8.18/1.49    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.18/1.49    inference(flattening,[],[f29])).
% 8.18/1.49  
% 8.18/1.49  fof(f61,plain,(
% 8.18/1.49    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.18/1.49    inference(cnf_transformation,[],[f30])).
% 8.18/1.49  
% 8.18/1.49  fof(f88,plain,(
% 8.18/1.49    k2_funct_1(sK2) != sK3),
% 8.18/1.49    inference(cnf_transformation,[],[f49])).
% 8.18/1.49  
% 8.18/1.49  cnf(c_14,plain,
% 8.18/1.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 8.18/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.18/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.18/1.49      | X3 = X2 ),
% 8.18/1.49      inference(cnf_transformation,[],[f63]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_30,negated_conjecture,
% 8.18/1.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 8.18/1.49      inference(cnf_transformation,[],[f84]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_415,plain,
% 8.18/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.49      | X3 = X0
% 8.18/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 8.18/1.49      | k6_partfun1(sK0) != X3
% 8.18/1.49      | sK0 != X2
% 8.18/1.49      | sK0 != X1 ),
% 8.18/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_416,plain,
% 8.18/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.18/1.49      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.18/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.18/1.49      inference(unflattening,[status(thm)],[c_415]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_15,plain,
% 8.18/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 8.18/1.49      inference(cnf_transformation,[],[f93]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_424,plain,
% 8.18/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.18/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.18/1.49      inference(forward_subsumption_resolution,
% 8.18/1.49                [status(thm)],
% 8.18/1.49                [c_416,c_15]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_706,plain,
% 8.18/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.18/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_424]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1345,plain,
% 8.18/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.18/1.49      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_37,negated_conjecture,
% 8.18/1.49      ( v1_funct_1(sK2) ),
% 8.18/1.49      inference(cnf_transformation,[],[f77]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_35,negated_conjecture,
% 8.18/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 8.18/1.49      inference(cnf_transformation,[],[f79]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_34,negated_conjecture,
% 8.18/1.49      ( v1_funct_1(sK3) ),
% 8.18/1.49      inference(cnf_transformation,[],[f80]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_32,negated_conjecture,
% 8.18/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 8.18/1.49      inference(cnf_transformation,[],[f82]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_16,plain,
% 8.18/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 8.18/1.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 8.18/1.49      | ~ v1_funct_1(X0)
% 8.18/1.49      | ~ v1_funct_1(X3) ),
% 8.18/1.49      inference(cnf_transformation,[],[f67]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_727,plain,
% 8.18/1.49      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 8.18/1.49      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 8.18/1.49      | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
% 8.18/1.49      | ~ v1_funct_1(X0_48)
% 8.18/1.49      | ~ v1_funct_1(X1_48) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1415,plain,
% 8.18/1.49      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.18/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 8.18/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 8.18/1.49      | ~ v1_funct_1(sK3)
% 8.18/1.49      | ~ v1_funct_1(sK2) ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_727]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2044,plain,
% 8.18/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.18/1.49      inference(global_propositional_subsumption,
% 8.18/1.49                [status(thm)],
% 8.18/1.49                [c_1345,c_37,c_35,c_34,c_32,c_706,c_1415]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_19,plain,
% 8.18/1.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 8.18/1.49      | ~ v1_funct_2(X2,X0,X1)
% 8.18/1.49      | ~ v1_funct_2(X3,X1,X0)
% 8.18/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 8.18/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.18/1.49      | ~ v1_funct_1(X2)
% 8.18/1.49      | ~ v1_funct_1(X3)
% 8.18/1.49      | k2_relset_1(X1,X0,X3) = X0 ),
% 8.18/1.49      inference(cnf_transformation,[],[f70]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_428,plain,
% 8.18/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 8.18/1.49      | ~ v1_funct_2(X3,X2,X1)
% 8.18/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 8.18/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.49      | ~ v1_funct_1(X3)
% 8.18/1.49      | ~ v1_funct_1(X0)
% 8.18/1.49      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.18/1.49      | k2_relset_1(X2,X1,X3) = X1
% 8.18/1.49      | k6_partfun1(X1) != k6_partfun1(sK0)
% 8.18/1.49      | sK0 != X1 ),
% 8.18/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_429,plain,
% 8.18/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 8.18/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 8.18/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 8.18/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 8.18/1.49      | ~ v1_funct_1(X2)
% 8.18/1.49      | ~ v1_funct_1(X0)
% 8.18/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.18/1.49      | k2_relset_1(X1,sK0,X0) = sK0
% 8.18/1.49      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 8.18/1.49      inference(unflattening,[status(thm)],[c_428]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_516,plain,
% 8.18/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 8.18/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 8.18/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 8.18/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 8.18/1.49      | ~ v1_funct_1(X0)
% 8.18/1.49      | ~ v1_funct_1(X2)
% 8.18/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.18/1.49      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 8.18/1.49      inference(equality_resolution_simp,[status(thm)],[c_429]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_705,plain,
% 8.18/1.49      ( ~ v1_funct_2(X0_48,X0_49,sK0)
% 8.18/1.49      | ~ v1_funct_2(X1_48,sK0,X0_49)
% 8.18/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
% 8.18/1.49      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
% 8.18/1.49      | ~ v1_funct_1(X0_48)
% 8.18/1.49      | ~ v1_funct_1(X1_48)
% 8.18/1.49      | k2_relset_1(X0_49,sK0,X0_48) = sK0
% 8.18/1.49      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_516]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1346,plain,
% 8.18/1.49      ( k2_relset_1(X0_49,sK0,X0_48) = sK0
% 8.18/1.49      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.18/1.49      | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
% 8.18/1.49      | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
% 8.18/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
% 8.18/1.49      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
% 8.18/1.49      | v1_funct_1(X1_48) != iProver_top
% 8.18/1.49      | v1_funct_1(X0_48) != iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2155,plain,
% 8.18/1.49      ( k2_relset_1(X0_49,sK0,X0_48) = sK0
% 8.18/1.49      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k6_partfun1(sK0)
% 8.18/1.49      | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
% 8.18/1.49      | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
% 8.18/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
% 8.18/1.49      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
% 8.18/1.49      | v1_funct_1(X1_48) != iProver_top
% 8.18/1.49      | v1_funct_1(X0_48) != iProver_top ),
% 8.18/1.49      inference(light_normalisation,[status(thm)],[c_1346,c_2044]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2159,plain,
% 8.18/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 8.18/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 8.18/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 8.18/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 8.18/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 8.18/1.49      | v1_funct_1(sK3) != iProver_top
% 8.18/1.49      | v1_funct_1(sK2) != iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_2044,c_2155]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_36,negated_conjecture,
% 8.18/1.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 8.18/1.49      inference(cnf_transformation,[],[f78]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_33,negated_conjecture,
% 8.18/1.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 8.18/1.49      inference(cnf_transformation,[],[f81]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1423,plain,
% 8.18/1.49      ( ~ v1_funct_2(X0_48,sK0,sK1)
% 8.18/1.49      | ~ v1_funct_2(sK3,sK1,sK0)
% 8.18/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 8.18/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 8.18/1.49      | ~ v1_funct_1(X0_48)
% 8.18/1.49      | ~ v1_funct_1(sK3)
% 8.18/1.49      | k2_relset_1(sK1,sK0,sK3) = sK0
% 8.18/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,X0_48,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_705]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1425,plain,
% 8.18/1.49      ( ~ v1_funct_2(sK3,sK1,sK0)
% 8.18/1.49      | ~ v1_funct_2(sK2,sK0,sK1)
% 8.18/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 8.18/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 8.18/1.49      | ~ v1_funct_1(sK3)
% 8.18/1.49      | ~ v1_funct_1(sK2)
% 8.18/1.49      | k2_relset_1(sK1,sK0,sK3) = sK0
% 8.18/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_1423]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_743,plain,( X0_48 = X0_48 ),theory(equality) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1467,plain,
% 8.18/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_743]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2418,plain,
% 8.18/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 8.18/1.49      inference(global_propositional_subsumption,
% 8.18/1.49                [status(thm)],
% 8.18/1.49                [c_2159,c_37,c_36,c_35,c_34,c_33,c_32,c_1425,c_1467]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_25,plain,
% 8.18/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 8.18/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.49      | ~ v2_funct_1(X0)
% 8.18/1.49      | ~ v1_funct_1(X0)
% 8.18/1.49      | k2_relset_1(X1,X2,X0) != X2
% 8.18/1.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 8.18/1.49      | k1_xboole_0 = X2 ),
% 8.18/1.49      inference(cnf_transformation,[],[f75]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_719,plain,
% 8.18/1.49      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 8.18/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 8.18/1.49      | ~ v2_funct_1(X0_48)
% 8.18/1.49      | ~ v1_funct_1(X0_48)
% 8.18/1.49      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 8.18/1.49      | k1_xboole_0 = X1_49
% 8.18/1.49      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_25]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1336,plain,
% 8.18/1.49      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 8.18/1.49      | k1_xboole_0 = X1_49
% 8.18/1.49      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49)
% 8.18/1.49      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 8.18/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 8.18/1.49      | v2_funct_1(X0_48) != iProver_top
% 8.18/1.49      | v1_funct_1(X0_48) != iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_4165,plain,
% 8.18/1.49      ( sK0 = k1_xboole_0
% 8.18/1.49      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 8.18/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 8.18/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 8.18/1.49      | v2_funct_1(sK3) != iProver_top
% 8.18/1.49      | v1_funct_1(sK3) != iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_2418,c_1336]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_28,negated_conjecture,
% 8.18/1.49      ( k1_xboole_0 != sK0 ),
% 8.18/1.49      inference(cnf_transformation,[],[f86]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_716,negated_conjecture,
% 8.18/1.49      ( k1_xboole_0 != sK0 ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_28]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_31,negated_conjecture,
% 8.18/1.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 8.18/1.49      inference(cnf_transformation,[],[f83]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_714,negated_conjecture,
% 8.18/1.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_31]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1389,plain,
% 8.18/1.49      ( ~ v1_funct_2(X0_48,X0_49,sK0)
% 8.18/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
% 8.18/1.49      | ~ v2_funct_1(X0_48)
% 8.18/1.49      | ~ v1_funct_1(X0_48)
% 8.18/1.49      | k2_relset_1(X0_49,sK0,X0_48) != sK0
% 8.18/1.49      | k1_xboole_0 = sK0
% 8.18/1.49      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_719]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1459,plain,
% 8.18/1.49      ( ~ v1_funct_2(sK3,sK1,sK0)
% 8.18/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 8.18/1.49      | ~ v2_funct_1(sK3)
% 8.18/1.49      | ~ v1_funct_1(sK3)
% 8.18/1.49      | k2_relset_1(sK1,sK0,sK3) != sK0
% 8.18/1.49      | k1_xboole_0 = sK0
% 8.18/1.49      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_1389]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_746,plain,
% 8.18/1.49      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 8.18/1.49      theory(equality) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1481,plain,
% 8.18/1.49      ( X0_48 != X1_48
% 8.18/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_48
% 8.18/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48 ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_746]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1536,plain,
% 8.18/1.49      ( X0_48 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.18/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48
% 8.18/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_1481]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1693,plain,
% 8.18/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.18/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 8.18/1.49      | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_1536]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_21,plain,
% 8.18/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 8.18/1.49      | ~ v1_funct_2(X3,X2,X4)
% 8.18/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 8.18/1.49      | v2_funct_1(X3)
% 8.18/1.49      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 8.18/1.49      | ~ v1_funct_1(X3)
% 8.18/1.49      | ~ v1_funct_1(X0)
% 8.18/1.49      | k2_relset_1(X1,X2,X0) != X2
% 8.18/1.49      | k1_xboole_0 = X4 ),
% 8.18/1.49      inference(cnf_transformation,[],[f73]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_723,plain,
% 8.18/1.49      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 8.18/1.49      | ~ v1_funct_2(X1_48,X1_49,X2_49)
% 8.18/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 8.18/1.49      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 8.18/1.49      | v2_funct_1(X1_48)
% 8.18/1.49      | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,X1_48))
% 8.18/1.49      | ~ v1_funct_1(X0_48)
% 8.18/1.49      | ~ v1_funct_1(X1_48)
% 8.18/1.49      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 8.18/1.49      | k1_xboole_0 = X2_49 ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_21]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1497,plain,
% 8.18/1.49      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 8.18/1.49      | ~ v1_funct_2(sK3,X1_49,X2_49)
% 8.18/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 8.18/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 8.18/1.49      | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,sK3))
% 8.18/1.49      | v2_funct_1(sK3)
% 8.18/1.49      | ~ v1_funct_1(X0_48)
% 8.18/1.49      | ~ v1_funct_1(sK3)
% 8.18/1.49      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 8.18/1.49      | k1_xboole_0 = X2_49 ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_723]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1655,plain,
% 8.18/1.49      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 8.18/1.49      | ~ v1_funct_2(sK3,X1_49,sK0)
% 8.18/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 8.18/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,sK0)))
% 8.18/1.49      | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,sK0,X0_48,sK3))
% 8.18/1.49      | v2_funct_1(sK3)
% 8.18/1.49      | ~ v1_funct_1(X0_48)
% 8.18/1.49      | ~ v1_funct_1(sK3)
% 8.18/1.49      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 8.18/1.49      | k1_xboole_0 = sK0 ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_1497]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1771,plain,
% 8.18/1.49      ( ~ v1_funct_2(sK3,sK1,sK0)
% 8.18/1.49      | ~ v1_funct_2(sK2,sK0,sK1)
% 8.18/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 8.18/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 8.18/1.49      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 8.18/1.49      | v2_funct_1(sK3)
% 8.18/1.49      | ~ v1_funct_1(sK3)
% 8.18/1.49      | ~ v1_funct_1(sK2)
% 8.18/1.49      | k2_relset_1(sK0,sK1,sK2) != sK1
% 8.18/1.49      | k1_xboole_0 = sK0 ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_1655]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_758,plain,
% 8.18/1.49      ( ~ v2_funct_1(X0_48) | v2_funct_1(X1_48) | X1_48 != X0_48 ),
% 8.18/1.49      theory(equality) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1877,plain,
% 8.18/1.49      ( ~ v2_funct_1(X0_48)
% 8.18/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 8.18/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0_48 ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_758]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2387,plain,
% 8.18/1.49      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 8.18/1.49      | ~ v2_funct_1(k6_partfun1(sK0))
% 8.18/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0) ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_1877]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_7,plain,
% 8.18/1.49      ( v2_funct_1(k6_partfun1(X0)) ),
% 8.18/1.49      inference(cnf_transformation,[],[f91]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_734,plain,
% 8.18/1.49      ( v2_funct_1(k6_partfun1(X0_49)) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2991,plain,
% 8.18/1.49      ( v2_funct_1(k6_partfun1(sK0)) ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_734]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_23064,plain,
% 8.18/1.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 8.18/1.49      inference(global_propositional_subsumption,
% 8.18/1.49                [status(thm)],
% 8.18/1.49                [c_4165,c_37,c_36,c_35,c_34,c_33,c_32,c_716,c_714,c_706,
% 8.18/1.49                 c_1415,c_1425,c_1459,c_1467,c_1693,c_1771,c_2387,c_2991]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_711,negated_conjecture,
% 8.18/1.49      ( v1_funct_1(sK3) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_34]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1340,plain,
% 8.18/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_6,plain,
% 8.18/1.49      ( ~ v1_funct_1(X0)
% 8.18/1.49      | ~ v1_relat_1(X0)
% 8.18/1.49      | v1_relat_1(k2_funct_1(X0)) ),
% 8.18/1.49      inference(cnf_transformation,[],[f55]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_735,plain,
% 8.18/1.49      ( ~ v1_funct_1(X0_48)
% 8.18/1.49      | ~ v1_relat_1(X0_48)
% 8.18/1.49      | v1_relat_1(k2_funct_1(X0_48)) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1320,plain,
% 8.18/1.49      ( v1_funct_1(X0_48) != iProver_top
% 8.18/1.49      | v1_relat_1(X0_48) != iProver_top
% 8.18/1.49      | v1_relat_1(k2_funct_1(X0_48)) = iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_735]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1,plain,
% 8.18/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 8.18/1.49      inference(cnf_transformation,[],[f51]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_740,plain,
% 8.18/1.49      ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1315,plain,
% 8.18/1.49      ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) = iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_713,negated_conjecture,
% 8.18/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_32]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1338,plain,
% 8.18/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_0,plain,
% 8.18/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.18/1.49      | ~ v1_relat_1(X1)
% 8.18/1.49      | v1_relat_1(X0) ),
% 8.18/1.49      inference(cnf_transformation,[],[f50]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_741,plain,
% 8.18/1.49      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 8.18/1.49      | ~ v1_relat_1(X1_48)
% 8.18/1.49      | v1_relat_1(X0_48) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1314,plain,
% 8.18/1.49      ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
% 8.18/1.49      | v1_relat_1(X1_48) != iProver_top
% 8.18/1.49      | v1_relat_1(X0_48) = iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1717,plain,
% 8.18/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 8.18/1.49      | v1_relat_1(sK3) = iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1338,c_1314]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1813,plain,
% 8.18/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1315,c_1717]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_710,negated_conjecture,
% 8.18/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_35]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1341,plain,
% 8.18/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1810,plain,
% 8.18/1.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 8.18/1.49      | v1_relat_1(sK2) = iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1341,c_1314]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1935,plain,
% 8.18/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1315,c_1810]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2,plain,
% 8.18/1.49      ( ~ v1_relat_1(X0)
% 8.18/1.49      | ~ v1_relat_1(X1)
% 8.18/1.49      | ~ v1_relat_1(X2)
% 8.18/1.49      | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
% 8.18/1.49      inference(cnf_transformation,[],[f52]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_739,plain,
% 8.18/1.49      ( ~ v1_relat_1(X0_48)
% 8.18/1.49      | ~ v1_relat_1(X1_48)
% 8.18/1.49      | ~ v1_relat_1(X2_48)
% 8.18/1.49      | k5_relat_1(k5_relat_1(X0_48,X2_48),X1_48) = k5_relat_1(X0_48,k5_relat_1(X2_48,X1_48)) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1316,plain,
% 8.18/1.49      ( k5_relat_1(k5_relat_1(X0_48,X1_48),X2_48) = k5_relat_1(X0_48,k5_relat_1(X1_48,X2_48))
% 8.18/1.49      | v1_relat_1(X0_48) != iProver_top
% 8.18/1.49      | v1_relat_1(X1_48) != iProver_top
% 8.18/1.49      | v1_relat_1(X2_48) != iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_3392,plain,
% 8.18/1.49      ( k5_relat_1(sK2,k5_relat_1(X0_48,X1_48)) = k5_relat_1(k5_relat_1(sK2,X0_48),X1_48)
% 8.18/1.49      | v1_relat_1(X0_48) != iProver_top
% 8.18/1.49      | v1_relat_1(X1_48) != iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1935,c_1316]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_5760,plain,
% 8.18/1.49      ( k5_relat_1(k5_relat_1(sK2,sK3),X0_48) = k5_relat_1(sK2,k5_relat_1(sK3,X0_48))
% 8.18/1.49      | v1_relat_1(X0_48) != iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1813,c_3392]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_18,plain,
% 8.18/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 8.18/1.49      | ~ v1_funct_1(X0)
% 8.18/1.49      | ~ v1_funct_1(X3)
% 8.18/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 8.18/1.49      inference(cnf_transformation,[],[f68]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_725,plain,
% 8.18/1.49      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 8.18/1.49      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 8.18/1.49      | ~ v1_funct_1(X0_48)
% 8.18/1.49      | ~ v1_funct_1(X1_48)
% 8.18/1.49      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1330,plain,
% 8.18/1.49      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 8.18/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 8.18/1.49      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 8.18/1.49      | v1_funct_1(X0_48) != iProver_top
% 8.18/1.49      | v1_funct_1(X1_48) != iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_3501,plain,
% 8.18/1.49      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
% 8.18/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 8.18/1.49      | v1_funct_1(X0_48) != iProver_top
% 8.18/1.49      | v1_funct_1(sK3) != iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1338,c_1330]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_41,plain,
% 8.18/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_3670,plain,
% 8.18/1.49      ( v1_funct_1(X0_48) != iProver_top
% 8.18/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 8.18/1.49      | k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3) ),
% 8.18/1.49      inference(global_propositional_subsumption,
% 8.18/1.49                [status(thm)],
% 8.18/1.49                [c_3501,c_41]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_3671,plain,
% 8.18/1.49      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
% 8.18/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 8.18/1.49      | v1_funct_1(X0_48) != iProver_top ),
% 8.18/1.49      inference(renaming,[status(thm)],[c_3670]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_3677,plain,
% 8.18/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 8.18/1.49      | v1_funct_1(sK2) != iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1341,c_3671]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_3680,plain,
% 8.18/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 8.18/1.49      | v1_funct_1(sK2) != iProver_top ),
% 8.18/1.49      inference(light_normalisation,[status(thm)],[c_3677,c_2044]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_38,plain,
% 8.18/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_4049,plain,
% 8.18/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 8.18/1.49      inference(global_propositional_subsumption,
% 8.18/1.49                [status(thm)],
% 8.18/1.49                [c_3680,c_38]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_5762,plain,
% 8.18/1.49      ( k5_relat_1(sK2,k5_relat_1(sK3,X0_48)) = k5_relat_1(k6_partfun1(sK0),X0_48)
% 8.18/1.49      | v1_relat_1(X0_48) != iProver_top ),
% 8.18/1.49      inference(light_normalisation,[status(thm)],[c_5760,c_4049]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_5781,plain,
% 8.18/1.49      ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(X0_48))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(X0_48))
% 8.18/1.49      | v1_funct_1(X0_48) != iProver_top
% 8.18/1.49      | v1_relat_1(X0_48) != iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1320,c_5762]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_11969,plain,
% 8.18/1.49      ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
% 8.18/1.49      | v1_relat_1(sK3) != iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1340,c_5781]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_3,plain,
% 8.18/1.49      ( ~ v1_relat_1(X0)
% 8.18/1.49      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 8.18/1.49      inference(cnf_transformation,[],[f89]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_738,plain,
% 8.18/1.49      ( ~ v1_relat_1(X0_48)
% 8.18/1.49      | k5_relat_1(k6_partfun1(k1_relat_1(X0_48)),X0_48) = X0_48 ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1317,plain,
% 8.18/1.49      ( k5_relat_1(k6_partfun1(k1_relat_1(X0_48)),X0_48) = X0_48
% 8.18/1.49      | v1_relat_1(X0_48) != iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2247,plain,
% 8.18/1.49      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0_48))),k2_funct_1(X0_48)) = k2_funct_1(X0_48)
% 8.18/1.49      | v1_funct_1(X0_48) != iProver_top
% 8.18/1.49      | v1_relat_1(X0_48) != iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1320,c_1317]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_6864,plain,
% 8.18/1.49      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) = k2_funct_1(sK3)
% 8.18/1.49      | v1_relat_1(sK3) != iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1340,c_2247]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1332,plain,
% 8.18/1.49      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 8.18/1.49      | k1_xboole_0 = X2_49
% 8.18/1.49      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 8.18/1.49      | v1_funct_2(X1_48,X1_49,X2_49) != iProver_top
% 8.18/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 8.18/1.49      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
% 8.18/1.49      | v2_funct_1(X1_48) = iProver_top
% 8.18/1.49      | v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,X1_48)) != iProver_top
% 8.18/1.49      | v1_funct_1(X1_48) != iProver_top
% 8.18/1.49      | v1_funct_1(X0_48) != iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_4211,plain,
% 8.18/1.49      ( k1_xboole_0 = X0_49
% 8.18/1.49      | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
% 8.18/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 8.18/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top
% 8.18/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 8.18/1.49      | v2_funct_1(X0_48) = iProver_top
% 8.18/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
% 8.18/1.49      | v1_funct_1(X0_48) != iProver_top
% 8.18/1.49      | v1_funct_1(sK2) != iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_714,c_1332]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_39,plain,
% 8.18/1.49      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_40,plain,
% 8.18/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_4218,plain,
% 8.18/1.49      ( v1_funct_1(X0_48) != iProver_top
% 8.18/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
% 8.18/1.49      | v2_funct_1(X0_48) = iProver_top
% 8.18/1.49      | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
% 8.18/1.49      | k1_xboole_0 = X0_49
% 8.18/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top ),
% 8.18/1.49      inference(global_propositional_subsumption,
% 8.18/1.49                [status(thm)],
% 8.18/1.49                [c_4211,c_38,c_39,c_40]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_4219,plain,
% 8.18/1.49      ( k1_xboole_0 = X0_49
% 8.18/1.49      | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
% 8.18/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top
% 8.18/1.49      | v2_funct_1(X0_48) = iProver_top
% 8.18/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
% 8.18/1.49      | v1_funct_1(X0_48) != iProver_top ),
% 8.18/1.49      inference(renaming,[status(thm)],[c_4218]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_4222,plain,
% 8.18/1.49      ( sK0 = k1_xboole_0
% 8.18/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 8.18/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 8.18/1.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 8.18/1.49      | v2_funct_1(sK3) = iProver_top
% 8.18/1.49      | v1_funct_1(sK3) != iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_2044,c_4219]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_42,plain,
% 8.18/1.49      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_43,plain,
% 8.18/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1772,plain,
% 8.18/1.49      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 8.18/1.49      | k1_xboole_0 = sK0
% 8.18/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 8.18/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 8.18/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 8.18/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 8.18/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) != iProver_top
% 8.18/1.49      | v2_funct_1(sK3) = iProver_top
% 8.18/1.49      | v1_funct_1(sK3) != iProver_top
% 8.18/1.49      | v1_funct_1(sK2) != iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_1771]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2388,plain,
% 8.18/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0)
% 8.18/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) = iProver_top
% 8.18/1.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_2387]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2992,plain,
% 8.18/1.49      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_2991]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_4259,plain,
% 8.18/1.49      ( v2_funct_1(sK3) = iProver_top ),
% 8.18/1.49      inference(global_propositional_subsumption,
% 8.18/1.49                [status(thm)],
% 8.18/1.49                [c_4222,c_37,c_38,c_39,c_35,c_40,c_34,c_41,c_42,c_32,
% 8.18/1.49                 c_43,c_716,c_714,c_706,c_1415,c_1467,c_1693,c_1772,
% 8.18/1.49                 c_2388,c_2992]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_10,plain,
% 8.18/1.49      ( ~ v2_funct_1(X0)
% 8.18/1.49      | ~ v1_funct_1(X0)
% 8.18/1.49      | ~ v1_relat_1(X0)
% 8.18/1.49      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 8.18/1.49      inference(cnf_transformation,[],[f59]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_731,plain,
% 8.18/1.49      ( ~ v2_funct_1(X0_48)
% 8.18/1.49      | ~ v1_funct_1(X0_48)
% 8.18/1.49      | ~ v1_relat_1(X0_48)
% 8.18/1.49      | k1_relat_1(k2_funct_1(X0_48)) = k2_relat_1(X0_48) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1324,plain,
% 8.18/1.49      ( k1_relat_1(k2_funct_1(X0_48)) = k2_relat_1(X0_48)
% 8.18/1.49      | v2_funct_1(X0_48) != iProver_top
% 8.18/1.49      | v1_funct_1(X0_48) != iProver_top
% 8.18/1.49      | v1_relat_1(X0_48) != iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_4263,plain,
% 8.18/1.49      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 8.18/1.49      | v1_funct_1(sK3) != iProver_top
% 8.18/1.49      | v1_relat_1(sK3) != iProver_top ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_4259,c_1324]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_12,plain,
% 8.18/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 8.18/1.49      inference(cnf_transformation,[],[f62]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_729,plain,
% 8.18/1.49      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 8.18/1.49      | k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48) ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1326,plain,
% 8.18/1.49      ( k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48)
% 8.18/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2622,plain,
% 8.18/1.49      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1338,c_1326]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2626,plain,
% 8.18/1.49      ( k2_relat_1(sK3) = sK0 ),
% 8.18/1.49      inference(light_normalisation,[status(thm)],[c_2622,c_2418]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_4266,plain,
% 8.18/1.49      ( k1_relat_1(k2_funct_1(sK3)) = sK0
% 8.18/1.49      | v1_funct_1(sK3) != iProver_top
% 8.18/1.49      | v1_relat_1(sK3) != iProver_top ),
% 8.18/1.49      inference(light_normalisation,[status(thm)],[c_4263,c_2626]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_5611,plain,
% 8.18/1.49      ( k1_relat_1(k2_funct_1(sK3)) = sK0 ),
% 8.18/1.49      inference(global_propositional_subsumption,
% 8.18/1.49                [status(thm)],
% 8.18/1.49                [c_4266,c_41,c_1813]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_6872,plain,
% 8.18/1.49      ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k2_funct_1(sK3)
% 8.18/1.49      | v1_relat_1(sK3) != iProver_top ),
% 8.18/1.49      inference(light_normalisation,[status(thm)],[c_6864,c_5611]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_7228,plain,
% 8.18/1.49      ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k2_funct_1(sK3) ),
% 8.18/1.49      inference(global_propositional_subsumption,
% 8.18/1.49                [status(thm)],
% 8.18/1.49                [c_6872,c_1813]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_11976,plain,
% 8.18/1.49      ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k2_funct_1(sK3)
% 8.18/1.49      | v1_relat_1(sK3) != iProver_top ),
% 8.18/1.49      inference(light_normalisation,[status(thm)],[c_11969,c_7228]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_12346,plain,
% 8.18/1.49      ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k2_funct_1(sK3) ),
% 8.18/1.49      inference(global_propositional_subsumption,
% 8.18/1.49                [status(thm)],
% 8.18/1.49                [c_11976,c_1813]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_23066,plain,
% 8.18/1.49      ( k5_relat_1(sK2,k6_partfun1(sK1)) = k2_funct_1(sK3) ),
% 8.18/1.49      inference(demodulation,[status(thm)],[c_23064,c_12346]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2623,plain,
% 8.18/1.49      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1341,c_1326]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2625,plain,
% 8.18/1.49      ( k2_relat_1(sK2) = sK1 ),
% 8.18/1.49      inference(light_normalisation,[status(thm)],[c_2623,c_714]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_4,plain,
% 8.18/1.49      ( ~ v1_relat_1(X0)
% 8.18/1.49      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 8.18/1.49      inference(cnf_transformation,[],[f90]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_737,plain,
% 8.18/1.49      ( ~ v1_relat_1(X0_48)
% 8.18/1.49      | k5_relat_1(X0_48,k6_partfun1(k2_relat_1(X0_48))) = X0_48 ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1318,plain,
% 8.18/1.49      ( k5_relat_1(X0_48,k6_partfun1(k2_relat_1(X0_48))) = X0_48
% 8.18/1.49      | v1_relat_1(X0_48) != iProver_top ),
% 8.18/1.49      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2221,plain,
% 8.18/1.49      ( k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) = sK2 ),
% 8.18/1.49      inference(superposition,[status(thm)],[c_1935,c_1318]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_2783,plain,
% 8.18/1.49      ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
% 8.18/1.49      inference(demodulation,[status(thm)],[c_2625,c_2221]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_23067,plain,
% 8.18/1.49      ( k2_funct_1(sK3) = sK2 ),
% 8.18/1.49      inference(light_normalisation,[status(thm)],[c_23066,c_2783]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_18308,plain,
% 8.18/1.49      ( k2_funct_1(sK3) != X0_48 | sK2 != X0_48 | sK2 = k2_funct_1(sK3) ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_746]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_18309,plain,
% 8.18/1.49      ( k2_funct_1(sK3) != sK2 | sK2 = k2_funct_1(sK3) | sK2 != sK2 ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_18308]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_756,plain,
% 8.18/1.49      ( X0_48 != X1_48 | k2_funct_1(X0_48) = k2_funct_1(X1_48) ),
% 8.18/1.49      theory(equality) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_7773,plain,
% 8.18/1.49      ( k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
% 8.18/1.49      | sK2 != k2_funct_1(sK3) ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_756]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1413,plain,
% 8.18/1.49      ( k2_funct_1(sK2) != X0_48 | k2_funct_1(sK2) = sK3 | sK3 != X0_48 ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_746]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_5585,plain,
% 8.18/1.49      ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
% 8.18/1.49      | k2_funct_1(sK2) = sK3
% 8.18/1.49      | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_1413]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_11,plain,
% 8.18/1.49      ( ~ v2_funct_1(X0)
% 8.18/1.49      | ~ v1_funct_1(X0)
% 8.18/1.49      | ~ v1_relat_1(X0)
% 8.18/1.49      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 8.18/1.49      inference(cnf_transformation,[],[f61]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_730,plain,
% 8.18/1.49      ( ~ v2_funct_1(X0_48)
% 8.18/1.49      | ~ v1_funct_1(X0_48)
% 8.18/1.49      | ~ v1_relat_1(X0_48)
% 8.18/1.49      | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1930,plain,
% 8.18/1.49      ( ~ v2_funct_1(sK3)
% 8.18/1.49      | ~ v1_funct_1(sK3)
% 8.18/1.49      | ~ v1_relat_1(sK3)
% 8.18/1.49      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_730]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1814,plain,
% 8.18/1.49      ( v1_relat_1(sK3) ),
% 8.18/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1813]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1438,plain,
% 8.18/1.49      ( X0_48 != X1_48 | sK3 != X1_48 | sK3 = X0_48 ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_746]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1476,plain,
% 8.18/1.49      ( X0_48 != sK3 | sK3 = X0_48 | sK3 != sK3 ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_1438]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1688,plain,
% 8.18/1.49      ( k2_funct_1(k2_funct_1(sK3)) != sK3
% 8.18/1.49      | sK3 = k2_funct_1(k2_funct_1(sK3))
% 8.18/1.49      | sK3 != sK3 ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_1476]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_1530,plain,
% 8.18/1.49      ( sK3 = sK3 ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_743]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_26,negated_conjecture,
% 8.18/1.49      ( k2_funct_1(sK2) != sK3 ),
% 8.18/1.49      inference(cnf_transformation,[],[f88]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_718,negated_conjecture,
% 8.18/1.49      ( k2_funct_1(sK2) != sK3 ),
% 8.18/1.49      inference(subtyping,[status(esa)],[c_26]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(c_777,plain,
% 8.18/1.49      ( sK2 = sK2 ),
% 8.18/1.49      inference(instantiation,[status(thm)],[c_743]) ).
% 8.18/1.49  
% 8.18/1.49  cnf(contradiction,plain,
% 8.18/1.49      ( $false ),
% 8.18/1.49      inference(minisat,
% 8.18/1.49                [status(thm)],
% 8.18/1.49                [c_23067,c_18309,c_7773,c_5585,c_2991,c_2387,c_1930,
% 8.18/1.49                 c_1814,c_1771,c_1693,c_1688,c_1530,c_1467,c_1415,c_706,
% 8.18/1.49                 c_714,c_716,c_718,c_777,c_32,c_33,c_34,c_35,c_36,c_37]) ).
% 8.18/1.49  
% 8.18/1.49  
% 8.18/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.18/1.49  
% 8.18/1.49  ------                               Statistics
% 8.18/1.49  
% 8.18/1.49  ------ General
% 8.18/1.49  
% 8.18/1.49  abstr_ref_over_cycles:                  0
% 8.18/1.49  abstr_ref_under_cycles:                 0
% 8.18/1.49  gc_basic_clause_elim:                   0
% 8.18/1.49  forced_gc_time:                         0
% 8.18/1.49  parsing_time:                           0.011
% 8.18/1.49  unif_index_cands_time:                  0.
% 8.18/1.49  unif_index_add_time:                    0.
% 8.18/1.49  orderings_time:                         0.
% 8.18/1.49  out_proof_time:                         0.016
% 8.18/1.49  total_time:                             0.961
% 8.18/1.49  num_of_symbols:                         54
% 8.18/1.49  num_of_terms:                           33633
% 8.18/1.49  
% 8.18/1.49  ------ Preprocessing
% 8.18/1.49  
% 8.18/1.49  num_of_splits:                          0
% 8.18/1.49  num_of_split_atoms:                     0
% 8.18/1.49  num_of_reused_defs:                     0
% 8.18/1.49  num_eq_ax_congr_red:                    0
% 8.18/1.49  num_of_sem_filtered_clauses:            1
% 8.18/1.49  num_of_subtypes:                        3
% 8.18/1.49  monotx_restored_types:                  1
% 8.18/1.49  sat_num_of_epr_types:                   0
% 8.18/1.49  sat_num_of_non_cyclic_types:            0
% 8.18/1.49  sat_guarded_non_collapsed_types:        2
% 8.18/1.49  num_pure_diseq_elim:                    0
% 8.18/1.49  simp_replaced_by:                       0
% 8.18/1.49  res_preprocessed:                       188
% 8.18/1.49  prep_upred:                             0
% 8.18/1.49  prep_unflattend:                        12
% 8.18/1.49  smt_new_axioms:                         0
% 8.18/1.49  pred_elim_cands:                        5
% 8.18/1.49  pred_elim:                              1
% 8.18/1.49  pred_elim_cl:                           1
% 8.18/1.49  pred_elim_cycles:                       3
% 8.18/1.49  merged_defs:                            0
% 8.18/1.49  merged_defs_ncl:                        0
% 8.18/1.49  bin_hyper_res:                          0
% 8.18/1.49  prep_cycles:                            4
% 8.18/1.49  pred_elim_time:                         0.005
% 8.18/1.49  splitting_time:                         0.
% 8.18/1.49  sem_filter_time:                        0.
% 8.18/1.49  monotx_time:                            0.001
% 8.18/1.49  subtype_inf_time:                       0.002
% 8.18/1.49  
% 8.18/1.49  ------ Problem properties
% 8.18/1.49  
% 8.18/1.49  clauses:                                37
% 8.18/1.49  conjectures:                            11
% 8.18/1.49  epr:                                    7
% 8.18/1.49  horn:                                   33
% 8.18/1.49  ground:                                 12
% 8.18/1.49  unary:                                  15
% 8.18/1.49  binary:                                 4
% 8.18/1.49  lits:                                   131
% 8.18/1.49  lits_eq:                                29
% 8.18/1.49  fd_pure:                                0
% 8.18/1.49  fd_pseudo:                              0
% 8.18/1.49  fd_cond:                                4
% 8.18/1.49  fd_pseudo_cond:                         0
% 8.18/1.49  ac_symbols:                             0
% 8.18/1.49  
% 8.18/1.49  ------ Propositional Solver
% 8.18/1.49  
% 8.18/1.49  prop_solver_calls:                      33
% 8.18/1.49  prop_fast_solver_calls:                 2066
% 8.18/1.49  smt_solver_calls:                       0
% 8.18/1.49  smt_fast_solver_calls:                  0
% 8.18/1.49  prop_num_of_clauses:                    11491
% 8.18/1.49  prop_preprocess_simplified:             22285
% 8.18/1.49  prop_fo_subsumed:                       127
% 8.18/1.49  prop_solver_time:                       0.
% 8.18/1.49  smt_solver_time:                        0.
% 8.18/1.49  smt_fast_solver_time:                   0.
% 8.18/1.49  prop_fast_solver_time:                  0.
% 8.18/1.49  prop_unsat_core_time:                   0.001
% 8.18/1.49  
% 8.18/1.49  ------ QBF
% 8.18/1.49  
% 8.18/1.49  qbf_q_res:                              0
% 8.18/1.49  qbf_num_tautologies:                    0
% 8.18/1.49  qbf_prep_cycles:                        0
% 8.18/1.49  
% 8.18/1.49  ------ BMC1
% 8.18/1.49  
% 8.18/1.49  bmc1_current_bound:                     -1
% 8.18/1.49  bmc1_last_solved_bound:                 -1
% 8.18/1.49  bmc1_unsat_core_size:                   -1
% 8.18/1.49  bmc1_unsat_core_parents_size:           -1
% 8.18/1.49  bmc1_merge_next_fun:                    0
% 8.18/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.18/1.49  
% 8.18/1.49  ------ Instantiation
% 8.18/1.49  
% 8.18/1.49  inst_num_of_clauses:                    3588
% 8.18/1.49  inst_num_in_passive:                    668
% 8.18/1.49  inst_num_in_active:                     1455
% 8.18/1.49  inst_num_in_unprocessed:                1465
% 8.18/1.49  inst_num_of_loops:                      1540
% 8.18/1.49  inst_num_of_learning_restarts:          0
% 8.18/1.49  inst_num_moves_active_passive:          78
% 8.18/1.49  inst_lit_activity:                      0
% 8.18/1.49  inst_lit_activity_moves:                0
% 8.18/1.49  inst_num_tautologies:                   0
% 8.18/1.49  inst_num_prop_implied:                  0
% 8.18/1.49  inst_num_existing_simplified:           0
% 8.18/1.49  inst_num_eq_res_simplified:             0
% 8.18/1.49  inst_num_child_elim:                    0
% 8.18/1.49  inst_num_of_dismatching_blockings:      761
% 8.18/1.49  inst_num_of_non_proper_insts:           3191
% 8.18/1.49  inst_num_of_duplicates:                 0
% 8.18/1.49  inst_inst_num_from_inst_to_res:         0
% 8.18/1.49  inst_dismatching_checking_time:         0.
% 8.18/1.49  
% 8.18/1.49  ------ Resolution
% 8.18/1.49  
% 8.18/1.49  res_num_of_clauses:                     0
% 8.18/1.49  res_num_in_passive:                     0
% 8.18/1.49  res_num_in_active:                      0
% 8.18/1.49  res_num_of_loops:                       192
% 8.18/1.49  res_forward_subset_subsumed:            531
% 8.18/1.49  res_backward_subset_subsumed:           2
% 8.18/1.49  res_forward_subsumed:                   0
% 8.18/1.49  res_backward_subsumed:                  0
% 8.18/1.49  res_forward_subsumption_resolution:     2
% 8.18/1.49  res_backward_subsumption_resolution:    0
% 8.18/1.49  res_clause_to_clause_subsumption:       1470
% 8.18/1.49  res_orphan_elimination:                 0
% 8.18/1.49  res_tautology_del:                      196
% 8.18/1.49  res_num_eq_res_simplified:              1
% 8.18/1.49  res_num_sel_changes:                    0
% 8.18/1.49  res_moves_from_active_to_pass:          0
% 8.18/1.49  
% 8.18/1.49  ------ Superposition
% 8.18/1.49  
% 8.18/1.49  sup_time_total:                         0.
% 8.18/1.49  sup_time_generating:                    0.
% 8.18/1.49  sup_time_sim_full:                      0.
% 8.18/1.49  sup_time_sim_immed:                     0.
% 8.18/1.49  
% 8.18/1.49  sup_num_of_clauses:                     714
% 8.18/1.49  sup_num_in_active:                      282
% 8.18/1.49  sup_num_in_passive:                     432
% 8.18/1.49  sup_num_of_loops:                       307
% 8.18/1.49  sup_fw_superposition:                   583
% 8.18/1.49  sup_bw_superposition:                   167
% 8.18/1.49  sup_immediate_simplified:               193
% 8.18/1.49  sup_given_eliminated:                   0
% 8.18/1.49  comparisons_done:                       0
% 8.18/1.49  comparisons_avoided:                    0
% 8.18/1.49  
% 8.18/1.49  ------ Simplifications
% 8.18/1.49  
% 8.18/1.49  
% 8.18/1.49  sim_fw_subset_subsumed:                 17
% 8.18/1.49  sim_bw_subset_subsumed:                 21
% 8.18/1.49  sim_fw_subsumed:                        13
% 8.18/1.49  sim_bw_subsumed:                        2
% 8.18/1.49  sim_fw_subsumption_res:                 0
% 8.18/1.49  sim_bw_subsumption_res:                 0
% 8.18/1.49  sim_tautology_del:                      2
% 8.18/1.49  sim_eq_tautology_del:                   18
% 8.18/1.49  sim_eq_res_simp:                        0
% 8.18/1.49  sim_fw_demodulated:                     17
% 8.18/1.49  sim_bw_demodulated:                     15
% 8.18/1.49  sim_light_normalised:                   162
% 8.18/1.49  sim_joinable_taut:                      0
% 8.18/1.49  sim_joinable_simp:                      0
% 8.18/1.49  sim_ac_normalised:                      0
% 8.18/1.49  sim_smt_subsumption:                    0
% 8.18/1.49  
%------------------------------------------------------------------------------
