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
% DateTime   : Thu Dec  3 12:02:12 EST 2020

% Result     : Theorem 23.56s
% Output     : CNFRefutation 23.56s
% Verified   : 
% Statistics : Number of formulae       :  228 (1212 expanded)
%              Number of clauses        :  135 ( 369 expanded)
%              Number of leaves         :   27 ( 303 expanded)
%              Depth                    :   20
%              Number of atoms          :  684 (7176 expanded)
%              Number of equality atoms :  244 ( 604 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK3,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f53,f52])).

fof(f92,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f77,f83])).

fof(f86,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f41])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f103,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f79])).

fof(f93,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f73,f83])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f94,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f72,f83])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1156,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_31,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_385,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_22,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_393,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_385,c_22])).

cnf(c_1144,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_3132,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1156,c_1144])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_11355,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3132,c_38,c_40,c_41,c_43])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1152,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11365,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_11355,c_1152])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_30,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_402,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_403,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_456,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X1
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_403])).

cnf(c_457,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_467,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_457,c_2])).

cnf(c_468,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1677,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_11,c_32])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1934,plain,
    ( v1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1677,c_14])).

cnf(c_1935,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1934])).

cnf(c_1151,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_13])).

cnf(c_1143,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(c_2330,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1143])).

cnf(c_3612,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2330,c_1935])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1165,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3616,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3612,c_1165])).

cnf(c_1148,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1154,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3061,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1154])).

cnf(c_7214,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3061,c_41])).

cnf(c_7215,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7214])).

cnf(c_7223,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_7215])).

cnf(c_1351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X3,X4,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1609,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_2239,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1609])).

cnf(c_3527,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2239])).

cnf(c_7664,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7223,c_37,c_35,c_34,c_32,c_3527])).

cnf(c_7669,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7664,c_1152])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_39,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X3,X4,X1,X2,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1629,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1341])).

cnf(c_2259,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1629])).

cnf(c_3594,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2259])).

cnf(c_4354,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_37,c_35,c_34,c_32,c_3594])).

cnf(c_659,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4568,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(k6_partfun1(sK0)) ),
    inference(resolution,[status(thm)],[c_4354,c_659])).

cnf(c_4579,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4568])).

cnf(c_650,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_649,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3233,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_650,c_649])).

cnf(c_6363,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[status(thm)],[c_3233,c_4354])).

cnf(c_7253,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v2_funct_1(k6_partfun1(sK0)) ),
    inference(resolution,[status(thm)],[c_6363,c_659])).

cnf(c_18,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_7508,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7253,c_18])).

cnf(c_7509,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7508])).

cnf(c_41767,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7669,c_38,c_39,c_40,c_41,c_42,c_43,c_4579,c_7509,c_11365])).

cnf(c_16,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_11363,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(superposition,[status(thm)],[c_11355,c_7664])).

cnf(c_15,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1159,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_87412,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11363,c_1159])).

cnf(c_1679,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_11,c_35])).

cnf(c_1941,plain,
    ( v1_relat_1(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1679,c_14])).

cnf(c_1942,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1941])).

cnf(c_87486,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_87412,c_1935,c_1942])).

cnf(c_87490,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_87486])).

cnf(c_87660,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11365,c_468,c_1935,c_3616,c_41767,c_87490])).

cnf(c_87765,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_87660,c_1148])).

cnf(c_89325,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_87765])).

cnf(c_2457,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_5252,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2457])).

cnf(c_5253,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_5252])).

cnf(c_4018,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_4019,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4018])).

cnf(c_4021,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4019])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2698,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2700,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2698])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1157,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2460,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1157])).

cnf(c_2463,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2460])).

cnf(c_1816,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1817,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1816])).

cnf(c_1819,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1555,plain,
    ( ~ v1_xboole_0(k6_partfun1(X0))
    | k1_xboole_0 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1559,plain,
    ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_1452,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_1400,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1403,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1400])).

cnf(c_1270,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_1271,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1270])).

cnf(c_1273,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_106,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_108,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_107,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_103,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_105,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_104,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_100,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_102,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_101,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_79,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_81,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_89325,c_87490,c_5253,c_4021,c_3616,c_2700,c_2463,c_1935,c_1819,c_1559,c_1452,c_1403,c_1273,c_468,c_108,c_107,c_105,c_104,c_102,c_101,c_81])).

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
% 0.14/0.34  % DateTime   : Tue Dec  1 16:07:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 23.56/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.56/3.50  
% 23.56/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.56/3.50  
% 23.56/3.50  ------  iProver source info
% 23.56/3.50  
% 23.56/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.56/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.56/3.50  git: non_committed_changes: false
% 23.56/3.50  git: last_make_outside_of_git: false
% 23.56/3.50  
% 23.56/3.50  ------ 
% 23.56/3.50  ------ Parsing...
% 23.56/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.56/3.50  
% 23.56/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 23.56/3.50  
% 23.56/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.56/3.50  
% 23.56/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.56/3.50  ------ Proving...
% 23.56/3.50  ------ Problem Properties 
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  clauses                                 30
% 23.56/3.50  conjectures                             6
% 23.56/3.50  EPR                                     9
% 23.56/3.50  Horn                                    28
% 23.56/3.50  unary                                   15
% 23.56/3.50  binary                                  3
% 23.56/3.50  lits                                    74
% 23.56/3.50  lits eq                                 13
% 23.56/3.50  fd_pure                                 0
% 23.56/3.50  fd_pseudo                               0
% 23.56/3.50  fd_cond                                 3
% 23.56/3.50  fd_pseudo_cond                          1
% 23.56/3.50  AC symbols                              0
% 23.56/3.50  
% 23.56/3.50  ------ Input Options Time Limit: Unbounded
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  ------ 
% 23.56/3.50  Current options:
% 23.56/3.50  ------ 
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  ------ Proving...
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  % SZS status Theorem for theBenchmark.p
% 23.56/3.50  
% 23.56/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.56/3.50  
% 23.56/3.50  fof(f6,axiom,(
% 23.56/3.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f47,plain,(
% 23.56/3.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 23.56/3.50    inference(nnf_transformation,[],[f6])).
% 23.56/3.50  
% 23.56/3.50  fof(f48,plain,(
% 23.56/3.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 23.56/3.50    inference(flattening,[],[f47])).
% 23.56/3.50  
% 23.56/3.50  fof(f63,plain,(
% 23.56/3.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 23.56/3.50    inference(cnf_transformation,[],[f48])).
% 23.56/3.50  
% 23.56/3.50  fof(f101,plain,(
% 23.56/3.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 23.56/3.50    inference(equality_resolution,[],[f63])).
% 23.56/3.50  
% 23.56/3.50  fof(f18,axiom,(
% 23.56/3.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f37,plain,(
% 23.56/3.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 23.56/3.50    inference(ennf_transformation,[],[f18])).
% 23.56/3.50  
% 23.56/3.50  fof(f38,plain,(
% 23.56/3.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 23.56/3.50    inference(flattening,[],[f37])).
% 23.56/3.50  
% 23.56/3.50  fof(f81,plain,(
% 23.56/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f38])).
% 23.56/3.50  
% 23.56/3.50  fof(f15,axiom,(
% 23.56/3.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f33,plain,(
% 23.56/3.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 23.56/3.50    inference(ennf_transformation,[],[f15])).
% 23.56/3.50  
% 23.56/3.50  fof(f34,plain,(
% 23.56/3.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.56/3.50    inference(flattening,[],[f33])).
% 23.56/3.50  
% 23.56/3.50  fof(f50,plain,(
% 23.56/3.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.56/3.50    inference(nnf_transformation,[],[f34])).
% 23.56/3.50  
% 23.56/3.50  fof(f75,plain,(
% 23.56/3.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.56/3.50    inference(cnf_transformation,[],[f50])).
% 23.56/3.50  
% 23.56/3.50  fof(f22,conjecture,(
% 23.56/3.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f23,negated_conjecture,(
% 23.56/3.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 23.56/3.50    inference(negated_conjecture,[],[f22])).
% 23.56/3.50  
% 23.56/3.50  fof(f43,plain,(
% 23.56/3.50    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 23.56/3.50    inference(ennf_transformation,[],[f23])).
% 23.56/3.50  
% 23.56/3.50  fof(f44,plain,(
% 23.56/3.50    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 23.56/3.50    inference(flattening,[],[f43])).
% 23.56/3.50  
% 23.56/3.50  fof(f53,plain,(
% 23.56/3.50    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 23.56/3.50    introduced(choice_axiom,[])).
% 23.56/3.50  
% 23.56/3.50  fof(f52,plain,(
% 23.56/3.50    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 23.56/3.50    introduced(choice_axiom,[])).
% 23.56/3.50  
% 23.56/3.50  fof(f54,plain,(
% 23.56/3.50    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 23.56/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f53,f52])).
% 23.56/3.50  
% 23.56/3.50  fof(f92,plain,(
% 23.56/3.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 23.56/3.50    inference(cnf_transformation,[],[f54])).
% 23.56/3.50  
% 23.56/3.50  fof(f16,axiom,(
% 23.56/3.50    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f77,plain,(
% 23.56/3.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 23.56/3.50    inference(cnf_transformation,[],[f16])).
% 23.56/3.50  
% 23.56/3.50  fof(f20,axiom,(
% 23.56/3.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f83,plain,(
% 23.56/3.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f20])).
% 23.56/3.50  
% 23.56/3.50  fof(f97,plain,(
% 23.56/3.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 23.56/3.50    inference(definition_unfolding,[],[f77,f83])).
% 23.56/3.50  
% 23.56/3.50  fof(f86,plain,(
% 23.56/3.50    v1_funct_1(sK2)),
% 23.56/3.50    inference(cnf_transformation,[],[f54])).
% 23.56/3.50  
% 23.56/3.50  fof(f88,plain,(
% 23.56/3.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 23.56/3.50    inference(cnf_transformation,[],[f54])).
% 23.56/3.50  
% 23.56/3.50  fof(f89,plain,(
% 23.56/3.50    v1_funct_1(sK3)),
% 23.56/3.50    inference(cnf_transformation,[],[f54])).
% 23.56/3.50  
% 23.56/3.50  fof(f91,plain,(
% 23.56/3.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 23.56/3.50    inference(cnf_transformation,[],[f54])).
% 23.56/3.50  
% 23.56/3.50  fof(f21,axiom,(
% 23.56/3.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f41,plain,(
% 23.56/3.50    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 23.56/3.50    inference(ennf_transformation,[],[f21])).
% 23.56/3.50  
% 23.56/3.50  fof(f42,plain,(
% 23.56/3.50    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 23.56/3.50    inference(flattening,[],[f41])).
% 23.56/3.50  
% 23.56/3.50  fof(f84,plain,(
% 23.56/3.50    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f42])).
% 23.56/3.50  
% 23.56/3.50  fof(f9,axiom,(
% 23.56/3.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f30,plain,(
% 23.56/3.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 23.56/3.50    inference(ennf_transformation,[],[f9])).
% 23.56/3.50  
% 23.56/3.50  fof(f49,plain,(
% 23.56/3.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 23.56/3.50    inference(nnf_transformation,[],[f30])).
% 23.56/3.50  
% 23.56/3.50  fof(f68,plain,(
% 23.56/3.50    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f49])).
% 23.56/3.50  
% 23.56/3.50  fof(f17,axiom,(
% 23.56/3.50    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f35,plain,(
% 23.56/3.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 23.56/3.50    inference(ennf_transformation,[],[f17])).
% 23.56/3.50  
% 23.56/3.50  fof(f36,plain,(
% 23.56/3.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 23.56/3.50    inference(flattening,[],[f35])).
% 23.56/3.50  
% 23.56/3.50  fof(f51,plain,(
% 23.56/3.50    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 23.56/3.50    inference(nnf_transformation,[],[f36])).
% 23.56/3.50  
% 23.56/3.50  fof(f79,plain,(
% 23.56/3.50    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f51])).
% 23.56/3.50  
% 23.56/3.50  fof(f103,plain,(
% 23.56/3.50    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 23.56/3.50    inference(equality_resolution,[],[f79])).
% 23.56/3.50  
% 23.56/3.50  fof(f93,plain,(
% 23.56/3.50    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 23.56/3.50    inference(cnf_transformation,[],[f54])).
% 23.56/3.50  
% 23.56/3.50  fof(f2,axiom,(
% 23.56/3.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f45,plain,(
% 23.56/3.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.56/3.50    inference(nnf_transformation,[],[f2])).
% 23.56/3.50  
% 23.56/3.50  fof(f46,plain,(
% 23.56/3.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.56/3.50    inference(flattening,[],[f45])).
% 23.56/3.50  
% 23.56/3.50  fof(f57,plain,(
% 23.56/3.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 23.56/3.50    inference(cnf_transformation,[],[f46])).
% 23.56/3.50  
% 23.56/3.50  fof(f98,plain,(
% 23.56/3.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.56/3.50    inference(equality_resolution,[],[f57])).
% 23.56/3.50  
% 23.56/3.50  fof(f8,axiom,(
% 23.56/3.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f29,plain,(
% 23.56/3.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 23.56/3.50    inference(ennf_transformation,[],[f8])).
% 23.56/3.50  
% 23.56/3.50  fof(f66,plain,(
% 23.56/3.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f29])).
% 23.56/3.50  
% 23.56/3.50  fof(f10,axiom,(
% 23.56/3.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f69,plain,(
% 23.56/3.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 23.56/3.50    inference(cnf_transformation,[],[f10])).
% 23.56/3.50  
% 23.56/3.50  fof(f14,axiom,(
% 23.56/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f24,plain,(
% 23.56/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 23.56/3.50    inference(pure_predicate_removal,[],[f14])).
% 23.56/3.50  
% 23.56/3.50  fof(f32,plain,(
% 23.56/3.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.56/3.50    inference(ennf_transformation,[],[f24])).
% 23.56/3.50  
% 23.56/3.50  fof(f74,plain,(
% 23.56/3.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.56/3.50    inference(cnf_transformation,[],[f32])).
% 23.56/3.50  
% 23.56/3.50  fof(f67,plain,(
% 23.56/3.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f49])).
% 23.56/3.50  
% 23.56/3.50  fof(f58,plain,(
% 23.56/3.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f46])).
% 23.56/3.50  
% 23.56/3.50  fof(f19,axiom,(
% 23.56/3.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f39,plain,(
% 23.56/3.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 23.56/3.50    inference(ennf_transformation,[],[f19])).
% 23.56/3.50  
% 23.56/3.50  fof(f40,plain,(
% 23.56/3.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 23.56/3.50    inference(flattening,[],[f39])).
% 23.56/3.50  
% 23.56/3.50  fof(f82,plain,(
% 23.56/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f40])).
% 23.56/3.50  
% 23.56/3.50  fof(f87,plain,(
% 23.56/3.50    v1_funct_2(sK2,sK0,sK1)),
% 23.56/3.50    inference(cnf_transformation,[],[f54])).
% 23.56/3.50  
% 23.56/3.50  fof(f90,plain,(
% 23.56/3.50    v1_funct_2(sK3,sK1,sK0)),
% 23.56/3.50    inference(cnf_transformation,[],[f54])).
% 23.56/3.50  
% 23.56/3.50  fof(f13,axiom,(
% 23.56/3.50    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f73,plain,(
% 23.56/3.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 23.56/3.50    inference(cnf_transformation,[],[f13])).
% 23.56/3.50  
% 23.56/3.50  fof(f96,plain,(
% 23.56/3.50    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 23.56/3.50    inference(definition_unfolding,[],[f73,f83])).
% 23.56/3.50  
% 23.56/3.50  fof(f12,axiom,(
% 23.56/3.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f72,plain,(
% 23.56/3.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 23.56/3.50    inference(cnf_transformation,[],[f12])).
% 23.56/3.50  
% 23.56/3.50  fof(f94,plain,(
% 23.56/3.50    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 23.56/3.50    inference(definition_unfolding,[],[f72,f83])).
% 23.56/3.50  
% 23.56/3.50  fof(f11,axiom,(
% 23.56/3.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f31,plain,(
% 23.56/3.50    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 23.56/3.50    inference(ennf_transformation,[],[f11])).
% 23.56/3.50  
% 23.56/3.50  fof(f70,plain,(
% 23.56/3.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f31])).
% 23.56/3.50  
% 23.56/3.50  fof(f7,axiom,(
% 23.56/3.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f28,plain,(
% 23.56/3.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 23.56/3.50    inference(ennf_transformation,[],[f7])).
% 23.56/3.50  
% 23.56/3.50  fof(f65,plain,(
% 23.56/3.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f28])).
% 23.56/3.50  
% 23.56/3.50  fof(f64,plain,(
% 23.56/3.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 23.56/3.50    inference(cnf_transformation,[],[f48])).
% 23.56/3.50  
% 23.56/3.50  fof(f100,plain,(
% 23.56/3.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 23.56/3.50    inference(equality_resolution,[],[f64])).
% 23.56/3.50  
% 23.56/3.50  fof(f1,axiom,(
% 23.56/3.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f25,plain,(
% 23.56/3.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 23.56/3.50    inference(ennf_transformation,[],[f1])).
% 23.56/3.50  
% 23.56/3.50  fof(f55,plain,(
% 23.56/3.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f25])).
% 23.56/3.50  
% 23.56/3.50  fof(f3,axiom,(
% 23.56/3.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f59,plain,(
% 23.56/3.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f3])).
% 23.56/3.50  
% 23.56/3.50  fof(f4,axiom,(
% 23.56/3.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f60,plain,(
% 23.56/3.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f4])).
% 23.56/3.50  
% 23.56/3.50  fof(f5,axiom,(
% 23.56/3.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f26,plain,(
% 23.56/3.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 23.56/3.50    inference(ennf_transformation,[],[f5])).
% 23.56/3.50  
% 23.56/3.50  fof(f27,plain,(
% 23.56/3.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 23.56/3.50    inference(flattening,[],[f26])).
% 23.56/3.50  
% 23.56/3.50  fof(f61,plain,(
% 23.56/3.50    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f27])).
% 23.56/3.50  
% 23.56/3.50  cnf(c_8,plain,
% 23.56/3.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 23.56/3.50      inference(cnf_transformation,[],[f101]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_25,plain,
% 23.56/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.56/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 23.56/3.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 23.56/3.50      | ~ v1_funct_1(X0)
% 23.56/3.50      | ~ v1_funct_1(X3) ),
% 23.56/3.50      inference(cnf_transformation,[],[f81]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1156,plain,
% 23.56/3.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.56/3.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 23.56/3.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 23.56/3.50      | v1_funct_1(X0) != iProver_top
% 23.56/3.50      | v1_funct_1(X3) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_21,plain,
% 23.56/3.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 23.56/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.56/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.56/3.50      | X3 = X2 ),
% 23.56/3.50      inference(cnf_transformation,[],[f75]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_31,negated_conjecture,
% 23.56/3.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 23.56/3.50      inference(cnf_transformation,[],[f92]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_384,plain,
% 23.56/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.56/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.56/3.50      | X3 = X0
% 23.56/3.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 23.56/3.50      | k6_partfun1(sK0) != X3
% 23.56/3.50      | sK0 != X2
% 23.56/3.50      | sK0 != X1 ),
% 23.56/3.50      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_385,plain,
% 23.56/3.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.56/3.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.56/3.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.56/3.50      inference(unflattening,[status(thm)],[c_384]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_22,plain,
% 23.56/3.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 23.56/3.50      inference(cnf_transformation,[],[f97]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_393,plain,
% 23.56/3.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.56/3.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.56/3.50      inference(forward_subsumption_resolution,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_385,c_22]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1144,plain,
% 23.56/3.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 23.56/3.50      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3132,plain,
% 23.56/3.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 23.56/3.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.56/3.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 23.56/3.50      | v1_funct_1(sK2) != iProver_top
% 23.56/3.50      | v1_funct_1(sK3) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_1156,c_1144]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_37,negated_conjecture,
% 23.56/3.50      ( v1_funct_1(sK2) ),
% 23.56/3.50      inference(cnf_transformation,[],[f86]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_38,plain,
% 23.56/3.50      ( v1_funct_1(sK2) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_35,negated_conjecture,
% 23.56/3.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 23.56/3.50      inference(cnf_transformation,[],[f88]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_40,plain,
% 23.56/3.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_34,negated_conjecture,
% 23.56/3.50      ( v1_funct_1(sK3) ),
% 23.56/3.50      inference(cnf_transformation,[],[f89]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_41,plain,
% 23.56/3.50      ( v1_funct_1(sK3) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_32,negated_conjecture,
% 23.56/3.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 23.56/3.50      inference(cnf_transformation,[],[f91]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_43,plain,
% 23.56/3.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_11355,plain,
% 23.56/3.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_3132,c_38,c_40,c_41,c_43]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_29,plain,
% 23.56/3.50      ( ~ v1_funct_2(X0,X1,X2)
% 23.56/3.50      | ~ v1_funct_2(X3,X4,X1)
% 23.56/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 23.56/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.56/3.50      | ~ v1_funct_1(X0)
% 23.56/3.50      | ~ v1_funct_1(X3)
% 23.56/3.50      | v2_funct_1(X3)
% 23.56/3.50      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 23.56/3.50      | k1_xboole_0 = X2 ),
% 23.56/3.50      inference(cnf_transformation,[],[f84]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1152,plain,
% 23.56/3.50      ( k1_xboole_0 = X0
% 23.56/3.50      | v1_funct_2(X1,X2,X0) != iProver_top
% 23.56/3.50      | v1_funct_2(X3,X4,X2) != iProver_top
% 23.56/3.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 23.56/3.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 23.56/3.50      | v1_funct_1(X1) != iProver_top
% 23.56/3.50      | v1_funct_1(X3) != iProver_top
% 23.56/3.50      | v2_funct_1(X3) = iProver_top
% 23.56/3.50      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_11365,plain,
% 23.56/3.50      ( sK0 = k1_xboole_0
% 23.56/3.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 23.56/3.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 23.56/3.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.56/3.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 23.56/3.50      | v1_funct_1(sK2) != iProver_top
% 23.56/3.50      | v1_funct_1(sK3) != iProver_top
% 23.56/3.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 23.56/3.50      | v2_funct_1(sK2) = iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_11355,c_1152]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_12,plain,
% 23.56/3.50      ( v5_relat_1(X0,X1)
% 23.56/3.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 23.56/3.50      | ~ v1_relat_1(X0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f68]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_23,plain,
% 23.56/3.50      ( v2_funct_2(X0,k2_relat_1(X0))
% 23.56/3.50      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 23.56/3.50      | ~ v1_relat_1(X0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f103]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_30,negated_conjecture,
% 23.56/3.50      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 23.56/3.50      inference(cnf_transformation,[],[f93]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_402,plain,
% 23.56/3.50      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 23.56/3.50      | ~ v2_funct_1(sK2)
% 23.56/3.50      | ~ v1_relat_1(X0)
% 23.56/3.50      | k2_relat_1(X0) != sK0
% 23.56/3.50      | sK3 != X0 ),
% 23.56/3.50      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_403,plain,
% 23.56/3.50      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 23.56/3.50      | ~ v2_funct_1(sK2)
% 23.56/3.50      | ~ v1_relat_1(sK3)
% 23.56/3.50      | k2_relat_1(sK3) != sK0 ),
% 23.56/3.50      inference(unflattening,[status(thm)],[c_402]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_456,plain,
% 23.56/3.50      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 23.56/3.50      | ~ v2_funct_1(sK2)
% 23.56/3.50      | ~ v1_relat_1(X0)
% 23.56/3.50      | ~ v1_relat_1(sK3)
% 23.56/3.50      | k2_relat_1(sK3) != X1
% 23.56/3.50      | k2_relat_1(sK3) != sK0
% 23.56/3.50      | sK3 != X0 ),
% 23.56/3.50      inference(resolution_lifted,[status(thm)],[c_12,c_403]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_457,plain,
% 23.56/3.50      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 23.56/3.50      | ~ v2_funct_1(sK2)
% 23.56/3.50      | ~ v1_relat_1(sK3)
% 23.56/3.50      | k2_relat_1(sK3) != sK0 ),
% 23.56/3.50      inference(unflattening,[status(thm)],[c_456]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2,plain,
% 23.56/3.50      ( r1_tarski(X0,X0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f98]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_467,plain,
% 23.56/3.50      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 23.56/3.50      inference(forward_subsumption_resolution,[status(thm)],[c_457,c_2]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_468,plain,
% 23.56/3.50      ( k2_relat_1(sK3) != sK0
% 23.56/3.50      | v2_funct_1(sK2) != iProver_top
% 23.56/3.50      | v1_relat_1(sK3) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_11,plain,
% 23.56/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.56/3.50      | ~ v1_relat_1(X1)
% 23.56/3.50      | v1_relat_1(X0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f66]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1677,plain,
% 23.56/3.50      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3) ),
% 23.56/3.50      inference(resolution,[status(thm)],[c_11,c_32]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_14,plain,
% 23.56/3.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 23.56/3.50      inference(cnf_transformation,[],[f69]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1934,plain,
% 23.56/3.50      ( v1_relat_1(sK3) ),
% 23.56/3.50      inference(forward_subsumption_resolution,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_1677,c_14]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1935,plain,
% 23.56/3.50      ( v1_relat_1(sK3) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_1934]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1151,plain,
% 23.56/3.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_19,plain,
% 23.56/3.50      ( v5_relat_1(X0,X1)
% 23.56/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 23.56/3.50      inference(cnf_transformation,[],[f74]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_13,plain,
% 23.56/3.50      ( ~ v5_relat_1(X0,X1)
% 23.56/3.50      | r1_tarski(k2_relat_1(X0),X1)
% 23.56/3.50      | ~ v1_relat_1(X0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f67]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_423,plain,
% 23.56/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.56/3.50      | r1_tarski(k2_relat_1(X0),X2)
% 23.56/3.50      | ~ v1_relat_1(X0) ),
% 23.56/3.50      inference(resolution,[status(thm)],[c_19,c_13]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1143,plain,
% 23.56/3.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.56/3.50      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 23.56/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_423]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2330,plain,
% 23.56/3.50      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 23.56/3.50      | v1_relat_1(sK3) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_1151,c_1143]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3612,plain,
% 23.56/3.50      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_2330,c_1935]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1,plain,
% 23.56/3.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.56/3.50      inference(cnf_transformation,[],[f58]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1165,plain,
% 23.56/3.50      ( X0 = X1
% 23.56/3.50      | r1_tarski(X0,X1) != iProver_top
% 23.56/3.50      | r1_tarski(X1,X0) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3616,plain,
% 23.56/3.50      ( k2_relat_1(sK3) = sK0
% 23.56/3.50      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_3612,c_1165]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1148,plain,
% 23.56/3.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_27,plain,
% 23.56/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.56/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 23.56/3.50      | ~ v1_funct_1(X0)
% 23.56/3.50      | ~ v1_funct_1(X3)
% 23.56/3.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f82]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1154,plain,
% 23.56/3.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 23.56/3.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 23.56/3.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 23.56/3.50      | v1_funct_1(X5) != iProver_top
% 23.56/3.50      | v1_funct_1(X4) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3061,plain,
% 23.56/3.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 23.56/3.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 23.56/3.50      | v1_funct_1(X2) != iProver_top
% 23.56/3.50      | v1_funct_1(sK3) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_1151,c_1154]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_7214,plain,
% 23.56/3.50      ( v1_funct_1(X2) != iProver_top
% 23.56/3.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 23.56/3.50      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_3061,c_41]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_7215,plain,
% 23.56/3.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 23.56/3.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 23.56/3.50      | v1_funct_1(X2) != iProver_top ),
% 23.56/3.50      inference(renaming,[status(thm)],[c_7214]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_7223,plain,
% 23.56/3.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 23.56/3.50      | v1_funct_1(sK2) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_1148,c_7215]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1351,plain,
% 23.56/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.56/3.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 23.56/3.50      | ~ v1_funct_1(X0)
% 23.56/3.50      | ~ v1_funct_1(sK2)
% 23.56/3.50      | k1_partfun1(X3,X4,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_27]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1609,plain,
% 23.56/3.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.56/3.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 23.56/3.50      | ~ v1_funct_1(sK2)
% 23.56/3.50      | ~ v1_funct_1(sK3)
% 23.56/3.50      | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1351]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2239,plain,
% 23.56/3.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.56/3.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 23.56/3.50      | ~ v1_funct_1(sK2)
% 23.56/3.50      | ~ v1_funct_1(sK3)
% 23.56/3.50      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1609]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3527,plain,
% 23.56/3.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.56/3.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 23.56/3.50      | ~ v1_funct_1(sK2)
% 23.56/3.50      | ~ v1_funct_1(sK3)
% 23.56/3.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_2239]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_7664,plain,
% 23.56/3.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_7223,c_37,c_35,c_34,c_32,c_3527]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_7669,plain,
% 23.56/3.50      ( sK0 = k1_xboole_0
% 23.56/3.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 23.56/3.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 23.56/3.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.56/3.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 23.56/3.50      | v1_funct_1(sK2) != iProver_top
% 23.56/3.50      | v1_funct_1(sK3) != iProver_top
% 23.56/3.50      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 23.56/3.50      | v2_funct_1(sK2) = iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_7664,c_1152]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_36,negated_conjecture,
% 23.56/3.50      ( v1_funct_2(sK2,sK0,sK1) ),
% 23.56/3.50      inference(cnf_transformation,[],[f87]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_39,plain,
% 23.56/3.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_33,negated_conjecture,
% 23.56/3.50      ( v1_funct_2(sK3,sK1,sK0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f90]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_42,plain,
% 23.56/3.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1341,plain,
% 23.56/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.56/3.50      | m1_subset_1(k1_partfun1(X3,X4,X1,X2,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 23.56/3.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 23.56/3.50      | ~ v1_funct_1(X0)
% 23.56/3.50      | ~ v1_funct_1(sK2) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_25]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1629,plain,
% 23.56/3.50      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
% 23.56/3.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.56/3.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 23.56/3.50      | ~ v1_funct_1(sK2)
% 23.56/3.50      | ~ v1_funct_1(sK3) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1341]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2259,plain,
% 23.56/3.50      ( m1_subset_1(k1_partfun1(X0,X1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 23.56/3.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.56/3.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 23.56/3.50      | ~ v1_funct_1(sK2)
% 23.56/3.50      | ~ v1_funct_1(sK3) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1629]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3594,plain,
% 23.56/3.50      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.56/3.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.56/3.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 23.56/3.50      | ~ v1_funct_1(sK2)
% 23.56/3.50      | ~ v1_funct_1(sK3) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_2259]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_4354,plain,
% 23.56/3.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_393,c_37,c_35,c_34,c_32,c_3594]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_659,plain,
% 23.56/3.50      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 23.56/3.50      theory(equality) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_4568,plain,
% 23.56/3.50      ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 23.56/3.50      | v2_funct_1(k6_partfun1(sK0)) ),
% 23.56/3.50      inference(resolution,[status(thm)],[c_4354,c_659]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_4579,plain,
% 23.56/3.50      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) != iProver_top
% 23.56/3.50      | v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_4568]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_650,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_649,plain,( X0 = X0 ),theory(equality) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3233,plain,
% 23.56/3.50      ( X0 != X1 | X1 = X0 ),
% 23.56/3.50      inference(resolution,[status(thm)],[c_650,c_649]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_6363,plain,
% 23.56/3.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 23.56/3.50      inference(resolution,[status(thm)],[c_3233,c_4354]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_7253,plain,
% 23.56/3.50      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 23.56/3.50      | ~ v2_funct_1(k6_partfun1(sK0)) ),
% 23.56/3.50      inference(resolution,[status(thm)],[c_6363,c_659]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_18,plain,
% 23.56/3.50      ( v2_funct_1(k6_partfun1(X0)) ),
% 23.56/3.50      inference(cnf_transformation,[],[f96]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_7508,plain,
% 23.56/3.50      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) ),
% 23.56/3.50      inference(forward_subsumption_resolution,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_7253,c_18]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_7509,plain,
% 23.56/3.50      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_7508]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_41767,plain,
% 23.56/3.50      ( sK0 = k1_xboole_0 | v2_funct_1(sK2) = iProver_top ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_7669,c_38,c_39,c_40,c_41,c_42,c_43,c_4579,c_7509,
% 23.56/3.50                 c_11365]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_16,plain,
% 23.56/3.50      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 23.56/3.50      inference(cnf_transformation,[],[f94]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_11363,plain,
% 23.56/3.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_11355,c_7664]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_15,plain,
% 23.56/3.50      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 23.56/3.50      | ~ v1_relat_1(X0)
% 23.56/3.50      | ~ v1_relat_1(X1) ),
% 23.56/3.50      inference(cnf_transformation,[],[f70]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1159,plain,
% 23.56/3.50      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 23.56/3.50      | v1_relat_1(X0) != iProver_top
% 23.56/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_87412,plain,
% 23.56/3.50      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 23.56/3.50      | v1_relat_1(sK2) != iProver_top
% 23.56/3.50      | v1_relat_1(sK3) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_11363,c_1159]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1679,plain,
% 23.56/3.50      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) ),
% 23.56/3.50      inference(resolution,[status(thm)],[c_11,c_35]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1941,plain,
% 23.56/3.50      ( v1_relat_1(sK2) ),
% 23.56/3.50      inference(forward_subsumption_resolution,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_1679,c_14]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1942,plain,
% 23.56/3.50      ( v1_relat_1(sK2) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_1941]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_87486,plain,
% 23.56/3.50      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_87412,c_1935,c_1942]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_87490,plain,
% 23.56/3.50      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_16,c_87486]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_87660,plain,
% 23.56/3.50      ( sK0 = k1_xboole_0 ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_11365,c_468,c_1935,c_3616,c_41767,c_87490]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_87765,plain,
% 23.56/3.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_87660,c_1148]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_89325,plain,
% 23.56/3.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_8,c_87765]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2457,plain,
% 23.56/3.50      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_650]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_5252,plain,
% 23.56/3.50      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_2457]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_5253,plain,
% 23.56/3.50      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_5252]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_4018,plain,
% 23.56/3.50      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_659]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_4019,plain,
% 23.56/3.50      ( sK2 != X0
% 23.56/3.50      | v2_funct_1(X0) != iProver_top
% 23.56/3.50      | v2_funct_1(sK2) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_4018]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_4021,plain,
% 23.56/3.50      ( sK2 != k1_xboole_0
% 23.56/3.50      | v2_funct_1(sK2) = iProver_top
% 23.56/3.50      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_4019]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_10,plain,
% 23.56/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.56/3.50      | ~ v1_xboole_0(X1)
% 23.56/3.50      | v1_xboole_0(X0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f65]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2698,plain,
% 23.56/3.50      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(X1))
% 23.56/3.50      | ~ v1_xboole_0(X1)
% 23.56/3.50      | v1_xboole_0(k6_partfun1(X0)) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_10]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2700,plain,
% 23.56/3.50      ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
% 23.56/3.50      | v1_xboole_0(k6_partfun1(k1_xboole_0))
% 23.56/3.50      | ~ v1_xboole_0(k1_xboole_0) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_2698]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_7,plain,
% 23.56/3.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 23.56/3.50      inference(cnf_transformation,[],[f100]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1157,plain,
% 23.56/3.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2460,plain,
% 23.56/3.50      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_7,c_1157]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2463,plain,
% 23.56/3.50      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
% 23.56/3.50      inference(predicate_to_equality_rev,[status(thm)],[c_2460]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1816,plain,
% 23.56/3.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 23.56/3.50      | ~ v1_xboole_0(X0)
% 23.56/3.50      | v1_xboole_0(sK2) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_10]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1817,plain,
% 23.56/3.50      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 23.56/3.50      | v1_xboole_0(X0) != iProver_top
% 23.56/3.50      | v1_xboole_0(sK2) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_1816]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1819,plain,
% 23.56/3.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 23.56/3.50      | v1_xboole_0(sK2) = iProver_top
% 23.56/3.50      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1817]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_0,plain,
% 23.56/3.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 23.56/3.50      inference(cnf_transformation,[],[f55]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1555,plain,
% 23.56/3.50      ( ~ v1_xboole_0(k6_partfun1(X0)) | k1_xboole_0 = k6_partfun1(X0) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_0]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1559,plain,
% 23.56/3.50      ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
% 23.56/3.50      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1555]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1452,plain,
% 23.56/3.50      ( sK2 = sK2 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_649]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1400,plain,
% 23.56/3.50      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_0]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1403,plain,
% 23.56/3.50      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_1400]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1270,plain,
% 23.56/3.50      ( v2_funct_1(X0)
% 23.56/3.50      | ~ v2_funct_1(k6_partfun1(X1))
% 23.56/3.50      | X0 != k6_partfun1(X1) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_659]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1271,plain,
% 23.56/3.50      ( X0 != k6_partfun1(X1)
% 23.56/3.50      | v2_funct_1(X0) = iProver_top
% 23.56/3.50      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_1270]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1273,plain,
% 23.56/3.50      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 23.56/3.50      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 23.56/3.50      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1271]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_4,plain,
% 23.56/3.50      ( r1_tarski(k1_xboole_0,X0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f59]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_106,plain,
% 23.56/3.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_108,plain,
% 23.56/3.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_106]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_107,plain,
% 23.56/3.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_4]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_5,plain,
% 23.56/3.50      ( r1_xboole_0(X0,k1_xboole_0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f60]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_103,plain,
% 23.56/3.50      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_105,plain,
% 23.56/3.50      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_103]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_104,plain,
% 23.56/3.50      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_5]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_6,plain,
% 23.56/3.50      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f61]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_100,plain,
% 23.56/3.50      ( r1_xboole_0(X0,X1) != iProver_top
% 23.56/3.50      | r1_tarski(X0,X1) != iProver_top
% 23.56/3.50      | v1_xboole_0(X0) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_102,plain,
% 23.56/3.50      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.56/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 23.56/3.50      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_100]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_101,plain,
% 23.56/3.50      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 23.56/3.50      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 23.56/3.50      | v1_xboole_0(k1_xboole_0) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_6]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_79,plain,
% 23.56/3.50      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_81,plain,
% 23.56/3.50      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_79]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(contradiction,plain,
% 23.56/3.50      ( $false ),
% 23.56/3.50      inference(minisat,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_89325,c_87490,c_5253,c_4021,c_3616,c_2700,c_2463,
% 23.56/3.50                 c_1935,c_1819,c_1559,c_1452,c_1403,c_1273,c_468,c_108,
% 23.56/3.50                 c_107,c_105,c_104,c_102,c_101,c_81]) ).
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.56/3.50  
% 23.56/3.50  ------                               Statistics
% 23.56/3.50  
% 23.56/3.50  ------ Selected
% 23.56/3.50  
% 23.56/3.50  total_time:                             2.85
% 23.56/3.50  
%------------------------------------------------------------------------------
