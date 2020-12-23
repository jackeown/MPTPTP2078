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
% DateTime   : Thu Dec  3 12:02:07 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 714 expanded)
%              Number of clauses        :  107 ( 235 expanded)
%              Number of leaves         :   23 ( 161 expanded)
%              Depth                    :   23
%              Number of atoms          :  641 (3912 expanded)
%              Number of equality atoms :  215 ( 445 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f61])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f73,f78])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f18,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK4,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
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
          ( ( ~ v2_funct_2(X3,sK1)
            | ~ v2_funct_1(sK3) )
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ v2_funct_2(sK4,sK1)
      | ~ v2_funct_1(sK3) )
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f36,f50,f49])).

fof(f88,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f98,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f75])).

fof(f89,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f90,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_21,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1648,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2616,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1648])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1651,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2769,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2616,c_1651])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1656,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_260,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_261,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_335,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_261])).

cnf(c_455,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_335])).

cnf(c_456,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_1637,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_3086,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1656,c_1637])).

cnf(c_3196,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2769,c_3086])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1653,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3195,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_3086])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1654,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4630,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3195,c_1654])).

cnf(c_8190,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3196,c_4630])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1647,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X0 = X3
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X3
    | k6_partfun1(sK1) != X0
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_589,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_597,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_589,c_21])).

cnf(c_1631,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_5070,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1647,c_1631])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_40,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6015,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5070,c_37,c_39,c_40,c_42])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1644,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X3) != iProver_top
    | v1_funct_2(X4,X3,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6041,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6015,c_1644])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_38,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_41,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_22,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_29,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_472,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_473,plain,
    ( ~ v5_relat_1(sK4,k2_relat_1(sK4))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_494,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != X1
    | k2_relat_1(sK4) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_473])).

cnf(c_495,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_505,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_495,c_5])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_505])).

cnf(c_515,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_907,plain,
    ( ~ v2_funct_1(sK3)
    | sP1_iProver_split
    | k2_relat_1(sK4) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_515])).

cnf(c_944,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_907])).

cnf(c_1643,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_906,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_515])).

cnf(c_1636,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_2455,plain,
    ( sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_1636])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1649,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3441,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1643,c_1649])).

cnf(c_26,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_601,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_602,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_682,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_602])).

cnf(c_1630,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_2023,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1630])).

cnf(c_2301,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2023,c_37,c_38,c_39,c_40,c_41,c_42])).

cnf(c_3456,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3441,c_2301])).

cnf(c_6216,plain,
    ( v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6041,c_37,c_38,c_39,c_40,c_41,c_42,c_944,c_2455,c_3456])).

cnf(c_6217,plain,
    ( sK1 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6216])).

cnf(c_15,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1650,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6222,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6217,c_1650])).

cnf(c_1640,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2768,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1640,c_1651])).

cnf(c_4628,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK3
    | r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2768,c_1654])).

cnf(c_6226,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK2) = sK3
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,sK2),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6222,c_4628])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6266,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6226,c_8])).

cnf(c_7797,plain,
    ( sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6266,c_3195])).

cnf(c_918,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6099,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_6101,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6099])).

cnf(c_2466,plain,
    ( ~ sP1_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2455])).

cnf(c_910,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2106,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_910])).

cnf(c_2107,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2106])).

cnf(c_1918,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_1920,plain,
    ( ~ v2_funct_1(k6_partfun1(k1_xboole_0))
    | v2_funct_1(k1_xboole_0)
    | k1_xboole_0 != k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1918])).

cnf(c_103,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_102,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_85,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8190,c_7797,c_6101,c_3456,c_2466,c_2107,c_1920,c_907,c_103,c_102,c_85])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:59:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.46/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/0.98  
% 3.46/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.46/0.98  
% 3.46/0.98  ------  iProver source info
% 3.46/0.98  
% 3.46/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.46/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.46/0.98  git: non_committed_changes: false
% 3.46/0.98  git: last_make_outside_of_git: false
% 3.46/0.98  
% 3.46/0.98  ------ 
% 3.46/0.98  
% 3.46/0.98  ------ Input Options
% 3.46/0.98  
% 3.46/0.98  --out_options                           all
% 3.46/0.98  --tptp_safe_out                         true
% 3.46/0.98  --problem_path                          ""
% 3.46/0.98  --include_path                          ""
% 3.46/0.98  --clausifier                            res/vclausify_rel
% 3.46/0.98  --clausifier_options                    --mode clausify
% 3.46/0.98  --stdin                                 false
% 3.46/0.98  --stats_out                             all
% 3.46/0.98  
% 3.46/0.98  ------ General Options
% 3.46/0.98  
% 3.46/0.98  --fof                                   false
% 3.46/0.98  --time_out_real                         305.
% 3.46/0.98  --time_out_virtual                      -1.
% 3.46/0.98  --symbol_type_check                     false
% 3.46/0.98  --clausify_out                          false
% 3.46/0.98  --sig_cnt_out                           false
% 3.46/0.98  --trig_cnt_out                          false
% 3.46/0.98  --trig_cnt_out_tolerance                1.
% 3.46/0.98  --trig_cnt_out_sk_spl                   false
% 3.46/0.98  --abstr_cl_out                          false
% 3.46/0.98  
% 3.46/0.98  ------ Global Options
% 3.46/0.98  
% 3.46/0.98  --schedule                              default
% 3.46/0.98  --add_important_lit                     false
% 3.46/0.98  --prop_solver_per_cl                    1000
% 3.46/0.98  --min_unsat_core                        false
% 3.46/0.98  --soft_assumptions                      false
% 3.46/0.98  --soft_lemma_size                       3
% 3.46/0.98  --prop_impl_unit_size                   0
% 3.46/0.98  --prop_impl_unit                        []
% 3.46/0.98  --share_sel_clauses                     true
% 3.46/0.98  --reset_solvers                         false
% 3.46/0.98  --bc_imp_inh                            [conj_cone]
% 3.46/0.98  --conj_cone_tolerance                   3.
% 3.46/0.98  --extra_neg_conj                        none
% 3.46/0.98  --large_theory_mode                     true
% 3.46/0.98  --prolific_symb_bound                   200
% 3.46/0.98  --lt_threshold                          2000
% 3.46/0.98  --clause_weak_htbl                      true
% 3.46/0.98  --gc_record_bc_elim                     false
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing Options
% 3.46/0.98  
% 3.46/0.98  --preprocessing_flag                    true
% 3.46/0.98  --time_out_prep_mult                    0.1
% 3.46/0.98  --splitting_mode                        input
% 3.46/0.98  --splitting_grd                         true
% 3.46/0.98  --splitting_cvd                         false
% 3.46/0.98  --splitting_cvd_svl                     false
% 3.46/0.98  --splitting_nvd                         32
% 3.46/0.98  --sub_typing                            true
% 3.46/0.98  --prep_gs_sim                           true
% 3.46/0.98  --prep_unflatten                        true
% 3.46/0.98  --prep_res_sim                          true
% 3.46/0.98  --prep_upred                            true
% 3.46/0.98  --prep_sem_filter                       exhaustive
% 3.46/0.98  --prep_sem_filter_out                   false
% 3.46/0.98  --pred_elim                             true
% 3.46/0.98  --res_sim_input                         true
% 3.46/0.98  --eq_ax_congr_red                       true
% 3.46/0.98  --pure_diseq_elim                       true
% 3.46/0.98  --brand_transform                       false
% 3.46/0.98  --non_eq_to_eq                          false
% 3.46/0.98  --prep_def_merge                        true
% 3.46/0.98  --prep_def_merge_prop_impl              false
% 3.46/0.98  --prep_def_merge_mbd                    true
% 3.46/0.98  --prep_def_merge_tr_red                 false
% 3.46/0.98  --prep_def_merge_tr_cl                  false
% 3.46/0.98  --smt_preprocessing                     true
% 3.46/0.98  --smt_ac_axioms                         fast
% 3.46/0.98  --preprocessed_out                      false
% 3.46/0.98  --preprocessed_stats                    false
% 3.46/0.98  
% 3.46/0.98  ------ Abstraction refinement Options
% 3.46/0.98  
% 3.46/0.98  --abstr_ref                             []
% 3.46/0.98  --abstr_ref_prep                        false
% 3.46/0.98  --abstr_ref_until_sat                   false
% 3.46/0.98  --abstr_ref_sig_restrict                funpre
% 3.46/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.46/0.98  --abstr_ref_under                       []
% 3.46/0.98  
% 3.46/0.98  ------ SAT Options
% 3.46/0.98  
% 3.46/0.98  --sat_mode                              false
% 3.46/0.98  --sat_fm_restart_options                ""
% 3.46/0.98  --sat_gr_def                            false
% 3.46/0.98  --sat_epr_types                         true
% 3.46/0.98  --sat_non_cyclic_types                  false
% 3.46/0.98  --sat_finite_models                     false
% 3.46/0.98  --sat_fm_lemmas                         false
% 3.46/0.98  --sat_fm_prep                           false
% 3.46/0.98  --sat_fm_uc_incr                        true
% 3.46/0.98  --sat_out_model                         small
% 3.46/0.98  --sat_out_clauses                       false
% 3.46/0.98  
% 3.46/0.98  ------ QBF Options
% 3.46/0.98  
% 3.46/0.98  --qbf_mode                              false
% 3.46/0.98  --qbf_elim_univ                         false
% 3.46/0.98  --qbf_dom_inst                          none
% 3.46/0.98  --qbf_dom_pre_inst                      false
% 3.46/0.98  --qbf_sk_in                             false
% 3.46/0.98  --qbf_pred_elim                         true
% 3.46/0.98  --qbf_split                             512
% 3.46/0.98  
% 3.46/0.98  ------ BMC1 Options
% 3.46/0.98  
% 3.46/0.98  --bmc1_incremental                      false
% 3.46/0.98  --bmc1_axioms                           reachable_all
% 3.46/0.98  --bmc1_min_bound                        0
% 3.46/0.98  --bmc1_max_bound                        -1
% 3.46/0.98  --bmc1_max_bound_default                -1
% 3.46/0.98  --bmc1_symbol_reachability              true
% 3.46/0.98  --bmc1_property_lemmas                  false
% 3.46/0.98  --bmc1_k_induction                      false
% 3.46/0.98  --bmc1_non_equiv_states                 false
% 3.46/0.98  --bmc1_deadlock                         false
% 3.46/0.98  --bmc1_ucm                              false
% 3.46/0.98  --bmc1_add_unsat_core                   none
% 3.46/0.98  --bmc1_unsat_core_children              false
% 3.46/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.46/0.98  --bmc1_out_stat                         full
% 3.46/0.98  --bmc1_ground_init                      false
% 3.46/0.98  --bmc1_pre_inst_next_state              false
% 3.46/0.98  --bmc1_pre_inst_state                   false
% 3.46/0.98  --bmc1_pre_inst_reach_state             false
% 3.46/0.98  --bmc1_out_unsat_core                   false
% 3.46/0.98  --bmc1_aig_witness_out                  false
% 3.46/0.98  --bmc1_verbose                          false
% 3.46/0.98  --bmc1_dump_clauses_tptp                false
% 3.46/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.46/0.98  --bmc1_dump_file                        -
% 3.46/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.46/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.46/0.98  --bmc1_ucm_extend_mode                  1
% 3.46/0.98  --bmc1_ucm_init_mode                    2
% 3.46/0.98  --bmc1_ucm_cone_mode                    none
% 3.46/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.46/0.98  --bmc1_ucm_relax_model                  4
% 3.46/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.46/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.46/0.98  --bmc1_ucm_layered_model                none
% 3.46/0.98  --bmc1_ucm_max_lemma_size               10
% 3.46/0.98  
% 3.46/0.98  ------ AIG Options
% 3.46/0.98  
% 3.46/0.98  --aig_mode                              false
% 3.46/0.98  
% 3.46/0.98  ------ Instantiation Options
% 3.46/0.98  
% 3.46/0.98  --instantiation_flag                    true
% 3.46/0.98  --inst_sos_flag                         false
% 3.46/0.98  --inst_sos_phase                        true
% 3.46/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.46/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.46/0.98  --inst_lit_sel_side                     num_symb
% 3.46/0.98  --inst_solver_per_active                1400
% 3.46/0.98  --inst_solver_calls_frac                1.
% 3.46/0.98  --inst_passive_queue_type               priority_queues
% 3.46/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.46/0.98  --inst_passive_queues_freq              [25;2]
% 3.46/0.98  --inst_dismatching                      true
% 3.46/0.98  --inst_eager_unprocessed_to_passive     true
% 3.46/0.98  --inst_prop_sim_given                   true
% 3.46/0.98  --inst_prop_sim_new                     false
% 3.46/0.98  --inst_subs_new                         false
% 3.46/0.98  --inst_eq_res_simp                      false
% 3.46/0.98  --inst_subs_given                       false
% 3.46/0.98  --inst_orphan_elimination               true
% 3.46/0.98  --inst_learning_loop_flag               true
% 3.46/0.98  --inst_learning_start                   3000
% 3.46/0.98  --inst_learning_factor                  2
% 3.46/0.98  --inst_start_prop_sim_after_learn       3
% 3.46/0.98  --inst_sel_renew                        solver
% 3.46/0.98  --inst_lit_activity_flag                true
% 3.46/0.98  --inst_restr_to_given                   false
% 3.46/0.98  --inst_activity_threshold               500
% 3.46/0.98  --inst_out_proof                        true
% 3.46/0.98  
% 3.46/0.98  ------ Resolution Options
% 3.46/0.98  
% 3.46/0.98  --resolution_flag                       true
% 3.46/0.98  --res_lit_sel                           adaptive
% 3.46/0.98  --res_lit_sel_side                      none
% 3.46/0.98  --res_ordering                          kbo
% 3.46/0.98  --res_to_prop_solver                    active
% 3.46/0.98  --res_prop_simpl_new                    false
% 3.46/0.98  --res_prop_simpl_given                  true
% 3.46/0.98  --res_passive_queue_type                priority_queues
% 3.46/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.46/0.98  --res_passive_queues_freq               [15;5]
% 3.46/0.98  --res_forward_subs                      full
% 3.46/0.98  --res_backward_subs                     full
% 3.46/0.98  --res_forward_subs_resolution           true
% 3.46/0.98  --res_backward_subs_resolution          true
% 3.46/0.98  --res_orphan_elimination                true
% 3.46/0.98  --res_time_limit                        2.
% 3.46/0.98  --res_out_proof                         true
% 3.46/0.98  
% 3.46/0.98  ------ Superposition Options
% 3.46/0.98  
% 3.46/0.98  --superposition_flag                    true
% 3.46/0.98  --sup_passive_queue_type                priority_queues
% 3.46/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.46/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.46/0.98  --demod_completeness_check              fast
% 3.46/0.98  --demod_use_ground                      true
% 3.46/0.98  --sup_to_prop_solver                    passive
% 3.46/0.98  --sup_prop_simpl_new                    true
% 3.46/0.98  --sup_prop_simpl_given                  true
% 3.46/0.98  --sup_fun_splitting                     false
% 3.46/0.98  --sup_smt_interval                      50000
% 3.46/0.98  
% 3.46/0.98  ------ Superposition Simplification Setup
% 3.46/0.98  
% 3.46/0.98  --sup_indices_passive                   []
% 3.46/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.46/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.98  --sup_full_bw                           [BwDemod]
% 3.46/0.98  --sup_immed_triv                        [TrivRules]
% 3.46/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.98  --sup_immed_bw_main                     []
% 3.46/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.46/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.98  
% 3.46/0.98  ------ Combination Options
% 3.46/0.98  
% 3.46/0.98  --comb_res_mult                         3
% 3.46/0.98  --comb_sup_mult                         2
% 3.46/0.98  --comb_inst_mult                        10
% 3.46/0.98  
% 3.46/0.98  ------ Debug Options
% 3.46/0.98  
% 3.46/0.98  --dbg_backtrace                         false
% 3.46/0.98  --dbg_dump_prop_clauses                 false
% 3.46/0.98  --dbg_dump_prop_clauses_file            -
% 3.46/0.98  --dbg_out_stat                          false
% 3.46/0.98  ------ Parsing...
% 3.46/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/0.98  ------ Proving...
% 3.46/0.98  ------ Problem Properties 
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  clauses                                 31
% 3.46/0.98  conjectures                             6
% 3.46/0.98  EPR                                     8
% 3.46/0.98  Horn                                    28
% 3.46/0.98  unary                                   11
% 3.46/0.98  binary                                  9
% 3.46/0.98  lits                                    87
% 3.46/0.98  lits eq                                 16
% 3.46/0.98  fd_pure                                 0
% 3.46/0.98  fd_pseudo                               0
% 3.46/0.98  fd_cond                                 2
% 3.46/0.98  fd_pseudo_cond                          1
% 3.46/0.98  AC symbols                              0
% 3.46/0.98  
% 3.46/0.98  ------ Schedule dynamic 5 is on 
% 3.46/0.98  
% 3.46/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  ------ 
% 3.46/0.98  Current options:
% 3.46/0.98  ------ 
% 3.46/0.98  
% 3.46/0.98  ------ Input Options
% 3.46/0.98  
% 3.46/0.98  --out_options                           all
% 3.46/0.98  --tptp_safe_out                         true
% 3.46/0.98  --problem_path                          ""
% 3.46/0.98  --include_path                          ""
% 3.46/0.98  --clausifier                            res/vclausify_rel
% 3.46/0.98  --clausifier_options                    --mode clausify
% 3.46/0.98  --stdin                                 false
% 3.46/0.98  --stats_out                             all
% 3.46/0.98  
% 3.46/0.98  ------ General Options
% 3.46/0.98  
% 3.46/0.98  --fof                                   false
% 3.46/0.98  --time_out_real                         305.
% 3.46/0.98  --time_out_virtual                      -1.
% 3.46/0.98  --symbol_type_check                     false
% 3.46/0.98  --clausify_out                          false
% 3.46/0.98  --sig_cnt_out                           false
% 3.46/0.98  --trig_cnt_out                          false
% 3.46/0.98  --trig_cnt_out_tolerance                1.
% 3.46/0.98  --trig_cnt_out_sk_spl                   false
% 3.46/0.98  --abstr_cl_out                          false
% 3.46/0.98  
% 3.46/0.98  ------ Global Options
% 3.46/0.98  
% 3.46/0.98  --schedule                              default
% 3.46/0.98  --add_important_lit                     false
% 3.46/0.98  --prop_solver_per_cl                    1000
% 3.46/0.98  --min_unsat_core                        false
% 3.46/0.98  --soft_assumptions                      false
% 3.46/0.98  --soft_lemma_size                       3
% 3.46/0.98  --prop_impl_unit_size                   0
% 3.46/0.98  --prop_impl_unit                        []
% 3.46/0.98  --share_sel_clauses                     true
% 3.46/0.98  --reset_solvers                         false
% 3.46/0.98  --bc_imp_inh                            [conj_cone]
% 3.46/0.98  --conj_cone_tolerance                   3.
% 3.46/0.98  --extra_neg_conj                        none
% 3.46/0.98  --large_theory_mode                     true
% 3.46/0.98  --prolific_symb_bound                   200
% 3.46/0.98  --lt_threshold                          2000
% 3.46/0.98  --clause_weak_htbl                      true
% 3.46/0.98  --gc_record_bc_elim                     false
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing Options
% 3.46/0.98  
% 3.46/0.98  --preprocessing_flag                    true
% 3.46/0.98  --time_out_prep_mult                    0.1
% 3.46/0.98  --splitting_mode                        input
% 3.46/0.98  --splitting_grd                         true
% 3.46/0.98  --splitting_cvd                         false
% 3.46/0.98  --splitting_cvd_svl                     false
% 3.46/0.98  --splitting_nvd                         32
% 3.46/0.98  --sub_typing                            true
% 3.46/0.98  --prep_gs_sim                           true
% 3.46/0.98  --prep_unflatten                        true
% 3.46/0.98  --prep_res_sim                          true
% 3.46/0.98  --prep_upred                            true
% 3.46/0.98  --prep_sem_filter                       exhaustive
% 3.46/0.98  --prep_sem_filter_out                   false
% 3.46/0.98  --pred_elim                             true
% 3.46/0.98  --res_sim_input                         true
% 3.46/0.99  --eq_ax_congr_red                       true
% 3.46/0.99  --pure_diseq_elim                       true
% 3.46/0.99  --brand_transform                       false
% 3.46/0.99  --non_eq_to_eq                          false
% 3.46/0.99  --prep_def_merge                        true
% 3.46/0.99  --prep_def_merge_prop_impl              false
% 3.46/0.99  --prep_def_merge_mbd                    true
% 3.46/0.99  --prep_def_merge_tr_red                 false
% 3.46/0.99  --prep_def_merge_tr_cl                  false
% 3.46/0.99  --smt_preprocessing                     true
% 3.46/0.99  --smt_ac_axioms                         fast
% 3.46/0.99  --preprocessed_out                      false
% 3.46/0.99  --preprocessed_stats                    false
% 3.46/0.99  
% 3.46/0.99  ------ Abstraction refinement Options
% 3.46/0.99  
% 3.46/0.99  --abstr_ref                             []
% 3.46/0.99  --abstr_ref_prep                        false
% 3.46/0.99  --abstr_ref_until_sat                   false
% 3.46/0.99  --abstr_ref_sig_restrict                funpre
% 3.46/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.46/0.99  --abstr_ref_under                       []
% 3.46/0.99  
% 3.46/0.99  ------ SAT Options
% 3.46/0.99  
% 3.46/0.99  --sat_mode                              false
% 3.46/0.99  --sat_fm_restart_options                ""
% 3.46/0.99  --sat_gr_def                            false
% 3.46/0.99  --sat_epr_types                         true
% 3.46/0.99  --sat_non_cyclic_types                  false
% 3.46/0.99  --sat_finite_models                     false
% 3.46/0.99  --sat_fm_lemmas                         false
% 3.46/0.99  --sat_fm_prep                           false
% 3.46/0.99  --sat_fm_uc_incr                        true
% 3.46/0.99  --sat_out_model                         small
% 3.46/0.99  --sat_out_clauses                       false
% 3.46/0.99  
% 3.46/0.99  ------ QBF Options
% 3.46/0.99  
% 3.46/0.99  --qbf_mode                              false
% 3.46/0.99  --qbf_elim_univ                         false
% 3.46/0.99  --qbf_dom_inst                          none
% 3.46/0.99  --qbf_dom_pre_inst                      false
% 3.46/0.99  --qbf_sk_in                             false
% 3.46/0.99  --qbf_pred_elim                         true
% 3.46/0.99  --qbf_split                             512
% 3.46/0.99  
% 3.46/0.99  ------ BMC1 Options
% 3.46/0.99  
% 3.46/0.99  --bmc1_incremental                      false
% 3.46/0.99  --bmc1_axioms                           reachable_all
% 3.46/0.99  --bmc1_min_bound                        0
% 3.46/0.99  --bmc1_max_bound                        -1
% 3.46/0.99  --bmc1_max_bound_default                -1
% 3.46/0.99  --bmc1_symbol_reachability              true
% 3.46/0.99  --bmc1_property_lemmas                  false
% 3.46/0.99  --bmc1_k_induction                      false
% 3.46/0.99  --bmc1_non_equiv_states                 false
% 3.46/0.99  --bmc1_deadlock                         false
% 3.46/0.99  --bmc1_ucm                              false
% 3.46/0.99  --bmc1_add_unsat_core                   none
% 3.46/0.99  --bmc1_unsat_core_children              false
% 3.46/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.46/0.99  --bmc1_out_stat                         full
% 3.46/0.99  --bmc1_ground_init                      false
% 3.46/0.99  --bmc1_pre_inst_next_state              false
% 3.46/0.99  --bmc1_pre_inst_state                   false
% 3.46/0.99  --bmc1_pre_inst_reach_state             false
% 3.46/0.99  --bmc1_out_unsat_core                   false
% 3.46/0.99  --bmc1_aig_witness_out                  false
% 3.46/0.99  --bmc1_verbose                          false
% 3.46/0.99  --bmc1_dump_clauses_tptp                false
% 3.46/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.46/0.99  --bmc1_dump_file                        -
% 3.46/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.46/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.46/0.99  --bmc1_ucm_extend_mode                  1
% 3.46/0.99  --bmc1_ucm_init_mode                    2
% 3.46/0.99  --bmc1_ucm_cone_mode                    none
% 3.46/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.46/0.99  --bmc1_ucm_relax_model                  4
% 3.46/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.46/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.46/0.99  --bmc1_ucm_layered_model                none
% 3.46/0.99  --bmc1_ucm_max_lemma_size               10
% 3.46/0.99  
% 3.46/0.99  ------ AIG Options
% 3.46/0.99  
% 3.46/0.99  --aig_mode                              false
% 3.46/0.99  
% 3.46/0.99  ------ Instantiation Options
% 3.46/0.99  
% 3.46/0.99  --instantiation_flag                    true
% 3.46/0.99  --inst_sos_flag                         false
% 3.46/0.99  --inst_sos_phase                        true
% 3.46/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.46/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.46/0.99  --inst_lit_sel_side                     none
% 3.46/0.99  --inst_solver_per_active                1400
% 3.46/0.99  --inst_solver_calls_frac                1.
% 3.46/0.99  --inst_passive_queue_type               priority_queues
% 3.46/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.46/0.99  --inst_passive_queues_freq              [25;2]
% 3.46/0.99  --inst_dismatching                      true
% 3.46/0.99  --inst_eager_unprocessed_to_passive     true
% 3.46/0.99  --inst_prop_sim_given                   true
% 3.46/0.99  --inst_prop_sim_new                     false
% 3.46/0.99  --inst_subs_new                         false
% 3.46/0.99  --inst_eq_res_simp                      false
% 3.46/0.99  --inst_subs_given                       false
% 3.46/0.99  --inst_orphan_elimination               true
% 3.46/0.99  --inst_learning_loop_flag               true
% 3.46/0.99  --inst_learning_start                   3000
% 3.46/0.99  --inst_learning_factor                  2
% 3.46/0.99  --inst_start_prop_sim_after_learn       3
% 3.46/0.99  --inst_sel_renew                        solver
% 3.46/0.99  --inst_lit_activity_flag                true
% 3.46/0.99  --inst_restr_to_given                   false
% 3.46/0.99  --inst_activity_threshold               500
% 3.46/0.99  --inst_out_proof                        true
% 3.46/0.99  
% 3.46/0.99  ------ Resolution Options
% 3.46/0.99  
% 3.46/0.99  --resolution_flag                       false
% 3.46/0.99  --res_lit_sel                           adaptive
% 3.46/0.99  --res_lit_sel_side                      none
% 3.46/0.99  --res_ordering                          kbo
% 3.46/0.99  --res_to_prop_solver                    active
% 3.46/0.99  --res_prop_simpl_new                    false
% 3.46/0.99  --res_prop_simpl_given                  true
% 3.46/0.99  --res_passive_queue_type                priority_queues
% 3.46/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.46/0.99  --res_passive_queues_freq               [15;5]
% 3.46/0.99  --res_forward_subs                      full
% 3.46/0.99  --res_backward_subs                     full
% 3.46/0.99  --res_forward_subs_resolution           true
% 3.46/0.99  --res_backward_subs_resolution          true
% 3.46/0.99  --res_orphan_elimination                true
% 3.46/0.99  --res_time_limit                        2.
% 3.46/0.99  --res_out_proof                         true
% 3.46/0.99  
% 3.46/0.99  ------ Superposition Options
% 3.46/0.99  
% 3.46/0.99  --superposition_flag                    true
% 3.46/0.99  --sup_passive_queue_type                priority_queues
% 3.46/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.46/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.46/0.99  --demod_completeness_check              fast
% 3.46/0.99  --demod_use_ground                      true
% 3.46/0.99  --sup_to_prop_solver                    passive
% 3.46/0.99  --sup_prop_simpl_new                    true
% 3.46/0.99  --sup_prop_simpl_given                  true
% 3.46/0.99  --sup_fun_splitting                     false
% 3.46/0.99  --sup_smt_interval                      50000
% 3.46/0.99  
% 3.46/0.99  ------ Superposition Simplification Setup
% 3.46/0.99  
% 3.46/0.99  --sup_indices_passive                   []
% 3.46/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.46/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.99  --sup_full_bw                           [BwDemod]
% 3.46/0.99  --sup_immed_triv                        [TrivRules]
% 3.46/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.99  --sup_immed_bw_main                     []
% 3.46/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.46/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.99  
% 3.46/0.99  ------ Combination Options
% 3.46/0.99  
% 3.46/0.99  --comb_res_mult                         3
% 3.46/0.99  --comb_sup_mult                         2
% 3.46/0.99  --comb_inst_mult                        10
% 3.46/0.99  
% 3.46/0.99  ------ Debug Options
% 3.46/0.99  
% 3.46/0.99  --dbg_backtrace                         false
% 3.46/0.99  --dbg_dump_prop_clauses                 false
% 3.46/0.99  --dbg_dump_prop_clauses_file            -
% 3.46/0.99  --dbg_out_stat                          false
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  % SZS status Theorem for theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  fof(f4,axiom,(
% 3.46/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f43,plain,(
% 3.46/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.46/0.99    inference(nnf_transformation,[],[f4])).
% 3.46/0.99  
% 3.46/0.99  fof(f44,plain,(
% 3.46/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.46/0.99    inference(flattening,[],[f43])).
% 3.46/0.99  
% 3.46/0.99  fof(f61,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.46/0.99    inference(cnf_transformation,[],[f44])).
% 3.46/0.99  
% 3.46/0.99  fof(f95,plain,(
% 3.46/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.46/0.99    inference(equality_resolution,[],[f61])).
% 3.46/0.99  
% 3.46/0.99  fof(f12,axiom,(
% 3.46/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f73,plain,(
% 3.46/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f12])).
% 3.46/0.99  
% 3.46/0.99  fof(f15,axiom,(
% 3.46/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f78,plain,(
% 3.46/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f15])).
% 3.46/0.99  
% 3.46/0.99  fof(f92,plain,(
% 3.46/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.46/0.99    inference(definition_unfolding,[],[f73,f78])).
% 3.46/0.99  
% 3.46/0.99  fof(f5,axiom,(
% 3.46/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f45,plain,(
% 3.46/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.46/0.99    inference(nnf_transformation,[],[f5])).
% 3.46/0.99  
% 3.46/0.99  fof(f62,plain,(
% 3.46/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f45])).
% 3.46/0.99  
% 3.46/0.99  fof(f1,axiom,(
% 3.46/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f20,plain,(
% 3.46/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.46/0.99    inference(ennf_transformation,[],[f1])).
% 3.46/0.99  
% 3.46/0.99  fof(f37,plain,(
% 3.46/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.46/0.99    inference(nnf_transformation,[],[f20])).
% 3.46/0.99  
% 3.46/0.99  fof(f38,plain,(
% 3.46/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.46/0.99    inference(rectify,[],[f37])).
% 3.46/0.99  
% 3.46/0.99  fof(f39,plain,(
% 3.46/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.46/0.99    introduced(choice_axiom,[])).
% 3.46/0.99  
% 3.46/0.99  fof(f40,plain,(
% 3.46/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.46/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 3.46/0.99  
% 3.46/0.99  fof(f53,plain,(
% 3.46/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f40])).
% 3.46/0.99  
% 3.46/0.99  fof(f2,axiom,(
% 3.46/0.99    v1_xboole_0(k1_xboole_0)),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f55,plain,(
% 3.46/0.99    v1_xboole_0(k1_xboole_0)),
% 3.46/0.99    inference(cnf_transformation,[],[f2])).
% 3.46/0.99  
% 3.46/0.99  fof(f6,axiom,(
% 3.46/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f21,plain,(
% 3.46/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.46/0.99    inference(ennf_transformation,[],[f6])).
% 3.46/0.99  
% 3.46/0.99  fof(f64,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f21])).
% 3.46/0.99  
% 3.46/0.99  fof(f63,plain,(
% 3.46/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f45])).
% 3.46/0.99  
% 3.46/0.99  fof(f3,axiom,(
% 3.46/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f41,plain,(
% 3.46/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.46/0.99    inference(nnf_transformation,[],[f3])).
% 3.46/0.99  
% 3.46/0.99  fof(f42,plain,(
% 3.46/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.46/0.99    inference(flattening,[],[f41])).
% 3.46/0.99  
% 3.46/0.99  fof(f56,plain,(
% 3.46/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.46/0.99    inference(cnf_transformation,[],[f42])).
% 3.46/0.99  
% 3.46/0.99  fof(f94,plain,(
% 3.46/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.46/0.99    inference(equality_resolution,[],[f56])).
% 3.46/0.99  
% 3.46/0.99  fof(f58,plain,(
% 3.46/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f42])).
% 3.46/0.99  
% 3.46/0.99  fof(f14,axiom,(
% 3.46/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f29,plain,(
% 3.46/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.46/0.99    inference(ennf_transformation,[],[f14])).
% 3.46/0.99  
% 3.46/0.99  fof(f30,plain,(
% 3.46/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.46/0.99    inference(flattening,[],[f29])).
% 3.46/0.99  
% 3.46/0.99  fof(f77,plain,(
% 3.46/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f30])).
% 3.46/0.99  
% 3.46/0.99  fof(f11,axiom,(
% 3.46/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f25,plain,(
% 3.46/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.46/0.99    inference(ennf_transformation,[],[f11])).
% 3.46/0.99  
% 3.46/0.99  fof(f26,plain,(
% 3.46/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/0.99    inference(flattening,[],[f25])).
% 3.46/0.99  
% 3.46/0.99  fof(f47,plain,(
% 3.46/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/0.99    inference(nnf_transformation,[],[f26])).
% 3.46/0.99  
% 3.46/0.99  fof(f71,plain,(
% 3.46/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f47])).
% 3.46/0.99  
% 3.46/0.99  fof(f18,conjecture,(
% 3.46/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f19,negated_conjecture,(
% 3.46/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.46/0.99    inference(negated_conjecture,[],[f18])).
% 3.46/0.99  
% 3.46/0.99  fof(f35,plain,(
% 3.46/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.46/0.99    inference(ennf_transformation,[],[f19])).
% 3.46/0.99  
% 3.46/0.99  fof(f36,plain,(
% 3.46/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.46/0.99    inference(flattening,[],[f35])).
% 3.46/0.99  
% 3.46/0.99  fof(f50,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 3.46/0.99    introduced(choice_axiom,[])).
% 3.46/0.99  
% 3.46/0.99  fof(f49,plain,(
% 3.46/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.46/0.99    introduced(choice_axiom,[])).
% 3.46/0.99  
% 3.46/0.99  fof(f51,plain,(
% 3.46/0.99    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.46/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f36,f50,f49])).
% 3.46/0.99  
% 3.46/0.99  fof(f88,plain,(
% 3.46/0.99    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 3.46/0.99    inference(cnf_transformation,[],[f51])).
% 3.46/0.99  
% 3.46/0.99  fof(f82,plain,(
% 3.46/0.99    v1_funct_1(sK3)),
% 3.46/0.99    inference(cnf_transformation,[],[f51])).
% 3.46/0.99  
% 3.46/0.99  fof(f84,plain,(
% 3.46/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.46/0.99    inference(cnf_transformation,[],[f51])).
% 3.46/0.99  
% 3.46/0.99  fof(f85,plain,(
% 3.46/0.99    v1_funct_1(sK4)),
% 3.46/0.99    inference(cnf_transformation,[],[f51])).
% 3.46/0.99  
% 3.46/0.99  fof(f87,plain,(
% 3.46/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.46/0.99    inference(cnf_transformation,[],[f51])).
% 3.46/0.99  
% 3.46/0.99  fof(f17,axiom,(
% 3.46/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f33,plain,(
% 3.46/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.46/0.99    inference(ennf_transformation,[],[f17])).
% 3.46/0.99  
% 3.46/0.99  fof(f34,plain,(
% 3.46/0.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.46/0.99    inference(flattening,[],[f33])).
% 3.46/0.99  
% 3.46/0.99  fof(f80,plain,(
% 3.46/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f34])).
% 3.46/0.99  
% 3.46/0.99  fof(f83,plain,(
% 3.46/0.99    v1_funct_2(sK3,sK1,sK2)),
% 3.46/0.99    inference(cnf_transformation,[],[f51])).
% 3.46/0.99  
% 3.46/0.99  fof(f86,plain,(
% 3.46/0.99    v1_funct_2(sK4,sK2,sK1)),
% 3.46/0.99    inference(cnf_transformation,[],[f51])).
% 3.46/0.99  
% 3.46/0.99  fof(f9,axiom,(
% 3.46/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f23,plain,(
% 3.46/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/0.99    inference(ennf_transformation,[],[f9])).
% 3.46/0.99  
% 3.46/0.99  fof(f69,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f23])).
% 3.46/0.99  
% 3.46/0.99  fof(f7,axiom,(
% 3.46/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f22,plain,(
% 3.46/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.46/0.99    inference(ennf_transformation,[],[f7])).
% 3.46/0.99  
% 3.46/0.99  fof(f46,plain,(
% 3.46/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.46/0.99    inference(nnf_transformation,[],[f22])).
% 3.46/0.99  
% 3.46/0.99  fof(f66,plain,(
% 3.46/0.99    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f46])).
% 3.46/0.99  
% 3.46/0.99  fof(f13,axiom,(
% 3.46/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f27,plain,(
% 3.46/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.46/0.99    inference(ennf_transformation,[],[f13])).
% 3.46/0.99  
% 3.46/0.99  fof(f28,plain,(
% 3.46/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.46/0.99    inference(flattening,[],[f27])).
% 3.46/0.99  
% 3.46/0.99  fof(f48,plain,(
% 3.46/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.46/0.99    inference(nnf_transformation,[],[f28])).
% 3.46/0.99  
% 3.46/0.99  fof(f75,plain,(
% 3.46/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f48])).
% 3.46/0.99  
% 3.46/0.99  fof(f98,plain,(
% 3.46/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.46/0.99    inference(equality_resolution,[],[f75])).
% 3.46/0.99  
% 3.46/0.99  fof(f89,plain,(
% 3.46/0.99    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 3.46/0.99    inference(cnf_transformation,[],[f51])).
% 3.46/0.99  
% 3.46/0.99  fof(f57,plain,(
% 3.46/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.46/0.99    inference(cnf_transformation,[],[f42])).
% 3.46/0.99  
% 3.46/0.99  fof(f93,plain,(
% 3.46/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.46/0.99    inference(equality_resolution,[],[f57])).
% 3.46/0.99  
% 3.46/0.99  fof(f10,axiom,(
% 3.46/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f24,plain,(
% 3.46/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.46/0.99    inference(ennf_transformation,[],[f10])).
% 3.46/0.99  
% 3.46/0.99  fof(f70,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f24])).
% 3.46/0.99  
% 3.46/0.99  fof(f16,axiom,(
% 3.46/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f31,plain,(
% 3.46/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.46/0.99    inference(ennf_transformation,[],[f16])).
% 3.46/0.99  
% 3.46/0.99  fof(f32,plain,(
% 3.46/0.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.46/0.99    inference(flattening,[],[f31])).
% 3.46/0.99  
% 3.46/0.99  fof(f79,plain,(
% 3.46/0.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f32])).
% 3.46/0.99  
% 3.46/0.99  fof(f8,axiom,(
% 3.46/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f68,plain,(
% 3.46/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f8])).
% 3.46/0.99  
% 3.46/0.99  fof(f90,plain,(
% 3.46/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.46/0.99    inference(definition_unfolding,[],[f68,f78])).
% 3.46/0.99  
% 3.46/0.99  fof(f60,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.46/0.99    inference(cnf_transformation,[],[f44])).
% 3.46/0.99  
% 3.46/0.99  fof(f96,plain,(
% 3.46/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.46/0.99    inference(equality_resolution,[],[f60])).
% 3.46/0.99  
% 3.46/0.99  fof(f59,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f44])).
% 3.46/0.99  
% 3.46/0.99  cnf(c_7,plain,
% 3.46/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.46/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_21,plain,
% 3.46/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.46/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1648,plain,
% 3.46/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2616,plain,
% 3.46/0.99      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_7,c_1648]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_11,plain,
% 3.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.46/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1651,plain,
% 3.46/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.46/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2769,plain,
% 3.46/0.99      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2616,c_1651]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1,plain,
% 3.46/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.46/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1656,plain,
% 3.46/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.46/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3,plain,
% 3.46/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_12,plain,
% 3.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.46/0.99      | ~ r2_hidden(X2,X0)
% 3.46/0.99      | ~ v1_xboole_0(X1) ),
% 3.46/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_10,plain,
% 3.46/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.46/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_260,plain,
% 3.46/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.46/0.99      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_261,plain,
% 3.46/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.46/0.99      inference(renaming,[status(thm)],[c_260]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_335,plain,
% 3.46/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.46/0.99      inference(bin_hyper_res,[status(thm)],[c_12,c_261]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_455,plain,
% 3.46/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 3.46/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_335]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_456,plain,
% 3.46/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 3.46/0.99      inference(unflattening,[status(thm)],[c_455]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1637,plain,
% 3.46/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.46/0.99      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3086,plain,
% 3.46/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.46/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_1656,c_1637]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3196,plain,
% 3.46/0.99      ( r1_tarski(k6_partfun1(k1_xboole_0),X0) = iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2769,c_3086]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6,plain,
% 3.46/0.99      ( r1_tarski(X0,X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1653,plain,
% 3.46/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3195,plain,
% 3.46/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_1653,c_3086]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_4,plain,
% 3.46/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.46/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1654,plain,
% 3.46/0.99      ( X0 = X1
% 3.46/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.46/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_4630,plain,
% 3.46/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_3195,c_1654]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_8190,plain,
% 3.46/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_3196,c_4630]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_24,plain,
% 3.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.46/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.46/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.46/0.99      | ~ v1_funct_1(X0)
% 3.46/0.99      | ~ v1_funct_1(X3) ),
% 3.46/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1647,plain,
% 3.46/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.46/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.46/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.46/0.99      | v1_funct_1(X3) != iProver_top
% 3.46/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_20,plain,
% 3.46/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.46/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.46/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.46/0.99      | X2 = X3 ),
% 3.46/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_30,negated_conjecture,
% 3.46/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 3.46/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_588,plain,
% 3.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.46/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.46/0.99      | X0 = X3
% 3.46/0.99      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X3
% 3.46/0.99      | k6_partfun1(sK1) != X0
% 3.46/0.99      | sK1 != X2
% 3.46/0.99      | sK1 != X1 ),
% 3.46/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_589,plain,
% 3.46/0.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.46/0.99      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.46/0.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.46/0.99      inference(unflattening,[status(thm)],[c_588]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_597,plain,
% 3.46/0.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.46/0.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.46/0.99      inference(forward_subsumption_resolution,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_589,c_21]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1631,plain,
% 3.46/0.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.46/0.99      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_5070,plain,
% 3.46/0.99      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
% 3.46/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.46/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.46/0.99      | v1_funct_1(sK3) != iProver_top
% 3.46/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_1647,c_1631]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_36,negated_conjecture,
% 3.46/0.99      ( v1_funct_1(sK3) ),
% 3.46/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_37,plain,
% 3.46/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_34,negated_conjecture,
% 3.46/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.46/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_39,plain,
% 3.46/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_33,negated_conjecture,
% 3.46/0.99      ( v1_funct_1(sK4) ),
% 3.46/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_40,plain,
% 3.46/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_31,negated_conjecture,
% 3.46/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.46/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_42,plain,
% 3.46/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6015,plain,
% 3.46/0.99      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
% 3.46/0.99      inference(global_propositional_subsumption,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_5070,c_37,c_39,c_40,c_42]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_28,plain,
% 3.46/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.46/0.99      | ~ v1_funct_2(X3,X2,X4)
% 3.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.46/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.46/0.99      | ~ v1_funct_1(X3)
% 3.46/0.99      | ~ v1_funct_1(X0)
% 3.46/0.99      | v2_funct_1(X0)
% 3.46/0.99      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 3.46/0.99      | k1_xboole_0 = X4 ),
% 3.46/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1644,plain,
% 3.46/0.99      ( k1_xboole_0 = X0
% 3.46/0.99      | v1_funct_2(X1,X2,X3) != iProver_top
% 3.46/0.99      | v1_funct_2(X4,X3,X0) != iProver_top
% 3.46/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.46/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 3.46/0.99      | v1_funct_1(X4) != iProver_top
% 3.46/0.99      | v1_funct_1(X1) != iProver_top
% 3.46/0.99      | v2_funct_1(X1) = iProver_top
% 3.46/0.99      | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6041,plain,
% 3.46/0.99      ( sK1 = k1_xboole_0
% 3.46/0.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.46/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.46/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.46/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.46/0.99      | v1_funct_1(sK3) != iProver_top
% 3.46/0.99      | v1_funct_1(sK4) != iProver_top
% 3.46/0.99      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 3.46/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_6015,c_1644]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_35,negated_conjecture,
% 3.46/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.46/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_38,plain,
% 3.46/0.99      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_32,negated_conjecture,
% 3.46/0.99      ( v1_funct_2(sK4,sK2,sK1) ),
% 3.46/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_41,plain,
% 3.46/0.99      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_17,plain,
% 3.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.46/0.99      | v1_relat_1(X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_13,plain,
% 3.46/0.99      ( v5_relat_1(X0,X1)
% 3.46/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.46/0.99      | ~ v1_relat_1(X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_22,plain,
% 3.46/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.46/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.46/0.99      | ~ v1_relat_1(X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_29,negated_conjecture,
% 3.46/0.99      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 3.46/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_472,plain,
% 3.46/0.99      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.46/0.99      | ~ v2_funct_1(sK3)
% 3.46/0.99      | ~ v1_relat_1(X0)
% 3.46/0.99      | k2_relat_1(X0) != sK1
% 3.46/0.99      | sK4 != X0 ),
% 3.46/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_29]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_473,plain,
% 3.46/0.99      ( ~ v5_relat_1(sK4,k2_relat_1(sK4))
% 3.46/0.99      | ~ v2_funct_1(sK3)
% 3.46/0.99      | ~ v1_relat_1(sK4)
% 3.46/0.99      | k2_relat_1(sK4) != sK1 ),
% 3.46/0.99      inference(unflattening,[status(thm)],[c_472]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_494,plain,
% 3.46/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.46/0.99      | ~ v2_funct_1(sK3)
% 3.46/0.99      | ~ v1_relat_1(X0)
% 3.46/0.99      | ~ v1_relat_1(sK4)
% 3.46/0.99      | k2_relat_1(sK4) != X1
% 3.46/0.99      | k2_relat_1(sK4) != sK1
% 3.46/0.99      | sK4 != X0 ),
% 3.46/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_473]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_495,plain,
% 3.46/0.99      ( ~ r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
% 3.46/0.99      | ~ v2_funct_1(sK3)
% 3.46/0.99      | ~ v1_relat_1(sK4)
% 3.46/0.99      | k2_relat_1(sK4) != sK1 ),
% 3.46/0.99      inference(unflattening,[status(thm)],[c_494]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_5,plain,
% 3.46/0.99      ( r1_tarski(X0,X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_505,plain,
% 3.46/0.99      ( ~ v2_funct_1(sK3) | ~ v1_relat_1(sK4) | k2_relat_1(sK4) != sK1 ),
% 3.46/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_495,c_5]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_514,plain,
% 3.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.46/0.99      | ~ v2_funct_1(sK3)
% 3.46/0.99      | k2_relat_1(sK4) != sK1
% 3.46/0.99      | sK4 != X0 ),
% 3.46/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_505]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_515,plain,
% 3.46/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.46/0.99      | ~ v2_funct_1(sK3)
% 3.46/0.99      | k2_relat_1(sK4) != sK1 ),
% 3.46/0.99      inference(unflattening,[status(thm)],[c_514]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_907,plain,
% 3.46/0.99      ( ~ v2_funct_1(sK3) | sP1_iProver_split | k2_relat_1(sK4) != sK1 ),
% 3.46/0.99      inference(splitting,
% 3.46/0.99                [splitting(split),new_symbols(definition,[])],
% 3.46/0.99                [c_515]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_944,plain,
% 3.46/0.99      ( k2_relat_1(sK4) != sK1
% 3.46/0.99      | v2_funct_1(sK3) != iProver_top
% 3.46/0.99      | sP1_iProver_split = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_907]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1643,plain,
% 3.46/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_906,plain,
% 3.46/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.46/0.99      | ~ sP1_iProver_split ),
% 3.46/0.99      inference(splitting,
% 3.46/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.46/0.99                [c_515]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1636,plain,
% 3.46/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.46/0.99      | sP1_iProver_split != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_906]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2455,plain,
% 3.46/0.99      ( sP1_iProver_split != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_1643,c_1636]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_18,plain,
% 3.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.46/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1649,plain,
% 3.46/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.46/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3441,plain,
% 3.46/0.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_1643,c_1649]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_26,plain,
% 3.46/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.46/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.46/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.46/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.46/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.46/0.99      | ~ v1_funct_1(X3)
% 3.46/0.99      | ~ v1_funct_1(X2)
% 3.46/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.46/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_601,plain,
% 3.46/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.46/0.99      | ~ v1_funct_2(X3,X2,X1)
% 3.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.46/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.46/0.99      | ~ v1_funct_1(X3)
% 3.46/0.99      | ~ v1_funct_1(X0)
% 3.46/0.99      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.46/0.99      | k2_relset_1(X2,X1,X3) = X1
% 3.46/0.99      | k6_partfun1(X1) != k6_partfun1(sK1)
% 3.46/0.99      | sK1 != X1 ),
% 3.46/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_602,plain,
% 3.46/0.99      ( ~ v1_funct_2(X0,X1,sK1)
% 3.46/0.99      | ~ v1_funct_2(X2,sK1,X1)
% 3.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.46/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.46/0.99      | ~ v1_funct_1(X2)
% 3.46/0.99      | ~ v1_funct_1(X0)
% 3.46/0.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.46/0.99      | k2_relset_1(X1,sK1,X0) = sK1
% 3.46/0.99      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 3.46/0.99      inference(unflattening,[status(thm)],[c_601]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_682,plain,
% 3.46/0.99      ( ~ v1_funct_2(X0,X1,sK1)
% 3.46/0.99      | ~ v1_funct_2(X2,sK1,X1)
% 3.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.46/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.46/0.99      | ~ v1_funct_1(X0)
% 3.46/0.99      | ~ v1_funct_1(X2)
% 3.46/0.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.46/0.99      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 3.46/0.99      inference(equality_resolution_simp,[status(thm)],[c_602]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1630,plain,
% 3.46/0.99      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.46/0.99      | k2_relset_1(X0,sK1,X2) = sK1
% 3.46/0.99      | v1_funct_2(X2,X0,sK1) != iProver_top
% 3.46/0.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.46/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.46/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.46/0.99      | v1_funct_1(X2) != iProver_top
% 3.46/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2023,plain,
% 3.46/0.99      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 3.46/0.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.46/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.46/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.46/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.46/0.99      | v1_funct_1(sK3) != iProver_top
% 3.46/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.46/0.99      inference(equality_resolution,[status(thm)],[c_1630]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2301,plain,
% 3.46/0.99      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 3.46/0.99      inference(global_propositional_subsumption,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_2023,c_37,c_38,c_39,c_40,c_41,c_42]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3456,plain,
% 3.46/0.99      ( k2_relat_1(sK4) = sK1 ),
% 3.46/0.99      inference(light_normalisation,[status(thm)],[c_3441,c_2301]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6216,plain,
% 3.46/0.99      ( v2_funct_1(k6_partfun1(sK1)) != iProver_top | sK1 = k1_xboole_0 ),
% 3.46/0.99      inference(global_propositional_subsumption,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_6041,c_37,c_38,c_39,c_40,c_41,c_42,c_944,c_2455,
% 3.46/0.99                 c_3456]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6217,plain,
% 3.46/0.99      ( sK1 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
% 3.46/0.99      inference(renaming,[status(thm)],[c_6216]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_15,plain,
% 3.46/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.46/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1650,plain,
% 3.46/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6222,plain,
% 3.46/0.99      ( sK1 = k1_xboole_0 ),
% 3.46/0.99      inference(forward_subsumption_resolution,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_6217,c_1650]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1640,plain,
% 3.46/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2768,plain,
% 3.46/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_1640,c_1651]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_4628,plain,
% 3.46/0.99      ( k2_zfmisc_1(sK1,sK2) = sK3
% 3.46/0.99      | r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2768,c_1654]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6226,plain,
% 3.46/0.99      ( k2_zfmisc_1(k1_xboole_0,sK2) = sK3
% 3.46/0.99      | r1_tarski(k2_zfmisc_1(k1_xboole_0,sK2),sK3) != iProver_top ),
% 3.46/0.99      inference(demodulation,[status(thm)],[c_6222,c_4628]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_8,plain,
% 3.46/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.46/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6266,plain,
% 3.46/0.99      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.46/0.99      inference(demodulation,[status(thm)],[c_6226,c_8]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_7797,plain,
% 3.46/0.99      ( sK3 = k1_xboole_0 ),
% 3.46/0.99      inference(forward_subsumption_resolution,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_6266,c_3195]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_918,plain,
% 3.46/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.46/0.99      theory(equality) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6099,plain,
% 3.46/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(sK3) | sK3 != X0 ),
% 3.46/0.99      inference(instantiation,[status(thm)],[c_918]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6101,plain,
% 3.46/0.99      ( v2_funct_1(sK3)
% 3.46/0.99      | ~ v2_funct_1(k1_xboole_0)
% 3.46/0.99      | sK3 != k1_xboole_0 ),
% 3.46/0.99      inference(instantiation,[status(thm)],[c_6099]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2466,plain,
% 3.46/0.99      ( ~ sP1_iProver_split ),
% 3.46/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2455]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_910,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2106,plain,
% 3.46/0.99      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 3.46/0.99      inference(instantiation,[status(thm)],[c_910]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2107,plain,
% 3.46/0.99      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 3.46/0.99      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.46/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.46/0.99      inference(instantiation,[status(thm)],[c_2106]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1918,plain,
% 3.46/0.99      ( v2_funct_1(X0)
% 3.46/0.99      | ~ v2_funct_1(k6_partfun1(X1))
% 3.46/0.99      | X0 != k6_partfun1(X1) ),
% 3.46/0.99      inference(instantiation,[status(thm)],[c_918]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1920,plain,
% 3.46/0.99      ( ~ v2_funct_1(k6_partfun1(k1_xboole_0))
% 3.46/0.99      | v2_funct_1(k1_xboole_0)
% 3.46/0.99      | k1_xboole_0 != k6_partfun1(k1_xboole_0) ),
% 3.46/0.99      inference(instantiation,[status(thm)],[c_1918]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_103,plain,
% 3.46/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.46/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_9,plain,
% 3.46/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.46/0.99      | k1_xboole_0 = X1
% 3.46/0.99      | k1_xboole_0 = X0 ),
% 3.46/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_102,plain,
% 3.46/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.46/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.46/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_85,plain,
% 3.46/0.99      ( v2_funct_1(k6_partfun1(k1_xboole_0)) ),
% 3.46/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(contradiction,plain,
% 3.46/0.99      ( $false ),
% 3.46/0.99      inference(minisat,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_8190,c_7797,c_6101,c_3456,c_2466,c_2107,c_1920,c_907,
% 3.46/0.99                 c_103,c_102,c_85]) ).
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  ------                               Statistics
% 3.46/0.99  
% 3.46/0.99  ------ General
% 3.46/0.99  
% 3.46/0.99  abstr_ref_over_cycles:                  0
% 3.46/0.99  abstr_ref_under_cycles:                 0
% 3.46/0.99  gc_basic_clause_elim:                   0
% 3.46/0.99  forced_gc_time:                         0
% 3.46/0.99  parsing_time:                           0.008
% 3.46/0.99  unif_index_cands_time:                  0.
% 3.46/0.99  unif_index_add_time:                    0.
% 3.46/0.99  orderings_time:                         0.
% 3.46/0.99  out_proof_time:                         0.011
% 3.46/0.99  total_time:                             0.341
% 3.46/0.99  num_of_symbols:                         56
% 3.46/0.99  num_of_terms:                           15630
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing
% 3.46/0.99  
% 3.46/0.99  num_of_splits:                          2
% 3.46/0.99  num_of_split_atoms:                     2
% 3.46/0.99  num_of_reused_defs:                     0
% 3.46/0.99  num_eq_ax_congr_red:                    21
% 3.46/0.99  num_of_sem_filtered_clauses:            1
% 3.46/0.99  num_of_subtypes:                        0
% 3.46/0.99  monotx_restored_types:                  0
% 3.46/0.99  sat_num_of_epr_types:                   0
% 3.46/0.99  sat_num_of_non_cyclic_types:            0
% 3.46/0.99  sat_guarded_non_collapsed_types:        0
% 3.46/0.99  num_pure_diseq_elim:                    0
% 3.46/0.99  simp_replaced_by:                       0
% 3.46/0.99  res_preprocessed:                       156
% 3.46/0.99  prep_upred:                             0
% 3.46/0.99  prep_unflattend:                        19
% 3.46/0.99  smt_new_axioms:                         0
% 3.46/0.99  pred_elim_cands:                        6
% 3.46/0.99  pred_elim:                              5
% 3.46/0.99  pred_elim_cl:                           7
% 3.46/0.99  pred_elim_cycles:                       7
% 3.46/0.99  merged_defs:                            8
% 3.46/0.99  merged_defs_ncl:                        0
% 3.46/0.99  bin_hyper_res:                          9
% 3.46/0.99  prep_cycles:                            4
% 3.46/0.99  pred_elim_time:                         0.006
% 3.46/0.99  splitting_time:                         0.
% 3.46/0.99  sem_filter_time:                        0.
% 3.46/0.99  monotx_time:                            0.
% 3.46/0.99  subtype_inf_time:                       0.
% 3.46/0.99  
% 3.46/0.99  ------ Problem properties
% 3.46/0.99  
% 3.46/0.99  clauses:                                31
% 3.46/0.99  conjectures:                            6
% 3.46/0.99  epr:                                    8
% 3.46/0.99  horn:                                   28
% 3.46/0.99  ground:                                 9
% 3.46/0.99  unary:                                  11
% 3.46/0.99  binary:                                 9
% 3.46/0.99  lits:                                   87
% 3.46/0.99  lits_eq:                                16
% 3.46/0.99  fd_pure:                                0
% 3.46/0.99  fd_pseudo:                              0
% 3.46/0.99  fd_cond:                                2
% 3.46/0.99  fd_pseudo_cond:                         1
% 3.46/0.99  ac_symbols:                             0
% 3.46/0.99  
% 3.46/0.99  ------ Propositional Solver
% 3.46/0.99  
% 3.46/0.99  prop_solver_calls:                      28
% 3.46/0.99  prop_fast_solver_calls:                 1122
% 3.46/0.99  smt_solver_calls:                       0
% 3.46/0.99  smt_fast_solver_calls:                  0
% 3.46/0.99  prop_num_of_clauses:                    3621
% 3.46/0.99  prop_preprocess_simplified:             9701
% 3.46/0.99  prop_fo_subsumed:                       22
% 3.46/0.99  prop_solver_time:                       0.
% 3.46/0.99  smt_solver_time:                        0.
% 3.46/0.99  smt_fast_solver_time:                   0.
% 3.46/0.99  prop_fast_solver_time:                  0.
% 3.46/0.99  prop_unsat_core_time:                   0.
% 3.46/0.99  
% 3.46/0.99  ------ QBF
% 3.46/0.99  
% 3.46/0.99  qbf_q_res:                              0
% 3.46/0.99  qbf_num_tautologies:                    0
% 3.46/0.99  qbf_prep_cycles:                        0
% 3.46/0.99  
% 3.46/0.99  ------ BMC1
% 3.46/0.99  
% 3.46/0.99  bmc1_current_bound:                     -1
% 3.46/0.99  bmc1_last_solved_bound:                 -1
% 3.46/0.99  bmc1_unsat_core_size:                   -1
% 3.46/0.99  bmc1_unsat_core_parents_size:           -1
% 3.46/0.99  bmc1_merge_next_fun:                    0
% 3.46/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.46/0.99  
% 3.46/0.99  ------ Instantiation
% 3.46/0.99  
% 3.46/0.99  inst_num_of_clauses:                    964
% 3.46/0.99  inst_num_in_passive:                    574
% 3.46/0.99  inst_num_in_active:                     318
% 3.46/0.99  inst_num_in_unprocessed:                72
% 3.46/0.99  inst_num_of_loops:                      420
% 3.46/0.99  inst_num_of_learning_restarts:          0
% 3.46/0.99  inst_num_moves_active_passive:          99
% 3.46/0.99  inst_lit_activity:                      0
% 3.46/0.99  inst_lit_activity_moves:                1
% 3.46/0.99  inst_num_tautologies:                   0
% 3.46/0.99  inst_num_prop_implied:                  0
% 3.46/0.99  inst_num_existing_simplified:           0
% 3.46/0.99  inst_num_eq_res_simplified:             0
% 3.46/0.99  inst_num_child_elim:                    0
% 3.46/0.99  inst_num_of_dismatching_blockings:      90
% 3.46/0.99  inst_num_of_non_proper_insts:           610
% 3.46/0.99  inst_num_of_duplicates:                 0
% 3.46/0.99  inst_inst_num_from_inst_to_res:         0
% 3.46/0.99  inst_dismatching_checking_time:         0.
% 3.46/0.99  
% 3.46/0.99  ------ Resolution
% 3.46/0.99  
% 3.46/0.99  res_num_of_clauses:                     0
% 3.46/0.99  res_num_in_passive:                     0
% 3.46/0.99  res_num_in_active:                      0
% 3.46/0.99  res_num_of_loops:                       160
% 3.46/0.99  res_forward_subset_subsumed:            28
% 3.46/0.99  res_backward_subset_subsumed:           0
% 3.46/0.99  res_forward_subsumed:                   0
% 3.46/0.99  res_backward_subsumed:                  0
% 3.46/0.99  res_forward_subsumption_resolution:     3
% 3.46/0.99  res_backward_subsumption_resolution:    0
% 3.46/0.99  res_clause_to_clause_subsumption:       308
% 3.46/0.99  res_orphan_elimination:                 0
% 3.46/0.99  res_tautology_del:                      33
% 3.46/0.99  res_num_eq_res_simplified:              1
% 3.46/0.99  res_num_sel_changes:                    0
% 3.46/0.99  res_moves_from_active_to_pass:          0
% 3.46/0.99  
% 3.46/0.99  ------ Superposition
% 3.46/0.99  
% 3.46/0.99  sup_time_total:                         0.
% 3.46/0.99  sup_time_generating:                    0.
% 3.46/0.99  sup_time_sim_full:                      0.
% 3.46/0.99  sup_time_sim_immed:                     0.
% 3.46/0.99  
% 3.46/0.99  sup_num_of_clauses:                     75
% 3.46/0.99  sup_num_in_active:                      47
% 3.46/0.99  sup_num_in_passive:                     28
% 3.46/0.99  sup_num_of_loops:                       83
% 3.46/0.99  sup_fw_superposition:                   56
% 3.46/0.99  sup_bw_superposition:                   38
% 3.46/0.99  sup_immediate_simplified:               17
% 3.46/0.99  sup_given_eliminated:                   3
% 3.46/0.99  comparisons_done:                       0
% 3.46/0.99  comparisons_avoided:                    0
% 3.46/0.99  
% 3.46/0.99  ------ Simplifications
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  sim_fw_subset_subsumed:                 1
% 3.46/0.99  sim_bw_subset_subsumed:                 2
% 3.46/0.99  sim_fw_subsumed:                        4
% 3.46/0.99  sim_bw_subsumed:                        5
% 3.46/0.99  sim_fw_subsumption_res:                 3
% 3.46/0.99  sim_bw_subsumption_res:                 0
% 3.46/0.99  sim_tautology_del:                      1
% 3.46/0.99  sim_eq_tautology_del:                   5
% 3.46/0.99  sim_eq_res_simp:                        1
% 3.46/0.99  sim_fw_demodulated:                     10
% 3.46/0.99  sim_bw_demodulated:                     33
% 3.46/0.99  sim_light_normalised:                   7
% 3.46/0.99  sim_joinable_taut:                      0
% 3.46/0.99  sim_joinable_simp:                      0
% 3.46/0.99  sim_ac_normalised:                      0
% 3.46/0.99  sim_smt_subsumption:                    0
% 3.46/0.99  
%------------------------------------------------------------------------------
