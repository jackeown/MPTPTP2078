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
% DateTime   : Thu Dec  3 12:02:08 EST 2020

% Result     : Theorem 11.55s
% Output     : CNFRefutation 11.55s
% Verified   : 
% Statistics : Number of formulae       :  230 (1271 expanded)
%              Number of clauses        :  135 ( 369 expanded)
%              Number of leaves         :   30 ( 319 expanded)
%              Depth                    :   17
%              Number of atoms          :  714 (7793 expanded)
%              Number of equality atoms :  179 ( 507 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f22])).

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
    inference(flattening,[],[f42])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK5,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK5),k6_partfun1(X0))
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK5,X1,X0)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
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
          ( ( ~ v2_funct_2(X3,sK2)
            | ~ v2_funct_1(sK4) )
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
          & v1_funct_2(X3,sK3,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ~ v2_funct_2(sK5,sK2)
      | ~ v2_funct_1(sK4) )
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & v1_funct_2(sK5,sK3,sK2)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f43,f58,f57])).

fof(f98,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f59])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f92,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f97,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f20,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f20])).

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
    inference(flattening,[],[f40])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f100,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f77,f89])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f107,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f84])).

fof(f99,plain,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f12,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f102,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f79,f89])).

fof(f96,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_48881,plain,
    ( ~ r2_hidden(sK1(X0,sK4),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_48883,plain,
    ( ~ r2_hidden(sK1(sK2,sK4),sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_48881])).

cnf(c_720,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_21158,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_21160,plain,
    ( v2_funct_1(sK4)
    | ~ v2_funct_1(sK2)
    | sK4 != sK2 ),
    inference(instantiation,[status(thm)],[c_21158])).

cnf(c_710,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_13220,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_13222,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13220])).

cnf(c_712,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_708,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4766,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_712,c_708])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
    | k6_partfun1(sK2) != X3
    | sK2 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_408,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_27,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_57,plain,
    ( m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_410,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_57])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1695,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X3,X4,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1992,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1695])).

cnf(c_2719,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_4256,plain,
    ( m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2719])).

cnf(c_6688,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_38,c_36,c_35,c_33,c_57,c_408,c_4256])).

cnf(c_11009,plain,
    ( ~ r1_tarski(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),X0)
    | r1_tarski(k6_partfun1(sK2),X0) ),
    inference(resolution,[status(thm)],[c_4766,c_6688])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2778,plain,
    ( r1_tarski(X0,X1)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_3,c_1])).

cnf(c_11570,plain,
    ( r1_tarski(k6_partfun1(sK2),X0)
    | ~ v1_xboole_0(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)) ),
    inference(resolution,[status(thm)],[c_11009,c_2778])).

cnf(c_709,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4737,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_709,c_708])).

cnf(c_8487,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
    inference(resolution,[status(thm)],[c_4737,c_6688])).

cnf(c_8591,plain,
    ( v1_xboole_0(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
    | ~ v1_xboole_0(k6_partfun1(sK2)) ),
    inference(resolution,[status(thm)],[c_8487,c_710])).

cnf(c_11794,plain,
    ( r1_tarski(k6_partfun1(sK2),X0)
    | ~ v1_xboole_0(k6_partfun1(sK2)) ),
    inference(resolution,[status(thm)],[c_11570,c_8591])).

cnf(c_11796,plain,
    ( r1_tarski(k6_partfun1(sK2),sK2)
    | ~ v1_xboole_0(k6_partfun1(sK2)) ),
    inference(instantiation,[status(thm)],[c_11794])).

cnf(c_6728,plain,
    ( ~ r1_tarski(X0,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
    | r1_tarski(X1,k6_partfun1(sK2))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_6688,c_712])).

cnf(c_8876,plain,
    ( r1_tarski(X0,k6_partfun1(sK2))
    | ~ v1_xboole_0(X1)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_6728,c_2778])).

cnf(c_8878,plain,
    ( r1_tarski(sK2,k6_partfun1(sK2))
    | ~ v1_xboole_0(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_8876])).

cnf(c_1319,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1322,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1325,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4531,plain,
    ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1322,c_1325])).

cnf(c_42,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4923,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4531,c_42])).

cnf(c_4924,plain,
    ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4923])).

cnf(c_4935,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_4924])).

cnf(c_1705,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X3,X4,X1,X2,sK4,X0) = k5_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1972,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(X0,X1,X2,X3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1705])).

cnf(c_2654,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(X0,X1,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1972])).

cnf(c_4244,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2654])).

cnf(c_5143,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4935,c_38,c_36,c_35,c_33,c_4244])).

cnf(c_1316,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_5146,plain,
    ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2)
    | m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5143,c_1316])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_44,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1328,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5148,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5143,c_1328])).

cnf(c_5641,plain,
    ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5146,c_39,c_41,c_42,c_44,c_5148])).

cnf(c_5644,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
    inference(demodulation,[status(thm)],[c_5641,c_5143])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1323,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5651,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(k6_partfun1(sK2)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5644,c_1323])).

cnf(c_15,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1331,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5645,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK2)),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5641,c_1331])).

cnf(c_16,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_5646,plain,
    ( r1_tarski(sK2,k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5645,c_16])).

cnf(c_5382,plain,
    ( ~ r2_hidden(sK1(sK4,X0),sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5384,plain,
    ( ~ r2_hidden(sK1(sK4,sK2),sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5382])).

cnf(c_3356,plain,
    ( r1_tarski(X0,sK4)
    | r2_hidden(sK1(X0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3358,plain,
    ( r1_tarski(sK2,sK4)
    | r2_hidden(sK1(sK2,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_3356])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_13])).

cnf(c_1315,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_2729,plain,
    ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1322,c_1315])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2461,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK2))
    | v1_relat_1(sK5) ),
    inference(resolution,[status(thm)],[c_11,c_33])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2468,plain,
    ( v1_relat_1(sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2461,c_14])).

cnf(c_2469,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2468])).

cnf(c_2985,plain,
    ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2729,c_2469])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1337,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2990,plain,
    ( k2_relat_1(sK5) = sK2
    | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_1337])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_23,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_31,negated_conjecture,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_426,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_427,plain,
    ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_480,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != X1
    | k2_relat_1(sK5) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_427])).

cnf(c_481,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_491,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_481,c_7])).

cnf(c_2642,plain,
    ( ~ v2_funct_1(sK4)
    | k2_relat_1(sK5) != sK2 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2468,c_491])).

cnf(c_2605,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2606,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2605])).

cnf(c_2416,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2418,plain,
    ( ~ r1_tarski(sK4,sK2)
    | ~ r1_tarski(sK2,sK4)
    | sK4 = sK2 ),
    inference(instantiation,[status(thm)],[c_2416])).

cnf(c_2396,plain,
    ( r1_tarski(sK4,X0)
    | r2_hidden(sK1(sK4,X0),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2398,plain,
    ( r1_tarski(sK4,sK2)
    | r2_hidden(sK1(sK4,sK2),sK4) ),
    inference(instantiation,[status(thm)],[c_2396])).

cnf(c_1598,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2359,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1598])).

cnf(c_2360,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2359])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2064,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X0,X0))
    | v1_xboole_0(k6_partfun1(X0)) ),
    inference(resolution,[status(thm)],[c_10,c_27])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2341,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k6_partfun1(X0)) ),
    inference(resolution,[status(thm)],[c_2064,c_9])).

cnf(c_2343,plain,
    ( v1_xboole_0(k6_partfun1(sK2))
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2341])).

cnf(c_2070,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK3))
    | v1_xboole_0(sK4) ),
    inference(resolution,[status(thm)],[c_10,c_36])).

cnf(c_2086,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK2) ),
    inference(resolution,[status(thm)],[c_2070,c_9])).

cnf(c_1833,plain,
    ( ~ r1_tarski(X0,k6_partfun1(X1))
    | ~ r1_tarski(k6_partfun1(X1),X0)
    | X0 = k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1835,plain,
    ( ~ r1_tarski(k6_partfun1(sK2),sK2)
    | ~ r1_tarski(sK2,k6_partfun1(sK2))
    | sK2 = k6_partfun1(sK2) ),
    inference(instantiation,[status(thm)],[c_1833])).

cnf(c_1608,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1610,plain,
    ( ~ v2_funct_1(k6_partfun1(sK2))
    | v2_funct_1(sK2)
    | sK2 != k6_partfun1(sK2) ),
    inference(instantiation,[status(thm)],[c_1608])).

cnf(c_492,plain,
    ( k2_relat_1(sK5) != sK2
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_110,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_106,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_18,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_83,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_85,plain,
    ( v2_funct_1(k6_partfun1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_84,plain,
    ( v2_funct_1(k6_partfun1(sK2)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_43,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_40,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48883,c_21160,c_13222,c_11796,c_8878,c_5651,c_5646,c_5384,c_3358,c_2990,c_2642,c_2606,c_2469,c_2418,c_2398,c_2360,c_2343,c_2086,c_1835,c_1610,c_492,c_5,c_110,c_106,c_85,c_84,c_44,c_43,c_42,c_41,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.55/2.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.55/2.01  
% 11.55/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.55/2.01  
% 11.55/2.01  ------  iProver source info
% 11.55/2.01  
% 11.55/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.55/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.55/2.01  git: non_committed_changes: false
% 11.55/2.01  git: last_make_outside_of_git: false
% 11.55/2.01  
% 11.55/2.01  ------ 
% 11.55/2.01  ------ Parsing...
% 11.55/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.55/2.01  
% 11.55/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.55/2.01  
% 11.55/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.55/2.01  
% 11.55/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.55/2.01  ------ Proving...
% 11.55/2.01  ------ Problem Properties 
% 11.55/2.01  
% 11.55/2.01  
% 11.55/2.01  clauses                                 32
% 11.55/2.01  conjectures                             6
% 11.55/2.01  EPR                                     9
% 11.55/2.01  Horn                                    29
% 11.55/2.01  unary                                   14
% 11.55/2.01  binary                                  6
% 11.55/2.01  lits                                    79
% 11.55/2.01  lits eq                                 7
% 11.55/2.01  fd_pure                                 0
% 11.55/2.01  fd_pseudo                               0
% 11.55/2.01  fd_cond                                 1
% 11.55/2.01  fd_pseudo_cond                          1
% 11.55/2.01  AC symbols                              0
% 11.55/2.01  
% 11.55/2.01  ------ Input Options Time Limit: Unbounded
% 11.55/2.01  
% 11.55/2.01  
% 11.55/2.01  ------ 
% 11.55/2.01  Current options:
% 11.55/2.01  ------ 
% 11.55/2.01  
% 11.55/2.01  
% 11.55/2.01  
% 11.55/2.01  
% 11.55/2.01  ------ Proving...
% 11.55/2.01  
% 11.55/2.01  
% 11.55/2.01  % SZS status Theorem for theBenchmark.p
% 11.55/2.01  
% 11.55/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.55/2.01  
% 11.55/2.01  fof(f1,axiom,(
% 11.55/2.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f44,plain,(
% 11.55/2.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 11.55/2.01    inference(nnf_transformation,[],[f1])).
% 11.55/2.01  
% 11.55/2.01  fof(f45,plain,(
% 11.55/2.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.55/2.01    inference(rectify,[],[f44])).
% 11.55/2.01  
% 11.55/2.01  fof(f46,plain,(
% 11.55/2.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 11.55/2.01    introduced(choice_axiom,[])).
% 11.55/2.01  
% 11.55/2.01  fof(f47,plain,(
% 11.55/2.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.55/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 11.55/2.01  
% 11.55/2.01  fof(f60,plain,(
% 11.55/2.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f47])).
% 11.55/2.01  
% 11.55/2.01  fof(f14,axiom,(
% 11.55/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f32,plain,(
% 11.55/2.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.55/2.01    inference(ennf_transformation,[],[f14])).
% 11.55/2.01  
% 11.55/2.01  fof(f33,plain,(
% 11.55/2.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.55/2.01    inference(flattening,[],[f32])).
% 11.55/2.01  
% 11.55/2.01  fof(f55,plain,(
% 11.55/2.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.55/2.01    inference(nnf_transformation,[],[f33])).
% 11.55/2.01  
% 11.55/2.01  fof(f81,plain,(
% 11.55/2.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.55/2.01    inference(cnf_transformation,[],[f55])).
% 11.55/2.01  
% 11.55/2.01  fof(f21,conjecture,(
% 11.55/2.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f22,negated_conjecture,(
% 11.55/2.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 11.55/2.01    inference(negated_conjecture,[],[f21])).
% 11.55/2.01  
% 11.55/2.01  fof(f42,plain,(
% 11.55/2.01    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.55/2.01    inference(ennf_transformation,[],[f22])).
% 11.55/2.01  
% 11.55/2.01  fof(f43,plain,(
% 11.55/2.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.55/2.01    inference(flattening,[],[f42])).
% 11.55/2.01  
% 11.55/2.01  fof(f58,plain,(
% 11.55/2.01    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK5,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK5),k6_partfun1(X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK5,X1,X0) & v1_funct_1(sK5))) )),
% 11.55/2.01    introduced(choice_axiom,[])).
% 11.55/2.01  
% 11.55/2.01  fof(f57,plain,(
% 11.55/2.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(X3,sK3,sK2) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 11.55/2.01    introduced(choice_axiom,[])).
% 11.55/2.01  
% 11.55/2.01  fof(f59,plain,(
% 11.55/2.01    ((~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 11.55/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f43,f58,f57])).
% 11.55/2.01  
% 11.55/2.01  fof(f98,plain,(
% 11.55/2.01    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))),
% 11.55/2.01    inference(cnf_transformation,[],[f59])).
% 11.55/2.01  
% 11.55/2.01  fof(f17,axiom,(
% 11.55/2.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f23,plain,(
% 11.55/2.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.55/2.01    inference(pure_predicate_removal,[],[f17])).
% 11.55/2.01  
% 11.55/2.01  fof(f87,plain,(
% 11.55/2.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.55/2.01    inference(cnf_transformation,[],[f23])).
% 11.55/2.01  
% 11.55/2.01  fof(f92,plain,(
% 11.55/2.01    v1_funct_1(sK4)),
% 11.55/2.01    inference(cnf_transformation,[],[f59])).
% 11.55/2.01  
% 11.55/2.01  fof(f94,plain,(
% 11.55/2.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 11.55/2.01    inference(cnf_transformation,[],[f59])).
% 11.55/2.01  
% 11.55/2.01  fof(f95,plain,(
% 11.55/2.01    v1_funct_1(sK5)),
% 11.55/2.01    inference(cnf_transformation,[],[f59])).
% 11.55/2.01  
% 11.55/2.01  fof(f97,plain,(
% 11.55/2.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 11.55/2.01    inference(cnf_transformation,[],[f59])).
% 11.55/2.01  
% 11.55/2.01  fof(f16,axiom,(
% 11.55/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f36,plain,(
% 11.55/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.55/2.01    inference(ennf_transformation,[],[f16])).
% 11.55/2.01  
% 11.55/2.01  fof(f37,plain,(
% 11.55/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.55/2.01    inference(flattening,[],[f36])).
% 11.55/2.01  
% 11.55/2.01  fof(f86,plain,(
% 11.55/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f37])).
% 11.55/2.01  
% 11.55/2.01  fof(f2,axiom,(
% 11.55/2.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f25,plain,(
% 11.55/2.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.55/2.01    inference(ennf_transformation,[],[f2])).
% 11.55/2.01  
% 11.55/2.01  fof(f48,plain,(
% 11.55/2.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.55/2.01    inference(nnf_transformation,[],[f25])).
% 11.55/2.01  
% 11.55/2.01  fof(f49,plain,(
% 11.55/2.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.55/2.01    inference(rectify,[],[f48])).
% 11.55/2.01  
% 11.55/2.01  fof(f50,plain,(
% 11.55/2.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 11.55/2.01    introduced(choice_axiom,[])).
% 11.55/2.01  
% 11.55/2.01  fof(f51,plain,(
% 11.55/2.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.55/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).
% 11.55/2.01  
% 11.55/2.01  fof(f63,plain,(
% 11.55/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f51])).
% 11.55/2.01  
% 11.55/2.01  fof(f18,axiom,(
% 11.55/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f38,plain,(
% 11.55/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.55/2.01    inference(ennf_transformation,[],[f18])).
% 11.55/2.01  
% 11.55/2.01  fof(f39,plain,(
% 11.55/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.55/2.01    inference(flattening,[],[f38])).
% 11.55/2.01  
% 11.55/2.01  fof(f88,plain,(
% 11.55/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f39])).
% 11.55/2.01  
% 11.55/2.01  fof(f20,axiom,(
% 11.55/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f40,plain,(
% 11.55/2.01    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.55/2.01    inference(ennf_transformation,[],[f20])).
% 11.55/2.01  
% 11.55/2.01  fof(f41,plain,(
% 11.55/2.01    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.55/2.01    inference(flattening,[],[f40])).
% 11.55/2.01  
% 11.55/2.01  fof(f90,plain,(
% 11.55/2.01    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f41])).
% 11.55/2.01  
% 11.55/2.01  fof(f10,axiom,(
% 11.55/2.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f30,plain,(
% 11.55/2.01    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.55/2.01    inference(ennf_transformation,[],[f10])).
% 11.55/2.01  
% 11.55/2.01  fof(f75,plain,(
% 11.55/2.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f30])).
% 11.55/2.01  
% 11.55/2.01  fof(f11,axiom,(
% 11.55/2.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f77,plain,(
% 11.55/2.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 11.55/2.01    inference(cnf_transformation,[],[f11])).
% 11.55/2.01  
% 11.55/2.01  fof(f19,axiom,(
% 11.55/2.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f89,plain,(
% 11.55/2.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f19])).
% 11.55/2.01  
% 11.55/2.01  fof(f100,plain,(
% 11.55/2.01    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 11.55/2.01    inference(definition_unfolding,[],[f77,f89])).
% 11.55/2.01  
% 11.55/2.01  fof(f13,axiom,(
% 11.55/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f24,plain,(
% 11.55/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.55/2.01    inference(pure_predicate_removal,[],[f13])).
% 11.55/2.01  
% 11.55/2.01  fof(f31,plain,(
% 11.55/2.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.55/2.01    inference(ennf_transformation,[],[f24])).
% 11.55/2.01  
% 11.55/2.01  fof(f80,plain,(
% 11.55/2.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.55/2.01    inference(cnf_transformation,[],[f31])).
% 11.55/2.01  
% 11.55/2.01  fof(f8,axiom,(
% 11.55/2.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f29,plain,(
% 11.55/2.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.55/2.01    inference(ennf_transformation,[],[f8])).
% 11.55/2.01  
% 11.55/2.01  fof(f54,plain,(
% 11.55/2.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.55/2.01    inference(nnf_transformation,[],[f29])).
% 11.55/2.01  
% 11.55/2.01  fof(f72,plain,(
% 11.55/2.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f54])).
% 11.55/2.01  
% 11.55/2.01  fof(f7,axiom,(
% 11.55/2.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f28,plain,(
% 11.55/2.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.55/2.01    inference(ennf_transformation,[],[f7])).
% 11.55/2.01  
% 11.55/2.01  fof(f71,plain,(
% 11.55/2.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f28])).
% 11.55/2.01  
% 11.55/2.01  fof(f9,axiom,(
% 11.55/2.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f74,plain,(
% 11.55/2.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.55/2.01    inference(cnf_transformation,[],[f9])).
% 11.55/2.01  
% 11.55/2.01  fof(f4,axiom,(
% 11.55/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f52,plain,(
% 11.55/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.55/2.01    inference(nnf_transformation,[],[f4])).
% 11.55/2.01  
% 11.55/2.01  fof(f53,plain,(
% 11.55/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.55/2.01    inference(flattening,[],[f52])).
% 11.55/2.01  
% 11.55/2.01  fof(f68,plain,(
% 11.55/2.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f53])).
% 11.55/2.01  
% 11.55/2.01  fof(f73,plain,(
% 11.55/2.01    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f54])).
% 11.55/2.01  
% 11.55/2.01  fof(f15,axiom,(
% 11.55/2.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f34,plain,(
% 11.55/2.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.55/2.01    inference(ennf_transformation,[],[f15])).
% 11.55/2.01  
% 11.55/2.01  fof(f35,plain,(
% 11.55/2.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.55/2.01    inference(flattening,[],[f34])).
% 11.55/2.01  
% 11.55/2.01  fof(f56,plain,(
% 11.55/2.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.55/2.01    inference(nnf_transformation,[],[f35])).
% 11.55/2.01  
% 11.55/2.01  fof(f84,plain,(
% 11.55/2.01    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f56])).
% 11.55/2.01  
% 11.55/2.01  fof(f107,plain,(
% 11.55/2.01    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.55/2.01    inference(equality_resolution,[],[f84])).
% 11.55/2.01  
% 11.55/2.01  fof(f99,plain,(
% 11.55/2.01    ~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)),
% 11.55/2.01    inference(cnf_transformation,[],[f59])).
% 11.55/2.01  
% 11.55/2.01  fof(f67,plain,(
% 11.55/2.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.55/2.01    inference(cnf_transformation,[],[f53])).
% 11.55/2.01  
% 11.55/2.01  fof(f104,plain,(
% 11.55/2.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.55/2.01    inference(equality_resolution,[],[f67])).
% 11.55/2.01  
% 11.55/2.01  fof(f6,axiom,(
% 11.55/2.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f27,plain,(
% 11.55/2.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 11.55/2.01    inference(ennf_transformation,[],[f6])).
% 11.55/2.01  
% 11.55/2.01  fof(f70,plain,(
% 11.55/2.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f27])).
% 11.55/2.01  
% 11.55/2.01  fof(f5,axiom,(
% 11.55/2.01    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f26,plain,(
% 11.55/2.01    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 11.55/2.01    inference(ennf_transformation,[],[f5])).
% 11.55/2.01  
% 11.55/2.01  fof(f69,plain,(
% 11.55/2.01    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 11.55/2.01    inference(cnf_transformation,[],[f26])).
% 11.55/2.01  
% 11.55/2.01  fof(f3,axiom,(
% 11.55/2.01    v1_xboole_0(k1_xboole_0)),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f65,plain,(
% 11.55/2.01    v1_xboole_0(k1_xboole_0)),
% 11.55/2.01    inference(cnf_transformation,[],[f3])).
% 11.55/2.01  
% 11.55/2.01  fof(f66,plain,(
% 11.55/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.55/2.01    inference(cnf_transformation,[],[f53])).
% 11.55/2.01  
% 11.55/2.01  fof(f105,plain,(
% 11.55/2.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.55/2.01    inference(equality_resolution,[],[f66])).
% 11.55/2.01  
% 11.55/2.01  fof(f12,axiom,(
% 11.55/2.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.55/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.01  
% 11.55/2.01  fof(f79,plain,(
% 11.55/2.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.55/2.01    inference(cnf_transformation,[],[f12])).
% 11.55/2.01  
% 11.55/2.01  fof(f102,plain,(
% 11.55/2.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 11.55/2.01    inference(definition_unfolding,[],[f79,f89])).
% 11.55/2.01  
% 11.55/2.01  fof(f96,plain,(
% 11.55/2.01    v1_funct_2(sK5,sK3,sK2)),
% 11.55/2.01    inference(cnf_transformation,[],[f59])).
% 11.55/2.01  
% 11.55/2.01  fof(f93,plain,(
% 11.55/2.01    v1_funct_2(sK4,sK2,sK3)),
% 11.55/2.01    inference(cnf_transformation,[],[f59])).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1,plain,
% 11.55/2.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.55/2.01      inference(cnf_transformation,[],[f60]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_48881,plain,
% 11.55/2.01      ( ~ r2_hidden(sK1(X0,sK4),X0) | ~ v1_xboole_0(X0) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_1]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_48883,plain,
% 11.55/2.01      ( ~ r2_hidden(sK1(sK2,sK4),sK2) | ~ v1_xboole_0(sK2) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_48881]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_720,plain,
% 11.55/2.01      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 11.55/2.01      theory(equality) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_21158,plain,
% 11.55/2.01      ( ~ v2_funct_1(X0) | v2_funct_1(sK4) | sK4 != X0 ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_720]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_21160,plain,
% 11.55/2.01      ( v2_funct_1(sK4) | ~ v2_funct_1(sK2) | sK4 != sK2 ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_21158]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_710,plain,
% 11.55/2.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 11.55/2.01      theory(equality) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_13220,plain,
% 11.55/2.01      ( v1_xboole_0(X0)
% 11.55/2.01      | ~ v1_xboole_0(k1_xboole_0)
% 11.55/2.01      | X0 != k1_xboole_0 ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_710]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_13222,plain,
% 11.55/2.01      ( v1_xboole_0(sK2)
% 11.55/2.01      | ~ v1_xboole_0(k1_xboole_0)
% 11.55/2.01      | sK2 != k1_xboole_0 ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_13220]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_712,plain,
% 11.55/2.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.55/2.01      theory(equality) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_708,plain,( X0 = X0 ),theory(equality) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_4766,plain,
% 11.55/2.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_712,c_708]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_22,plain,
% 11.55/2.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.55/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.55/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.55/2.01      | X3 = X2 ),
% 11.55/2.01      inference(cnf_transformation,[],[f81]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_32,negated_conjecture,
% 11.55/2.01      ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
% 11.55/2.01      inference(cnf_transformation,[],[f98]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_407,plain,
% 11.55/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.55/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.55/2.01      | X3 = X0
% 11.55/2.01      | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
% 11.55/2.01      | k6_partfun1(sK2) != X3
% 11.55/2.01      | sK2 != X2
% 11.55/2.01      | sK2 != X1 ),
% 11.55/2.01      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_408,plain,
% 11.55/2.01      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.55/2.01      | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.55/2.01      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 11.55/2.01      inference(unflattening,[status(thm)],[c_407]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_27,plain,
% 11.55/2.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.55/2.01      inference(cnf_transformation,[],[f87]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_57,plain,
% 11.55/2.01      ( m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_27]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_410,plain,
% 11.55/2.01      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.55/2.01      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 11.55/2.01      inference(global_propositional_subsumption,
% 11.55/2.01                [status(thm)],
% 11.55/2.01                [c_408,c_57]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_38,negated_conjecture,
% 11.55/2.01      ( v1_funct_1(sK4) ),
% 11.55/2.01      inference(cnf_transformation,[],[f92]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_36,negated_conjecture,
% 11.55/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 11.55/2.01      inference(cnf_transformation,[],[f94]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_35,negated_conjecture,
% 11.55/2.01      ( v1_funct_1(sK5) ),
% 11.55/2.01      inference(cnf_transformation,[],[f95]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_33,negated_conjecture,
% 11.55/2.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 11.55/2.01      inference(cnf_transformation,[],[f97]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_25,plain,
% 11.55/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.55/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.55/2.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.55/2.01      | ~ v1_funct_1(X0)
% 11.55/2.01      | ~ v1_funct_1(X3) ),
% 11.55/2.01      inference(cnf_transformation,[],[f86]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1695,plain,
% 11.55/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.55/2.01      | m1_subset_1(k1_partfun1(X3,X4,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 11.55/2.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 11.55/2.01      | ~ v1_funct_1(X0)
% 11.55/2.01      | ~ v1_funct_1(sK4) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_25]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1992,plain,
% 11.55/2.01      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
% 11.55/2.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.55/2.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.55/2.01      | ~ v1_funct_1(sK4)
% 11.55/2.01      | ~ v1_funct_1(sK5) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_1695]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2719,plain,
% 11.55/2.01      ( m1_subset_1(k1_partfun1(X0,X1,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 11.55/2.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.55/2.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 11.55/2.01      | ~ v1_funct_1(sK4)
% 11.55/2.01      | ~ v1_funct_1(sK5) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_1992]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_4256,plain,
% 11.55/2.01      ( m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.55/2.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.55/2.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 11.55/2.01      | ~ v1_funct_1(sK4)
% 11.55/2.01      | ~ v1_funct_1(sK5) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_2719]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_6688,plain,
% 11.55/2.01      ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 11.55/2.01      inference(global_propositional_subsumption,
% 11.55/2.01                [status(thm)],
% 11.55/2.01                [c_410,c_38,c_36,c_35,c_33,c_57,c_408,c_4256]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_11009,plain,
% 11.55/2.01      ( ~ r1_tarski(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),X0)
% 11.55/2.01      | r1_tarski(k6_partfun1(sK2),X0) ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_4766,c_6688]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_3,plain,
% 11.55/2.01      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 11.55/2.01      inference(cnf_transformation,[],[f63]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2778,plain,
% 11.55/2.01      ( r1_tarski(X0,X1) | ~ v1_xboole_0(X0) ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_3,c_1]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_11570,plain,
% 11.55/2.01      ( r1_tarski(k6_partfun1(sK2),X0)
% 11.55/2.01      | ~ v1_xboole_0(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)) ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_11009,c_2778]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_709,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_4737,plain,
% 11.55/2.01      ( X0 != X1 | X1 = X0 ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_709,c_708]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_8487,plain,
% 11.55/2.01      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_4737,c_6688]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_8591,plain,
% 11.55/2.01      ( v1_xboole_0(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
% 11.55/2.01      | ~ v1_xboole_0(k6_partfun1(sK2)) ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_8487,c_710]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_11794,plain,
% 11.55/2.01      ( r1_tarski(k6_partfun1(sK2),X0)
% 11.55/2.01      | ~ v1_xboole_0(k6_partfun1(sK2)) ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_11570,c_8591]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_11796,plain,
% 11.55/2.01      ( r1_tarski(k6_partfun1(sK2),sK2)
% 11.55/2.01      | ~ v1_xboole_0(k6_partfun1(sK2)) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_11794]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_6728,plain,
% 11.55/2.01      ( ~ r1_tarski(X0,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
% 11.55/2.01      | r1_tarski(X1,k6_partfun1(sK2))
% 11.55/2.01      | X1 != X0 ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_6688,c_712]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_8876,plain,
% 11.55/2.01      ( r1_tarski(X0,k6_partfun1(sK2)) | ~ v1_xboole_0(X1) | X0 != X1 ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_6728,c_2778]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_8878,plain,
% 11.55/2.01      ( r1_tarski(sK2,k6_partfun1(sK2))
% 11.55/2.01      | ~ v1_xboole_0(sK2)
% 11.55/2.01      | sK2 != sK2 ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_8876]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1319,plain,
% 11.55/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1322,plain,
% 11.55/2.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_28,plain,
% 11.55/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.55/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.55/2.01      | ~ v1_funct_1(X0)
% 11.55/2.01      | ~ v1_funct_1(X3)
% 11.55/2.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.55/2.01      inference(cnf_transformation,[],[f88]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1325,plain,
% 11.55/2.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.55/2.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.55/2.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.55/2.01      | v1_funct_1(X5) != iProver_top
% 11.55/2.01      | v1_funct_1(X4) != iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_4531,plain,
% 11.55/2.01      ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
% 11.55/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.55/2.01      | v1_funct_1(X2) != iProver_top
% 11.55/2.01      | v1_funct_1(sK5) != iProver_top ),
% 11.55/2.01      inference(superposition,[status(thm)],[c_1322,c_1325]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_42,plain,
% 11.55/2.01      ( v1_funct_1(sK5) = iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_4923,plain,
% 11.55/2.01      ( v1_funct_1(X2) != iProver_top
% 11.55/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.55/2.01      | k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5) ),
% 11.55/2.01      inference(global_propositional_subsumption,
% 11.55/2.01                [status(thm)],
% 11.55/2.01                [c_4531,c_42]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_4924,plain,
% 11.55/2.01      ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
% 11.55/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.55/2.01      | v1_funct_1(X2) != iProver_top ),
% 11.55/2.01      inference(renaming,[status(thm)],[c_4923]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_4935,plain,
% 11.55/2.01      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
% 11.55/2.01      | v1_funct_1(sK4) != iProver_top ),
% 11.55/2.01      inference(superposition,[status(thm)],[c_1319,c_4924]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1705,plain,
% 11.55/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.55/2.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 11.55/2.01      | ~ v1_funct_1(X0)
% 11.55/2.01      | ~ v1_funct_1(sK4)
% 11.55/2.01      | k1_partfun1(X3,X4,X1,X2,sK4,X0) = k5_relat_1(sK4,X0) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_28]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1972,plain,
% 11.55/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.55/2.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.55/2.01      | ~ v1_funct_1(sK4)
% 11.55/2.01      | ~ v1_funct_1(sK5)
% 11.55/2.01      | k1_partfun1(X0,X1,X2,X3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_1705]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2654,plain,
% 11.55/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.55/2.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 11.55/2.01      | ~ v1_funct_1(sK4)
% 11.55/2.01      | ~ v1_funct_1(sK5)
% 11.55/2.01      | k1_partfun1(X0,X1,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_1972]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_4244,plain,
% 11.55/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.55/2.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 11.55/2.01      | ~ v1_funct_1(sK4)
% 11.55/2.01      | ~ v1_funct_1(sK5)
% 11.55/2.01      | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_2654]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_5143,plain,
% 11.55/2.01      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 11.55/2.01      inference(global_propositional_subsumption,
% 11.55/2.01                [status(thm)],
% 11.55/2.01                [c_4935,c_38,c_36,c_35,c_33,c_4244]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1316,plain,
% 11.55/2.01      ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
% 11.55/2.01      | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_5146,plain,
% 11.55/2.01      ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2)
% 11.55/2.01      | m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 11.55/2.01      inference(demodulation,[status(thm)],[c_5143,c_1316]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_39,plain,
% 11.55/2.01      ( v1_funct_1(sK4) = iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_41,plain,
% 11.55/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_44,plain,
% 11.55/2.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1328,plain,
% 11.55/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.55/2.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 11.55/2.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 11.55/2.01      | v1_funct_1(X0) != iProver_top
% 11.55/2.01      | v1_funct_1(X3) != iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_5148,plain,
% 11.55/2.01      ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top
% 11.55/2.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 11.55/2.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 11.55/2.01      | v1_funct_1(sK4) != iProver_top
% 11.55/2.01      | v1_funct_1(sK5) != iProver_top ),
% 11.55/2.01      inference(superposition,[status(thm)],[c_5143,c_1328]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_5641,plain,
% 11.55/2.01      ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2) ),
% 11.55/2.01      inference(global_propositional_subsumption,
% 11.55/2.01                [status(thm)],
% 11.55/2.01                [c_5146,c_39,c_41,c_42,c_44,c_5148]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_5644,plain,
% 11.55/2.01      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
% 11.55/2.01      inference(demodulation,[status(thm)],[c_5641,c_5143]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_30,plain,
% 11.55/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.55/2.01      | ~ v1_funct_2(X3,X4,X1)
% 11.55/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 11.55/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.55/2.01      | ~ v1_funct_1(X0)
% 11.55/2.01      | ~ v1_funct_1(X3)
% 11.55/2.01      | v2_funct_1(X3)
% 11.55/2.01      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 11.55/2.01      | k1_xboole_0 = X2 ),
% 11.55/2.01      inference(cnf_transformation,[],[f90]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1323,plain,
% 11.55/2.01      ( k1_xboole_0 = X0
% 11.55/2.01      | v1_funct_2(X1,X2,X0) != iProver_top
% 11.55/2.01      | v1_funct_2(X3,X4,X2) != iProver_top
% 11.55/2.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 11.55/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 11.55/2.01      | v1_funct_1(X1) != iProver_top
% 11.55/2.01      | v1_funct_1(X3) != iProver_top
% 11.55/2.01      | v2_funct_1(X3) = iProver_top
% 11.55/2.01      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_5651,plain,
% 11.55/2.01      ( sK2 = k1_xboole_0
% 11.55/2.01      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 11.55/2.01      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 11.55/2.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 11.55/2.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 11.55/2.01      | v1_funct_1(sK4) != iProver_top
% 11.55/2.01      | v1_funct_1(sK5) != iProver_top
% 11.55/2.01      | v2_funct_1(k6_partfun1(sK2)) != iProver_top
% 11.55/2.01      | v2_funct_1(sK4) = iProver_top ),
% 11.55/2.01      inference(superposition,[status(thm)],[c_5644,c_1323]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_15,plain,
% 11.55/2.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 11.55/2.01      | ~ v1_relat_1(X0)
% 11.55/2.01      | ~ v1_relat_1(X1) ),
% 11.55/2.01      inference(cnf_transformation,[],[f75]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1331,plain,
% 11.55/2.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 11.55/2.01      | v1_relat_1(X0) != iProver_top
% 11.55/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_5645,plain,
% 11.55/2.01      ( r1_tarski(k2_relat_1(k6_partfun1(sK2)),k2_relat_1(sK5)) = iProver_top
% 11.55/2.01      | v1_relat_1(sK4) != iProver_top
% 11.55/2.01      | v1_relat_1(sK5) != iProver_top ),
% 11.55/2.01      inference(superposition,[status(thm)],[c_5641,c_1331]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_16,plain,
% 11.55/2.01      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 11.55/2.01      inference(cnf_transformation,[],[f100]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_5646,plain,
% 11.55/2.01      ( r1_tarski(sK2,k2_relat_1(sK5)) = iProver_top
% 11.55/2.01      | v1_relat_1(sK4) != iProver_top
% 11.55/2.01      | v1_relat_1(sK5) != iProver_top ),
% 11.55/2.01      inference(demodulation,[status(thm)],[c_5645,c_16]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_5382,plain,
% 11.55/2.01      ( ~ r2_hidden(sK1(sK4,X0),sK4) | ~ v1_xboole_0(sK4) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_1]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_5384,plain,
% 11.55/2.01      ( ~ r2_hidden(sK1(sK4,sK2),sK4) | ~ v1_xboole_0(sK4) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_5382]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_3356,plain,
% 11.55/2.01      ( r1_tarski(X0,sK4) | r2_hidden(sK1(X0,sK4),X0) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_3]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_3358,plain,
% 11.55/2.01      ( r1_tarski(sK2,sK4) | r2_hidden(sK1(sK2,sK4),sK2) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_3356]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_20,plain,
% 11.55/2.01      ( v5_relat_1(X0,X1)
% 11.55/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.55/2.01      inference(cnf_transformation,[],[f80]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_13,plain,
% 11.55/2.01      ( ~ v5_relat_1(X0,X1)
% 11.55/2.01      | r1_tarski(k2_relat_1(X0),X1)
% 11.55/2.01      | ~ v1_relat_1(X0) ),
% 11.55/2.01      inference(cnf_transformation,[],[f72]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_447,plain,
% 11.55/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.55/2.01      | r1_tarski(k2_relat_1(X0),X2)
% 11.55/2.01      | ~ v1_relat_1(X0) ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_20,c_13]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1315,plain,
% 11.55/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.55/2.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 11.55/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2729,plain,
% 11.55/2.01      ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
% 11.55/2.01      | v1_relat_1(sK5) != iProver_top ),
% 11.55/2.01      inference(superposition,[status(thm)],[c_1322,c_1315]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_11,plain,
% 11.55/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.55/2.01      | ~ v1_relat_1(X1)
% 11.55/2.01      | v1_relat_1(X0) ),
% 11.55/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2461,plain,
% 11.55/2.01      ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK2)) | v1_relat_1(sK5) ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_11,c_33]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_14,plain,
% 11.55/2.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.55/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2468,plain,
% 11.55/2.01      ( v1_relat_1(sK5) ),
% 11.55/2.01      inference(forward_subsumption_resolution,
% 11.55/2.01                [status(thm)],
% 11.55/2.01                [c_2461,c_14]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2469,plain,
% 11.55/2.01      ( v1_relat_1(sK5) = iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_2468]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2985,plain,
% 11.55/2.01      ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top ),
% 11.55/2.01      inference(global_propositional_subsumption,
% 11.55/2.01                [status(thm)],
% 11.55/2.01                [c_2729,c_2469]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_6,plain,
% 11.55/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.55/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1337,plain,
% 11.55/2.01      ( X0 = X1
% 11.55/2.01      | r1_tarski(X1,X0) != iProver_top
% 11.55/2.01      | r1_tarski(X0,X1) != iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2990,plain,
% 11.55/2.01      ( k2_relat_1(sK5) = sK2
% 11.55/2.01      | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top ),
% 11.55/2.01      inference(superposition,[status(thm)],[c_2985,c_1337]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_12,plain,
% 11.55/2.01      ( v5_relat_1(X0,X1)
% 11.55/2.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 11.55/2.01      | ~ v1_relat_1(X0) ),
% 11.55/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_23,plain,
% 11.55/2.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 11.55/2.01      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 11.55/2.01      | ~ v1_relat_1(X0) ),
% 11.55/2.01      inference(cnf_transformation,[],[f107]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_31,negated_conjecture,
% 11.55/2.01      ( ~ v2_funct_2(sK5,sK2) | ~ v2_funct_1(sK4) ),
% 11.55/2.01      inference(cnf_transformation,[],[f99]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_426,plain,
% 11.55/2.01      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 11.55/2.01      | ~ v2_funct_1(sK4)
% 11.55/2.01      | ~ v1_relat_1(X0)
% 11.55/2.01      | k2_relat_1(X0) != sK2
% 11.55/2.01      | sK5 != X0 ),
% 11.55/2.01      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_427,plain,
% 11.55/2.01      ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
% 11.55/2.01      | ~ v2_funct_1(sK4)
% 11.55/2.01      | ~ v1_relat_1(sK5)
% 11.55/2.01      | k2_relat_1(sK5) != sK2 ),
% 11.55/2.01      inference(unflattening,[status(thm)],[c_426]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_480,plain,
% 11.55/2.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 11.55/2.01      | ~ v2_funct_1(sK4)
% 11.55/2.01      | ~ v1_relat_1(X0)
% 11.55/2.01      | ~ v1_relat_1(sK5)
% 11.55/2.01      | k2_relat_1(sK5) != X1
% 11.55/2.01      | k2_relat_1(sK5) != sK2
% 11.55/2.01      | sK5 != X0 ),
% 11.55/2.01      inference(resolution_lifted,[status(thm)],[c_12,c_427]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_481,plain,
% 11.55/2.01      ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
% 11.55/2.01      | ~ v2_funct_1(sK4)
% 11.55/2.01      | ~ v1_relat_1(sK5)
% 11.55/2.01      | k2_relat_1(sK5) != sK2 ),
% 11.55/2.01      inference(unflattening,[status(thm)],[c_480]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_7,plain,
% 11.55/2.01      ( r1_tarski(X0,X0) ),
% 11.55/2.01      inference(cnf_transformation,[],[f104]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_491,plain,
% 11.55/2.01      ( ~ v2_funct_1(sK4) | ~ v1_relat_1(sK5) | k2_relat_1(sK5) != sK2 ),
% 11.55/2.01      inference(forward_subsumption_resolution,[status(thm)],[c_481,c_7]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2642,plain,
% 11.55/2.01      ( ~ v2_funct_1(sK4) | k2_relat_1(sK5) != sK2 ),
% 11.55/2.01      inference(backward_subsumption_resolution,
% 11.55/2.01                [status(thm)],
% 11.55/2.01                [c_2468,c_491]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2605,plain,
% 11.55/2.01      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_14]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2606,plain,
% 11.55/2.01      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_2605]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2416,plain,
% 11.55/2.01      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_6]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2418,plain,
% 11.55/2.01      ( ~ r1_tarski(sK4,sK2) | ~ r1_tarski(sK2,sK4) | sK4 = sK2 ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_2416]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2396,plain,
% 11.55/2.01      ( r1_tarski(sK4,X0) | r2_hidden(sK1(sK4,X0),sK4) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_3]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2398,plain,
% 11.55/2.01      ( r1_tarski(sK4,sK2) | r2_hidden(sK1(sK4,sK2),sK4) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_2396]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1598,plain,
% 11.55/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.55/2.01      | v1_relat_1(X0)
% 11.55/2.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_11]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2359,plain,
% 11.55/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.55/2.01      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
% 11.55/2.01      | v1_relat_1(sK4) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_1598]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2360,plain,
% 11.55/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 11.55/2.01      | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 11.55/2.01      | v1_relat_1(sK4) = iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_2359]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_10,plain,
% 11.55/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.55/2.01      | ~ v1_xboole_0(X1)
% 11.55/2.01      | v1_xboole_0(X0) ),
% 11.55/2.01      inference(cnf_transformation,[],[f70]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2064,plain,
% 11.55/2.01      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X0))
% 11.55/2.01      | v1_xboole_0(k6_partfun1(X0)) ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_10,c_27]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_9,plain,
% 11.55/2.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 11.55/2.01      inference(cnf_transformation,[],[f69]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2341,plain,
% 11.55/2.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k6_partfun1(X0)) ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_2064,c_9]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2343,plain,
% 11.55/2.01      ( v1_xboole_0(k6_partfun1(sK2)) | ~ v1_xboole_0(sK2) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_2341]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2070,plain,
% 11.55/2.01      ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK3)) | v1_xboole_0(sK4) ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_10,c_36]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_2086,plain,
% 11.55/2.01      ( v1_xboole_0(sK4) | ~ v1_xboole_0(sK2) ),
% 11.55/2.01      inference(resolution,[status(thm)],[c_2070,c_9]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1833,plain,
% 11.55/2.01      ( ~ r1_tarski(X0,k6_partfun1(X1))
% 11.55/2.01      | ~ r1_tarski(k6_partfun1(X1),X0)
% 11.55/2.01      | X0 = k6_partfun1(X1) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_6]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1835,plain,
% 11.55/2.01      ( ~ r1_tarski(k6_partfun1(sK2),sK2)
% 11.55/2.01      | ~ r1_tarski(sK2,k6_partfun1(sK2))
% 11.55/2.01      | sK2 = k6_partfun1(sK2) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_1833]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1608,plain,
% 11.55/2.01      ( v2_funct_1(X0)
% 11.55/2.01      | ~ v2_funct_1(k6_partfun1(X1))
% 11.55/2.01      | X0 != k6_partfun1(X1) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_720]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_1610,plain,
% 11.55/2.01      ( ~ v2_funct_1(k6_partfun1(sK2))
% 11.55/2.01      | v2_funct_1(sK2)
% 11.55/2.01      | sK2 != k6_partfun1(sK2) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_1608]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_492,plain,
% 11.55/2.01      ( k2_relat_1(sK5) != sK2
% 11.55/2.01      | v2_funct_1(sK4) != iProver_top
% 11.55/2.01      | v1_relat_1(sK5) != iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_5,plain,
% 11.55/2.01      ( v1_xboole_0(k1_xboole_0) ),
% 11.55/2.01      inference(cnf_transformation,[],[f65]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_110,plain,
% 11.55/2.01      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_6]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_8,plain,
% 11.55/2.01      ( r1_tarski(X0,X0) ),
% 11.55/2.01      inference(cnf_transformation,[],[f105]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_106,plain,
% 11.55/2.01      ( r1_tarski(sK2,sK2) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_8]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_18,plain,
% 11.55/2.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 11.55/2.01      inference(cnf_transformation,[],[f102]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_83,plain,
% 11.55/2.01      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_85,plain,
% 11.55/2.01      ( v2_funct_1(k6_partfun1(sK2)) = iProver_top ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_83]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_84,plain,
% 11.55/2.01      ( v2_funct_1(k6_partfun1(sK2)) ),
% 11.55/2.01      inference(instantiation,[status(thm)],[c_18]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_34,negated_conjecture,
% 11.55/2.01      ( v1_funct_2(sK5,sK3,sK2) ),
% 11.55/2.01      inference(cnf_transformation,[],[f96]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_43,plain,
% 11.55/2.01      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_37,negated_conjecture,
% 11.55/2.01      ( v1_funct_2(sK4,sK2,sK3) ),
% 11.55/2.01      inference(cnf_transformation,[],[f93]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(c_40,plain,
% 11.55/2.01      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 11.55/2.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.55/2.01  
% 11.55/2.01  cnf(contradiction,plain,
% 11.55/2.01      ( $false ),
% 11.55/2.01      inference(minisat,
% 11.55/2.01                [status(thm)],
% 11.55/2.01                [c_48883,c_21160,c_13222,c_11796,c_8878,c_5651,c_5646,
% 11.55/2.01                 c_5384,c_3358,c_2990,c_2642,c_2606,c_2469,c_2418,c_2398,
% 11.55/2.01                 c_2360,c_2343,c_2086,c_1835,c_1610,c_492,c_5,c_110,
% 11.55/2.01                 c_106,c_85,c_84,c_44,c_43,c_42,c_41,c_40,c_39]) ).
% 11.55/2.01  
% 11.55/2.01  
% 11.55/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.55/2.01  
% 11.55/2.01  ------                               Statistics
% 11.55/2.01  
% 11.55/2.01  ------ Selected
% 11.55/2.01  
% 11.55/2.01  total_time:                             1.352
% 11.55/2.01  
%------------------------------------------------------------------------------
