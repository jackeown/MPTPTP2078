%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:08 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :  250 (1602 expanded)
%              Number of clauses        :  144 ( 528 expanded)
%              Number of leaves         :   28 ( 372 expanded)
%              Depth                    :   23
%              Number of atoms          :  745 (8182 expanded)
%              Number of equality atoms :  274 ( 901 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f54,f55])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f24,conjecture,(
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

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f65,plain,(
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

fof(f64,plain,
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

fof(f66,plain,
    ( ( ~ v2_funct_2(sK5,sK2)
      | ~ v2_funct_1(sK4) )
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & v1_funct_2(sK5,sK3,sK2)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f48,f65,f64])).

fof(f111,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f66])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f59])).

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

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f108,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f66])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f66])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f112,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f66])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f22,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f118,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f97,f103])).

fof(f106,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f114,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f90,f103])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f88,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f122,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f99])).

fof(f113,plain,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f119,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f15,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f116,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f92,f103])).

fof(f23,axiom,(
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

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f104,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f107,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f110,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f89,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f115,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f89,f103])).

fof(f87,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f117,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f91,f103])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1825,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1805,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_26,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_16,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_26,c_16])).

cnf(c_1795,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_2911,plain,
    ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_1795])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1824,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3637,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2911,c_1824])).

cnf(c_3937,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top
    | r2_hidden(sK1(k2_relat_1(sK5),X0),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_3637])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1818,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1819,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2746,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_1819])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_335,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_336,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_335])).

cnf(c_417,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_336])).

cnf(c_1798,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_10214,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2746,c_1798])).

cnf(c_10350,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1818,c_10214])).

cnf(c_12452,plain,
    ( r2_hidden(sK1(k2_relat_1(sK5),X0),sK2) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3937,c_10350])).

cnf(c_12453,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top
    | r2_hidden(sK1(k2_relat_1(sK5),X0),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_12452])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1826,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12459,plain,
    ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_12453,c_1826])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1822,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12469,plain,
    ( k2_relat_1(sK5) = sK2
    | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12459,c_1822])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1802,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1808,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4299,plain,
    ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_1808])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_49,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_4453,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4299,c_49])).

cnf(c_4454,plain,
    ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4453])).

cnf(c_4463,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_4454])).

cnf(c_29,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_39,negated_conjecture,
    ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
    | k6_partfun1(sK2) != X3
    | sK2 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_39])).

cnf(c_589,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_30,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_597,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_589,c_30])).

cnf(c_1796,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1875,plain,
    ( m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_2181,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1796,c_45,c_43,c_42,c_40,c_597,c_1875])).

cnf(c_4464,plain,
    ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2)
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4463,c_2181])).

cnf(c_46,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_4679,plain,
    ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4464,c_46])).

cnf(c_19,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1816,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4681,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK2)),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4679,c_1816])).

cnf(c_22,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_4682,plain,
    ( r1_tarski(sK2,k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4681,c_22])).

cnf(c_3229,plain,
    ( k2_relat_1(sK5) = sK2
    | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2911,c_1822])).

cnf(c_4873,plain,
    ( k2_relat_1(sK5) = sK2
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4682,c_3229])).

cnf(c_2747,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_1819])).

cnf(c_10215,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2747,c_1798])).

cnf(c_10353,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1818,c_10215])).

cnf(c_12598,plain,
    ( k2_relat_1(sK5) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12469,c_4873,c_10350,c_10353])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1815,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12612,plain,
    ( sK2 != k1_xboole_0
    | sK5 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_12598,c_1815])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_31,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_38,negated_conjecture,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_606,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_38])).

cnf(c_607,plain,
    ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_660,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != X1
    | k2_relat_1(sK5) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_607])).

cnf(c_661,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_671,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_661,c_7])).

cnf(c_672,plain,
    ( k2_relat_1(sK5) != sK2
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_24,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1813,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1806,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3513,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(k6_partfun1(sK2)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2181,c_1806])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_47,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_48,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_50,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_8019,plain,
    ( sK2 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK2)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3513,c_46,c_47,c_48,c_49,c_50,c_51])).

cnf(c_8023,plain,
    ( sK2 = k1_xboole_0
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_8019])).

cnf(c_13125,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12612,c_672,c_4873,c_8023,c_10350,c_10353])).

cnf(c_13132,plain,
    ( k2_relat_1(k1_xboole_0) = sK2 ),
    inference(demodulation,[status(thm)],[c_13125,c_12598])).

cnf(c_23,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1814,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3054,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1814])).

cnf(c_25,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_90,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3073,plain,
    ( k1_xboole_0 != X0
    | k6_partfun1(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3054,c_90])).

cnf(c_3074,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_3073])).

cnf(c_3076,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_3074])).

cnf(c_3082,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3076,c_22])).

cnf(c_13191,plain,
    ( sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13132,c_3082])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1827,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3001,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1827])).

cnf(c_27,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_27,c_14])).

cnf(c_1797,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_3091,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_1797])).

cnf(c_3277,plain,
    ( k1_relat_1(sK4) = sK2
    | r1_tarski(sK2,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3091,c_1822])).

cnf(c_3413,plain,
    ( k1_relat_1(sK4) = sK2
    | v1_relat_1(sK4) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3001,c_3277])).

cnf(c_13619,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13191,c_3413])).

cnf(c_2651,plain,
    ( ~ v1_relat_1(k6_partfun1(X0))
    | k1_relat_1(k6_partfun1(X0)) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2653,plain,
    ( ~ v1_relat_1(k6_partfun1(k1_xboole_0))
    | k1_relat_1(k6_partfun1(k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2651])).

cnf(c_989,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2165,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_2646,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2165])).

cnf(c_2647,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2646])).

cnf(c_2432,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1999,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2140,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_2057,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2058,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2057])).

cnf(c_1000,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1942,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_1943,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1942])).

cnf(c_1945,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1943])).

cnf(c_1888,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_1889,plain,
    ( sK4 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1888])).

cnf(c_1891,plain,
    ( sK4 != k1_xboole_0
    | v2_funct_1(sK4) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1889])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_140,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_96,plain,
    ( k1_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_93,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_95,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_91,plain,
    ( v1_relat_1(k6_partfun1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13619,c_10353,c_10350,c_4873,c_2653,c_2647,c_2432,c_2140,c_2058,c_1945,c_1891,c_672,c_140,c_96,c_95,c_91])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:30:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.02/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.02/0.99  
% 4.02/0.99  ------  iProver source info
% 4.02/0.99  
% 4.02/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.02/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.02/0.99  git: non_committed_changes: false
% 4.02/0.99  git: last_make_outside_of_git: false
% 4.02/0.99  
% 4.02/0.99  ------ 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options
% 4.02/0.99  
% 4.02/0.99  --out_options                           all
% 4.02/0.99  --tptp_safe_out                         true
% 4.02/0.99  --problem_path                          ""
% 4.02/0.99  --include_path                          ""
% 4.02/0.99  --clausifier                            res/vclausify_rel
% 4.02/0.99  --clausifier_options                    ""
% 4.02/0.99  --stdin                                 false
% 4.02/0.99  --stats_out                             all
% 4.02/0.99  
% 4.02/0.99  ------ General Options
% 4.02/0.99  
% 4.02/0.99  --fof                                   false
% 4.02/0.99  --time_out_real                         305.
% 4.02/0.99  --time_out_virtual                      -1.
% 4.02/0.99  --symbol_type_check                     false
% 4.02/0.99  --clausify_out                          false
% 4.02/0.99  --sig_cnt_out                           false
% 4.02/0.99  --trig_cnt_out                          false
% 4.02/0.99  --trig_cnt_out_tolerance                1.
% 4.02/0.99  --trig_cnt_out_sk_spl                   false
% 4.02/0.99  --abstr_cl_out                          false
% 4.02/0.99  
% 4.02/0.99  ------ Global Options
% 4.02/0.99  
% 4.02/0.99  --schedule                              default
% 4.02/0.99  --add_important_lit                     false
% 4.02/0.99  --prop_solver_per_cl                    1000
% 4.02/0.99  --min_unsat_core                        false
% 4.02/0.99  --soft_assumptions                      false
% 4.02/0.99  --soft_lemma_size                       3
% 4.02/0.99  --prop_impl_unit_size                   0
% 4.02/0.99  --prop_impl_unit                        []
% 4.02/0.99  --share_sel_clauses                     true
% 4.02/0.99  --reset_solvers                         false
% 4.02/0.99  --bc_imp_inh                            [conj_cone]
% 4.02/0.99  --conj_cone_tolerance                   3.
% 4.02/0.99  --extra_neg_conj                        none
% 4.02/0.99  --large_theory_mode                     true
% 4.02/0.99  --prolific_symb_bound                   200
% 4.02/0.99  --lt_threshold                          2000
% 4.02/0.99  --clause_weak_htbl                      true
% 4.02/0.99  --gc_record_bc_elim                     false
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing Options
% 4.02/0.99  
% 4.02/0.99  --preprocessing_flag                    true
% 4.02/0.99  --time_out_prep_mult                    0.1
% 4.02/0.99  --splitting_mode                        input
% 4.02/0.99  --splitting_grd                         true
% 4.02/0.99  --splitting_cvd                         false
% 4.02/0.99  --splitting_cvd_svl                     false
% 4.02/0.99  --splitting_nvd                         32
% 4.02/0.99  --sub_typing                            true
% 4.02/0.99  --prep_gs_sim                           true
% 4.02/0.99  --prep_unflatten                        true
% 4.02/0.99  --prep_res_sim                          true
% 4.02/0.99  --prep_upred                            true
% 4.02/0.99  --prep_sem_filter                       exhaustive
% 4.02/0.99  --prep_sem_filter_out                   false
% 4.02/0.99  --pred_elim                             true
% 4.02/0.99  --res_sim_input                         true
% 4.02/0.99  --eq_ax_congr_red                       true
% 4.02/0.99  --pure_diseq_elim                       true
% 4.02/0.99  --brand_transform                       false
% 4.02/0.99  --non_eq_to_eq                          false
% 4.02/0.99  --prep_def_merge                        true
% 4.02/0.99  --prep_def_merge_prop_impl              false
% 4.02/0.99  --prep_def_merge_mbd                    true
% 4.02/0.99  --prep_def_merge_tr_red                 false
% 4.02/0.99  --prep_def_merge_tr_cl                  false
% 4.02/0.99  --smt_preprocessing                     true
% 4.02/0.99  --smt_ac_axioms                         fast
% 4.02/0.99  --preprocessed_out                      false
% 4.02/0.99  --preprocessed_stats                    false
% 4.02/0.99  
% 4.02/0.99  ------ Abstraction refinement Options
% 4.02/0.99  
% 4.02/0.99  --abstr_ref                             []
% 4.02/0.99  --abstr_ref_prep                        false
% 4.02/0.99  --abstr_ref_until_sat                   false
% 4.02/0.99  --abstr_ref_sig_restrict                funpre
% 4.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.02/0.99  --abstr_ref_under                       []
% 4.02/0.99  
% 4.02/0.99  ------ SAT Options
% 4.02/0.99  
% 4.02/0.99  --sat_mode                              false
% 4.02/0.99  --sat_fm_restart_options                ""
% 4.02/0.99  --sat_gr_def                            false
% 4.02/0.99  --sat_epr_types                         true
% 4.02/0.99  --sat_non_cyclic_types                  false
% 4.02/0.99  --sat_finite_models                     false
% 4.02/0.99  --sat_fm_lemmas                         false
% 4.02/0.99  --sat_fm_prep                           false
% 4.02/0.99  --sat_fm_uc_incr                        true
% 4.02/0.99  --sat_out_model                         small
% 4.02/0.99  --sat_out_clauses                       false
% 4.02/0.99  
% 4.02/0.99  ------ QBF Options
% 4.02/0.99  
% 4.02/0.99  --qbf_mode                              false
% 4.02/0.99  --qbf_elim_univ                         false
% 4.02/0.99  --qbf_dom_inst                          none
% 4.02/0.99  --qbf_dom_pre_inst                      false
% 4.02/0.99  --qbf_sk_in                             false
% 4.02/0.99  --qbf_pred_elim                         true
% 4.02/0.99  --qbf_split                             512
% 4.02/0.99  
% 4.02/0.99  ------ BMC1 Options
% 4.02/0.99  
% 4.02/0.99  --bmc1_incremental                      false
% 4.02/0.99  --bmc1_axioms                           reachable_all
% 4.02/0.99  --bmc1_min_bound                        0
% 4.02/0.99  --bmc1_max_bound                        -1
% 4.02/0.99  --bmc1_max_bound_default                -1
% 4.02/0.99  --bmc1_symbol_reachability              true
% 4.02/0.99  --bmc1_property_lemmas                  false
% 4.02/0.99  --bmc1_k_induction                      false
% 4.02/0.99  --bmc1_non_equiv_states                 false
% 4.02/0.99  --bmc1_deadlock                         false
% 4.02/0.99  --bmc1_ucm                              false
% 4.02/0.99  --bmc1_add_unsat_core                   none
% 4.02/0.99  --bmc1_unsat_core_children              false
% 4.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/0.99  --bmc1_out_stat                         full
% 4.02/0.99  --bmc1_ground_init                      false
% 4.02/0.99  --bmc1_pre_inst_next_state              false
% 4.02/0.99  --bmc1_pre_inst_state                   false
% 4.02/0.99  --bmc1_pre_inst_reach_state             false
% 4.02/0.99  --bmc1_out_unsat_core                   false
% 4.02/0.99  --bmc1_aig_witness_out                  false
% 4.02/0.99  --bmc1_verbose                          false
% 4.02/0.99  --bmc1_dump_clauses_tptp                false
% 4.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.02/0.99  --bmc1_dump_file                        -
% 4.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.02/0.99  --bmc1_ucm_extend_mode                  1
% 4.02/0.99  --bmc1_ucm_init_mode                    2
% 4.02/0.99  --bmc1_ucm_cone_mode                    none
% 4.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.02/0.99  --bmc1_ucm_relax_model                  4
% 4.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/0.99  --bmc1_ucm_layered_model                none
% 4.02/0.99  --bmc1_ucm_max_lemma_size               10
% 4.02/0.99  
% 4.02/0.99  ------ AIG Options
% 4.02/0.99  
% 4.02/0.99  --aig_mode                              false
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation Options
% 4.02/0.99  
% 4.02/0.99  --instantiation_flag                    true
% 4.02/0.99  --inst_sos_flag                         true
% 4.02/0.99  --inst_sos_phase                        true
% 4.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel_side                     num_symb
% 4.02/0.99  --inst_solver_per_active                1400
% 4.02/0.99  --inst_solver_calls_frac                1.
% 4.02/0.99  --inst_passive_queue_type               priority_queues
% 4.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/0.99  --inst_passive_queues_freq              [25;2]
% 4.02/0.99  --inst_dismatching                      true
% 4.02/0.99  --inst_eager_unprocessed_to_passive     true
% 4.02/0.99  --inst_prop_sim_given                   true
% 4.02/0.99  --inst_prop_sim_new                     false
% 4.02/0.99  --inst_subs_new                         false
% 4.02/0.99  --inst_eq_res_simp                      false
% 4.02/0.99  --inst_subs_given                       false
% 4.02/0.99  --inst_orphan_elimination               true
% 4.02/0.99  --inst_learning_loop_flag               true
% 4.02/0.99  --inst_learning_start                   3000
% 4.02/0.99  --inst_learning_factor                  2
% 4.02/0.99  --inst_start_prop_sim_after_learn       3
% 4.02/0.99  --inst_sel_renew                        solver
% 4.02/0.99  --inst_lit_activity_flag                true
% 4.02/0.99  --inst_restr_to_given                   false
% 4.02/0.99  --inst_activity_threshold               500
% 4.02/0.99  --inst_out_proof                        true
% 4.02/0.99  
% 4.02/0.99  ------ Resolution Options
% 4.02/0.99  
% 4.02/0.99  --resolution_flag                       true
% 4.02/0.99  --res_lit_sel                           adaptive
% 4.02/0.99  --res_lit_sel_side                      none
% 4.02/0.99  --res_ordering                          kbo
% 4.02/0.99  --res_to_prop_solver                    active
% 4.02/0.99  --res_prop_simpl_new                    false
% 4.02/0.99  --res_prop_simpl_given                  true
% 4.02/0.99  --res_passive_queue_type                priority_queues
% 4.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/0.99  --res_passive_queues_freq               [15;5]
% 4.02/0.99  --res_forward_subs                      full
% 4.02/0.99  --res_backward_subs                     full
% 4.02/0.99  --res_forward_subs_resolution           true
% 4.02/0.99  --res_backward_subs_resolution          true
% 4.02/0.99  --res_orphan_elimination                true
% 4.02/0.99  --res_time_limit                        2.
% 4.02/0.99  --res_out_proof                         true
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Options
% 4.02/0.99  
% 4.02/0.99  --superposition_flag                    true
% 4.02/0.99  --sup_passive_queue_type                priority_queues
% 4.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.02/0.99  --demod_completeness_check              fast
% 4.02/0.99  --demod_use_ground                      true
% 4.02/0.99  --sup_to_prop_solver                    passive
% 4.02/0.99  --sup_prop_simpl_new                    true
% 4.02/0.99  --sup_prop_simpl_given                  true
% 4.02/0.99  --sup_fun_splitting                     true
% 4.02/0.99  --sup_smt_interval                      50000
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Simplification Setup
% 4.02/0.99  
% 4.02/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.02/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_immed_triv                        [TrivRules]
% 4.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_bw_main                     []
% 4.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_input_bw                          []
% 4.02/0.99  
% 4.02/0.99  ------ Combination Options
% 4.02/0.99  
% 4.02/0.99  --comb_res_mult                         3
% 4.02/0.99  --comb_sup_mult                         2
% 4.02/0.99  --comb_inst_mult                        10
% 4.02/0.99  
% 4.02/0.99  ------ Debug Options
% 4.02/0.99  
% 4.02/0.99  --dbg_backtrace                         false
% 4.02/0.99  --dbg_dump_prop_clauses                 false
% 4.02/0.99  --dbg_dump_prop_clauses_file            -
% 4.02/0.99  --dbg_out_stat                          false
% 4.02/0.99  ------ Parsing...
% 4.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/0.99  ------ Proving...
% 4.02/0.99  ------ Problem Properties 
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  clauses                                 37
% 4.02/0.99  conjectures                             6
% 4.02/0.99  EPR                                     11
% 4.02/0.99  Horn                                    34
% 4.02/0.99  unary                                   14
% 4.02/0.99  binary                                  7
% 4.02/0.99  lits                                    93
% 4.02/0.99  lits eq                                 11
% 4.02/0.99  fd_pure                                 0
% 4.02/0.99  fd_pseudo                               0
% 4.02/0.99  fd_cond                                 3
% 4.02/0.99  fd_pseudo_cond                          1
% 4.02/0.99  AC symbols                              0
% 4.02/0.99  
% 4.02/0.99  ------ Schedule dynamic 5 is on 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  ------ 
% 4.02/0.99  Current options:
% 4.02/0.99  ------ 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options
% 4.02/0.99  
% 4.02/0.99  --out_options                           all
% 4.02/0.99  --tptp_safe_out                         true
% 4.02/0.99  --problem_path                          ""
% 4.02/0.99  --include_path                          ""
% 4.02/0.99  --clausifier                            res/vclausify_rel
% 4.02/0.99  --clausifier_options                    ""
% 4.02/0.99  --stdin                                 false
% 4.02/0.99  --stats_out                             all
% 4.02/0.99  
% 4.02/0.99  ------ General Options
% 4.02/0.99  
% 4.02/0.99  --fof                                   false
% 4.02/0.99  --time_out_real                         305.
% 4.02/0.99  --time_out_virtual                      -1.
% 4.02/0.99  --symbol_type_check                     false
% 4.02/0.99  --clausify_out                          false
% 4.02/0.99  --sig_cnt_out                           false
% 4.02/0.99  --trig_cnt_out                          false
% 4.02/0.99  --trig_cnt_out_tolerance                1.
% 4.02/0.99  --trig_cnt_out_sk_spl                   false
% 4.02/0.99  --abstr_cl_out                          false
% 4.02/0.99  
% 4.02/0.99  ------ Global Options
% 4.02/0.99  
% 4.02/0.99  --schedule                              default
% 4.02/0.99  --add_important_lit                     false
% 4.02/0.99  --prop_solver_per_cl                    1000
% 4.02/0.99  --min_unsat_core                        false
% 4.02/0.99  --soft_assumptions                      false
% 4.02/0.99  --soft_lemma_size                       3
% 4.02/0.99  --prop_impl_unit_size                   0
% 4.02/0.99  --prop_impl_unit                        []
% 4.02/0.99  --share_sel_clauses                     true
% 4.02/0.99  --reset_solvers                         false
% 4.02/0.99  --bc_imp_inh                            [conj_cone]
% 4.02/0.99  --conj_cone_tolerance                   3.
% 4.02/0.99  --extra_neg_conj                        none
% 4.02/0.99  --large_theory_mode                     true
% 4.02/0.99  --prolific_symb_bound                   200
% 4.02/0.99  --lt_threshold                          2000
% 4.02/0.99  --clause_weak_htbl                      true
% 4.02/0.99  --gc_record_bc_elim                     false
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing Options
% 4.02/0.99  
% 4.02/0.99  --preprocessing_flag                    true
% 4.02/0.99  --time_out_prep_mult                    0.1
% 4.02/0.99  --splitting_mode                        input
% 4.02/0.99  --splitting_grd                         true
% 4.02/0.99  --splitting_cvd                         false
% 4.02/0.99  --splitting_cvd_svl                     false
% 4.02/0.99  --splitting_nvd                         32
% 4.02/0.99  --sub_typing                            true
% 4.02/0.99  --prep_gs_sim                           true
% 4.02/0.99  --prep_unflatten                        true
% 4.02/0.99  --prep_res_sim                          true
% 4.02/0.99  --prep_upred                            true
% 4.02/0.99  --prep_sem_filter                       exhaustive
% 4.02/0.99  --prep_sem_filter_out                   false
% 4.02/0.99  --pred_elim                             true
% 4.02/0.99  --res_sim_input                         true
% 4.02/0.99  --eq_ax_congr_red                       true
% 4.02/0.99  --pure_diseq_elim                       true
% 4.02/0.99  --brand_transform                       false
% 4.02/0.99  --non_eq_to_eq                          false
% 4.02/0.99  --prep_def_merge                        true
% 4.02/0.99  --prep_def_merge_prop_impl              false
% 4.02/0.99  --prep_def_merge_mbd                    true
% 4.02/0.99  --prep_def_merge_tr_red                 false
% 4.02/0.99  --prep_def_merge_tr_cl                  false
% 4.02/0.99  --smt_preprocessing                     true
% 4.02/0.99  --smt_ac_axioms                         fast
% 4.02/0.99  --preprocessed_out                      false
% 4.02/0.99  --preprocessed_stats                    false
% 4.02/0.99  
% 4.02/0.99  ------ Abstraction refinement Options
% 4.02/0.99  
% 4.02/0.99  --abstr_ref                             []
% 4.02/0.99  --abstr_ref_prep                        false
% 4.02/0.99  --abstr_ref_until_sat                   false
% 4.02/0.99  --abstr_ref_sig_restrict                funpre
% 4.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.02/0.99  --abstr_ref_under                       []
% 4.02/0.99  
% 4.02/0.99  ------ SAT Options
% 4.02/0.99  
% 4.02/0.99  --sat_mode                              false
% 4.02/0.99  --sat_fm_restart_options                ""
% 4.02/0.99  --sat_gr_def                            false
% 4.02/0.99  --sat_epr_types                         true
% 4.02/0.99  --sat_non_cyclic_types                  false
% 4.02/0.99  --sat_finite_models                     false
% 4.02/0.99  --sat_fm_lemmas                         false
% 4.02/0.99  --sat_fm_prep                           false
% 4.02/0.99  --sat_fm_uc_incr                        true
% 4.02/0.99  --sat_out_model                         small
% 4.02/0.99  --sat_out_clauses                       false
% 4.02/0.99  
% 4.02/0.99  ------ QBF Options
% 4.02/0.99  
% 4.02/0.99  --qbf_mode                              false
% 4.02/0.99  --qbf_elim_univ                         false
% 4.02/0.99  --qbf_dom_inst                          none
% 4.02/0.99  --qbf_dom_pre_inst                      false
% 4.02/0.99  --qbf_sk_in                             false
% 4.02/0.99  --qbf_pred_elim                         true
% 4.02/0.99  --qbf_split                             512
% 4.02/0.99  
% 4.02/0.99  ------ BMC1 Options
% 4.02/0.99  
% 4.02/0.99  --bmc1_incremental                      false
% 4.02/0.99  --bmc1_axioms                           reachable_all
% 4.02/0.99  --bmc1_min_bound                        0
% 4.02/0.99  --bmc1_max_bound                        -1
% 4.02/0.99  --bmc1_max_bound_default                -1
% 4.02/0.99  --bmc1_symbol_reachability              true
% 4.02/0.99  --bmc1_property_lemmas                  false
% 4.02/0.99  --bmc1_k_induction                      false
% 4.02/0.99  --bmc1_non_equiv_states                 false
% 4.02/0.99  --bmc1_deadlock                         false
% 4.02/0.99  --bmc1_ucm                              false
% 4.02/0.99  --bmc1_add_unsat_core                   none
% 4.02/0.99  --bmc1_unsat_core_children              false
% 4.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/0.99  --bmc1_out_stat                         full
% 4.02/0.99  --bmc1_ground_init                      false
% 4.02/0.99  --bmc1_pre_inst_next_state              false
% 4.02/0.99  --bmc1_pre_inst_state                   false
% 4.02/0.99  --bmc1_pre_inst_reach_state             false
% 4.02/0.99  --bmc1_out_unsat_core                   false
% 4.02/0.99  --bmc1_aig_witness_out                  false
% 4.02/0.99  --bmc1_verbose                          false
% 4.02/0.99  --bmc1_dump_clauses_tptp                false
% 4.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.02/0.99  --bmc1_dump_file                        -
% 4.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.02/0.99  --bmc1_ucm_extend_mode                  1
% 4.02/0.99  --bmc1_ucm_init_mode                    2
% 4.02/0.99  --bmc1_ucm_cone_mode                    none
% 4.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.02/0.99  --bmc1_ucm_relax_model                  4
% 4.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/0.99  --bmc1_ucm_layered_model                none
% 4.02/0.99  --bmc1_ucm_max_lemma_size               10
% 4.02/0.99  
% 4.02/0.99  ------ AIG Options
% 4.02/0.99  
% 4.02/0.99  --aig_mode                              false
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation Options
% 4.02/0.99  
% 4.02/0.99  --instantiation_flag                    true
% 4.02/0.99  --inst_sos_flag                         true
% 4.02/0.99  --inst_sos_phase                        true
% 4.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel_side                     none
% 4.02/0.99  --inst_solver_per_active                1400
% 4.02/0.99  --inst_solver_calls_frac                1.
% 4.02/0.99  --inst_passive_queue_type               priority_queues
% 4.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/0.99  --inst_passive_queues_freq              [25;2]
% 4.02/0.99  --inst_dismatching                      true
% 4.02/0.99  --inst_eager_unprocessed_to_passive     true
% 4.02/0.99  --inst_prop_sim_given                   true
% 4.02/0.99  --inst_prop_sim_new                     false
% 4.02/0.99  --inst_subs_new                         false
% 4.02/0.99  --inst_eq_res_simp                      false
% 4.02/0.99  --inst_subs_given                       false
% 4.02/0.99  --inst_orphan_elimination               true
% 4.02/0.99  --inst_learning_loop_flag               true
% 4.02/0.99  --inst_learning_start                   3000
% 4.02/0.99  --inst_learning_factor                  2
% 4.02/0.99  --inst_start_prop_sim_after_learn       3
% 4.02/0.99  --inst_sel_renew                        solver
% 4.02/0.99  --inst_lit_activity_flag                true
% 4.02/0.99  --inst_restr_to_given                   false
% 4.02/0.99  --inst_activity_threshold               500
% 4.02/0.99  --inst_out_proof                        true
% 4.02/0.99  
% 4.02/0.99  ------ Resolution Options
% 4.02/0.99  
% 4.02/0.99  --resolution_flag                       false
% 4.02/0.99  --res_lit_sel                           adaptive
% 4.02/0.99  --res_lit_sel_side                      none
% 4.02/0.99  --res_ordering                          kbo
% 4.02/0.99  --res_to_prop_solver                    active
% 4.02/0.99  --res_prop_simpl_new                    false
% 4.02/0.99  --res_prop_simpl_given                  true
% 4.02/0.99  --res_passive_queue_type                priority_queues
% 4.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/0.99  --res_passive_queues_freq               [15;5]
% 4.02/0.99  --res_forward_subs                      full
% 4.02/0.99  --res_backward_subs                     full
% 4.02/0.99  --res_forward_subs_resolution           true
% 4.02/0.99  --res_backward_subs_resolution          true
% 4.02/0.99  --res_orphan_elimination                true
% 4.02/0.99  --res_time_limit                        2.
% 4.02/0.99  --res_out_proof                         true
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Options
% 4.02/0.99  
% 4.02/0.99  --superposition_flag                    true
% 4.02/0.99  --sup_passive_queue_type                priority_queues
% 4.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.02/0.99  --demod_completeness_check              fast
% 4.02/0.99  --demod_use_ground                      true
% 4.02/0.99  --sup_to_prop_solver                    passive
% 4.02/0.99  --sup_prop_simpl_new                    true
% 4.02/0.99  --sup_prop_simpl_given                  true
% 4.02/0.99  --sup_fun_splitting                     true
% 4.02/0.99  --sup_smt_interval                      50000
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Simplification Setup
% 4.02/0.99  
% 4.02/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.02/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_immed_triv                        [TrivRules]
% 4.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_bw_main                     []
% 4.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_input_bw                          []
% 4.02/0.99  
% 4.02/0.99  ------ Combination Options
% 4.02/0.99  
% 4.02/0.99  --comb_res_mult                         3
% 4.02/0.99  --comb_sup_mult                         2
% 4.02/0.99  --comb_inst_mult                        10
% 4.02/0.99  
% 4.02/0.99  ------ Debug Options
% 4.02/0.99  
% 4.02/0.99  --dbg_backtrace                         false
% 4.02/0.99  --dbg_dump_prop_clauses                 false
% 4.02/0.99  --dbg_dump_prop_clauses_file            -
% 4.02/0.99  --dbg_out_stat                          false
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  ------ Proving...
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  % SZS status Theorem for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  fof(f2,axiom,(
% 4.02/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f26,plain,(
% 4.02/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f2])).
% 4.02/0.99  
% 4.02/0.99  fof(f53,plain,(
% 4.02/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.02/0.99    inference(nnf_transformation,[],[f26])).
% 4.02/0.99  
% 4.02/0.99  fof(f54,plain,(
% 4.02/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.02/0.99    inference(rectify,[],[f53])).
% 4.02/0.99  
% 4.02/0.99  fof(f55,plain,(
% 4.02/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f56,plain,(
% 4.02/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f54,f55])).
% 4.02/0.99  
% 4.02/0.99  fof(f70,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f56])).
% 4.02/0.99  
% 4.02/0.99  fof(f24,conjecture,(
% 4.02/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f25,negated_conjecture,(
% 4.02/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 4.02/0.99    inference(negated_conjecture,[],[f24])).
% 4.02/0.99  
% 4.02/0.99  fof(f47,plain,(
% 4.02/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 4.02/0.99    inference(ennf_transformation,[],[f25])).
% 4.02/0.99  
% 4.02/0.99  fof(f48,plain,(
% 4.02/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 4.02/0.99    inference(flattening,[],[f47])).
% 4.02/0.99  
% 4.02/0.99  fof(f65,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK5,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK5),k6_partfun1(X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK5,X1,X0) & v1_funct_1(sK5))) )),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f64,plain,(
% 4.02/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(X3,sK3,sK2) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f66,plain,(
% 4.02/0.99    ((~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 4.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f48,f65,f64])).
% 4.02/0.99  
% 4.02/0.99  fof(f111,plain,(
% 4.02/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 4.02/0.99    inference(cnf_transformation,[],[f66])).
% 4.02/0.99  
% 4.02/0.99  fof(f16,axiom,(
% 4.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f36,plain,(
% 4.02/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.02/0.99    inference(ennf_transformation,[],[f16])).
% 4.02/0.99  
% 4.02/0.99  fof(f94,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f36])).
% 4.02/0.99  
% 4.02/0.99  fof(f9,axiom,(
% 4.02/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f30,plain,(
% 4.02/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.02/0.99    inference(ennf_transformation,[],[f9])).
% 4.02/0.99  
% 4.02/0.99  fof(f61,plain,(
% 4.02/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.02/0.99    inference(nnf_transformation,[],[f30])).
% 4.02/0.99  
% 4.02/0.99  fof(f82,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f61])).
% 4.02/0.99  
% 4.02/0.99  fof(f69,plain,(
% 4.02/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f56])).
% 4.02/0.99  
% 4.02/0.99  fof(f10,axiom,(
% 4.02/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f84,plain,(
% 4.02/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f10])).
% 4.02/0.99  
% 4.02/0.99  fof(f6,axiom,(
% 4.02/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f59,plain,(
% 4.02/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.02/0.99    inference(nnf_transformation,[],[f6])).
% 4.02/0.99  
% 4.02/0.99  fof(f77,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f59])).
% 4.02/0.99  
% 4.02/0.99  fof(f7,axiom,(
% 4.02/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f28,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f7])).
% 4.02/0.99  
% 4.02/0.99  fof(f79,plain,(
% 4.02/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f28])).
% 4.02/0.99  
% 4.02/0.99  fof(f78,plain,(
% 4.02/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f59])).
% 4.02/0.99  
% 4.02/0.99  fof(f71,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f56])).
% 4.02/0.99  
% 4.02/0.99  fof(f4,axiom,(
% 4.02/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f57,plain,(
% 4.02/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.02/0.99    inference(nnf_transformation,[],[f4])).
% 4.02/0.99  
% 4.02/0.99  fof(f58,plain,(
% 4.02/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.02/0.99    inference(flattening,[],[f57])).
% 4.02/0.99  
% 4.02/0.99  fof(f75,plain,(
% 4.02/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f58])).
% 4.02/0.99  
% 4.02/0.99  fof(f108,plain,(
% 4.02/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 4.02/0.99    inference(cnf_transformation,[],[f66])).
% 4.02/0.99  
% 4.02/0.99  fof(f21,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f43,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.02/0.99    inference(ennf_transformation,[],[f21])).
% 4.02/0.99  
% 4.02/0.99  fof(f44,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.02/0.99    inference(flattening,[],[f43])).
% 4.02/0.99  
% 4.02/0.99  fof(f102,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f44])).
% 4.02/0.99  
% 4.02/0.99  fof(f109,plain,(
% 4.02/0.99    v1_funct_1(sK5)),
% 4.02/0.99    inference(cnf_transformation,[],[f66])).
% 4.02/0.99  
% 4.02/0.99  fof(f17,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f37,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.02/0.99    inference(ennf_transformation,[],[f17])).
% 4.02/0.99  
% 4.02/0.99  fof(f38,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.02/0.99    inference(flattening,[],[f37])).
% 4.02/0.99  
% 4.02/0.99  fof(f62,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.02/0.99    inference(nnf_transformation,[],[f38])).
% 4.02/0.99  
% 4.02/0.99  fof(f95,plain,(
% 4.02/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f62])).
% 4.02/0.99  
% 4.02/0.99  fof(f112,plain,(
% 4.02/0.99    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))),
% 4.02/0.99    inference(cnf_transformation,[],[f66])).
% 4.02/0.99  
% 4.02/0.99  fof(f18,axiom,(
% 4.02/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f97,plain,(
% 4.02/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f18])).
% 4.02/0.99  
% 4.02/0.99  fof(f22,axiom,(
% 4.02/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f103,plain,(
% 4.02/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f22])).
% 4.02/0.99  
% 4.02/0.99  fof(f118,plain,(
% 4.02/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.02/0.99    inference(definition_unfolding,[],[f97,f103])).
% 4.02/0.99  
% 4.02/0.99  fof(f106,plain,(
% 4.02/0.99    v1_funct_1(sK4)),
% 4.02/0.99    inference(cnf_transformation,[],[f66])).
% 4.02/0.99  
% 4.02/0.99  fof(f20,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f41,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.02/0.99    inference(ennf_transformation,[],[f20])).
% 4.02/0.99  
% 4.02/0.99  fof(f42,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.02/0.99    inference(flattening,[],[f41])).
% 4.02/0.99  
% 4.02/0.99  fof(f101,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f42])).
% 4.02/0.99  
% 4.02/0.99  fof(f12,axiom,(
% 4.02/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f33,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f12])).
% 4.02/0.99  
% 4.02/0.99  fof(f86,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f33])).
% 4.02/0.99  
% 4.02/0.99  fof(f14,axiom,(
% 4.02/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f90,plain,(
% 4.02/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.02/0.99    inference(cnf_transformation,[],[f14])).
% 4.02/0.99  
% 4.02/0.99  fof(f114,plain,(
% 4.02/0.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 4.02/0.99    inference(definition_unfolding,[],[f90,f103])).
% 4.02/0.99  
% 4.02/0.99  fof(f13,axiom,(
% 4.02/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f34,plain,(
% 4.02/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f13])).
% 4.02/0.99  
% 4.02/0.99  fof(f35,plain,(
% 4.02/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.02/0.99    inference(flattening,[],[f34])).
% 4.02/0.99  
% 4.02/0.99  fof(f88,plain,(
% 4.02/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f35])).
% 4.02/0.99  
% 4.02/0.99  fof(f83,plain,(
% 4.02/0.99    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f61])).
% 4.02/0.99  
% 4.02/0.99  fof(f19,axiom,(
% 4.02/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f39,plain,(
% 4.02/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.02/0.99    inference(ennf_transformation,[],[f19])).
% 4.02/0.99  
% 4.02/0.99  fof(f40,plain,(
% 4.02/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.02/0.99    inference(flattening,[],[f39])).
% 4.02/0.99  
% 4.02/0.99  fof(f63,plain,(
% 4.02/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.02/0.99    inference(nnf_transformation,[],[f40])).
% 4.02/0.99  
% 4.02/0.99  fof(f99,plain,(
% 4.02/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f63])).
% 4.02/0.99  
% 4.02/0.99  fof(f122,plain,(
% 4.02/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.02/0.99    inference(equality_resolution,[],[f99])).
% 4.02/0.99  
% 4.02/0.99  fof(f113,plain,(
% 4.02/0.99    ~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)),
% 4.02/0.99    inference(cnf_transformation,[],[f66])).
% 4.02/0.99  
% 4.02/0.99  fof(f74,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.02/0.99    inference(cnf_transformation,[],[f58])).
% 4.02/0.99  
% 4.02/0.99  fof(f119,plain,(
% 4.02/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.02/0.99    inference(equality_resolution,[],[f74])).
% 4.02/0.99  
% 4.02/0.99  fof(f15,axiom,(
% 4.02/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f92,plain,(
% 4.02/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f15])).
% 4.02/0.99  
% 4.02/0.99  fof(f116,plain,(
% 4.02/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 4.02/0.99    inference(definition_unfolding,[],[f92,f103])).
% 4.02/0.99  
% 4.02/0.99  fof(f23,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f45,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 4.02/0.99    inference(ennf_transformation,[],[f23])).
% 4.02/0.99  
% 4.02/0.99  fof(f46,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 4.02/0.99    inference(flattening,[],[f45])).
% 4.02/0.99  
% 4.02/0.99  fof(f104,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f46])).
% 4.02/0.99  
% 4.02/0.99  fof(f107,plain,(
% 4.02/0.99    v1_funct_2(sK4,sK2,sK3)),
% 4.02/0.99    inference(cnf_transformation,[],[f66])).
% 4.02/0.99  
% 4.02/0.99  fof(f110,plain,(
% 4.02/0.99    v1_funct_2(sK5,sK3,sK2)),
% 4.02/0.99    inference(cnf_transformation,[],[f66])).
% 4.02/0.99  
% 4.02/0.99  fof(f89,plain,(
% 4.02/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.02/0.99    inference(cnf_transformation,[],[f14])).
% 4.02/0.99  
% 4.02/0.99  fof(f115,plain,(
% 4.02/0.99    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 4.02/0.99    inference(definition_unfolding,[],[f89,f103])).
% 4.02/0.99  
% 4.02/0.99  fof(f87,plain,(
% 4.02/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f35])).
% 4.02/0.99  
% 4.02/0.99  fof(f91,plain,(
% 4.02/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f15])).
% 4.02/0.99  
% 4.02/0.99  fof(f117,plain,(
% 4.02/0.99    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 4.02/0.99    inference(definition_unfolding,[],[f91,f103])).
% 4.02/0.99  
% 4.02/0.99  fof(f1,axiom,(
% 4.02/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f49,plain,(
% 4.02/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 4.02/0.99    inference(nnf_transformation,[],[f1])).
% 4.02/0.99  
% 4.02/0.99  fof(f50,plain,(
% 4.02/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.02/0.99    inference(rectify,[],[f49])).
% 4.02/0.99  
% 4.02/0.99  fof(f51,plain,(
% 4.02/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f52,plain,(
% 4.02/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 4.02/0.99  
% 4.02/0.99  fof(f67,plain,(
% 4.02/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f52])).
% 4.02/0.99  
% 4.02/0.99  fof(f93,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f36])).
% 4.02/0.99  
% 4.02/0.99  fof(f8,axiom,(
% 4.02/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f29,plain,(
% 4.02/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.02/0.99    inference(ennf_transformation,[],[f8])).
% 4.02/0.99  
% 4.02/0.99  fof(f60,plain,(
% 4.02/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.02/0.99    inference(nnf_transformation,[],[f29])).
% 4.02/0.99  
% 4.02/0.99  fof(f80,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f60])).
% 4.02/0.99  
% 4.02/0.99  fof(f3,axiom,(
% 4.02/0.99    v1_xboole_0(k1_xboole_0)),
% 4.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f72,plain,(
% 4.02/0.99    v1_xboole_0(k1_xboole_0)),
% 4.02/0.99    inference(cnf_transformation,[],[f3])).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3,plain,
% 4.02/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f70]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1825,plain,
% 4.02/0.99      ( r1_tarski(X0,X1) = iProver_top
% 4.02/0.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_40,negated_conjecture,
% 4.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 4.02/0.99      inference(cnf_transformation,[],[f111]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1805,plain,
% 4.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_26,plain,
% 4.02/0.99      ( v5_relat_1(X0,X1)
% 4.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 4.02/0.99      inference(cnf_transformation,[],[f94]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_16,plain,
% 4.02/0.99      ( ~ v5_relat_1(X0,X1)
% 4.02/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 4.02/0.99      | ~ v1_relat_1(X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f82]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_627,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 4.02/0.99      | ~ v1_relat_1(X0) ),
% 4.02/0.99      inference(resolution,[status(thm)],[c_26,c_16]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1795,plain,
% 4.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.02/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 4.02/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2911,plain,
% 4.02/0.99      ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
% 4.02/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1805,c_1795]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4,plain,
% 4.02/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f69]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1824,plain,
% 4.02/0.99      ( r1_tarski(X0,X1) != iProver_top
% 4.02/0.99      | r2_hidden(X2,X0) != iProver_top
% 4.02/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3637,plain,
% 4.02/0.99      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 4.02/0.99      | r2_hidden(X0,sK2) = iProver_top
% 4.02/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2911,c_1824]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3937,plain,
% 4.02/0.99      ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top
% 4.02/0.99      | r2_hidden(sK1(k2_relat_1(sK5),X0),sK2) = iProver_top
% 4.02/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1825,c_3637]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_17,plain,
% 4.02/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f84]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1818,plain,
% 4.02/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_11,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f77]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1819,plain,
% 4.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.02/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2746,plain,
% 4.02/0.99      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK2)) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1805,c_1819]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_12,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.02/0.99      | ~ v1_relat_1(X1)
% 4.02/0.99      | v1_relat_1(X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f79]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_10,plain,
% 4.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f78]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_335,plain,
% 4.02/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 4.02/0.99      inference(prop_impl,[status(thm)],[c_10]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_336,plain,
% 4.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_335]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_417,plain,
% 4.02/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 4.02/0.99      inference(bin_hyper_res,[status(thm)],[c_12,c_336]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1798,plain,
% 4.02/0.99      ( r1_tarski(X0,X1) != iProver_top
% 4.02/0.99      | v1_relat_1(X1) != iProver_top
% 4.02/0.99      | v1_relat_1(X0) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_10214,plain,
% 4.02/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top
% 4.02/0.99      | v1_relat_1(sK5) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2746,c_1798]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_10350,plain,
% 4.02/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1818,c_10214]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_12452,plain,
% 4.02/0.99      ( r2_hidden(sK1(k2_relat_1(sK5),X0),sK2) = iProver_top
% 4.02/0.99      | r1_tarski(k2_relat_1(sK5),X0) = iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_3937,c_10350]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_12453,plain,
% 4.02/0.99      ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top
% 4.02/0.99      | r2_hidden(sK1(k2_relat_1(sK5),X0),sK2) = iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_12452]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2,plain,
% 4.02/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f71]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1826,plain,
% 4.02/0.99      ( r1_tarski(X0,X1) = iProver_top
% 4.02/0.99      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_12459,plain,
% 4.02/0.99      ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_12453,c_1826]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6,plain,
% 4.02/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f75]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1822,plain,
% 4.02/0.99      ( X0 = X1
% 4.02/0.99      | r1_tarski(X1,X0) != iProver_top
% 4.02/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_12469,plain,
% 4.02/0.99      ( k2_relat_1(sK5) = sK2
% 4.02/0.99      | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_12459,c_1822]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_43,negated_conjecture,
% 4.02/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 4.02/0.99      inference(cnf_transformation,[],[f108]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1802,plain,
% 4.02/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_35,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.02/0.99      | ~ v1_funct_1(X0)
% 4.02/0.99      | ~ v1_funct_1(X3)
% 4.02/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f102]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1808,plain,
% 4.02/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 4.02/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 4.02/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.02/0.99      | v1_funct_1(X5) != iProver_top
% 4.02/0.99      | v1_funct_1(X4) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4299,plain,
% 4.02/0.99      ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.02/0.99      | v1_funct_1(X2) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1805,c_1808]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_42,negated_conjecture,
% 4.02/0.99      ( v1_funct_1(sK5) ),
% 4.02/0.99      inference(cnf_transformation,[],[f109]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_49,plain,
% 4.02/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4453,plain,
% 4.02/0.99      ( v1_funct_1(X2) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.02/0.99      | k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5) ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_4299,c_49]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4454,plain,
% 4.02/0.99      ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.02/0.99      | v1_funct_1(X2) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_4453]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4463,plain,
% 4.02/0.99      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
% 4.02/0.99      | v1_funct_1(sK4) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1802,c_4454]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_29,plain,
% 4.02/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 4.02/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.02/0.99      | X3 = X2 ),
% 4.02/0.99      inference(cnf_transformation,[],[f95]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_39,negated_conjecture,
% 4.02/0.99      ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f112]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_588,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/0.99      | X3 = X0
% 4.02/0.99      | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
% 4.02/0.99      | k6_partfun1(sK2) != X3
% 4.02/0.99      | sK2 != X2
% 4.02/0.99      | sK2 != X1 ),
% 4.02/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_39]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_589,plain,
% 4.02/0.99      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 4.02/0.99      | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 4.02/0.99      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 4.02/0.99      inference(unflattening,[status(thm)],[c_588]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_30,plain,
% 4.02/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 4.02/0.99      inference(cnf_transformation,[],[f118]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_597,plain,
% 4.02/0.99      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 4.02/0.99      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 4.02/0.99      inference(forward_subsumption_resolution,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_589,c_30]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1796,plain,
% 4.02/0.99      ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
% 4.02/0.99      | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_45,negated_conjecture,
% 4.02/0.99      ( v1_funct_1(sK4) ),
% 4.02/0.99      inference(cnf_transformation,[],[f106]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_33,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.02/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.02/0.99      | ~ v1_funct_1(X0)
% 4.02/0.99      | ~ v1_funct_1(X3) ),
% 4.02/0.99      inference(cnf_transformation,[],[f101]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1875,plain,
% 4.02/0.99      ( m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 4.02/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 4.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 4.02/0.99      | ~ v1_funct_1(sK4)
% 4.02/0.99      | ~ v1_funct_1(sK5) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_33]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2181,plain,
% 4.02/0.99      ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_1796,c_45,c_43,c_42,c_40,c_597,c_1875]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4464,plain,
% 4.02/0.99      ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2)
% 4.02/0.99      | v1_funct_1(sK4) != iProver_top ),
% 4.02/0.99      inference(light_normalisation,[status(thm)],[c_4463,c_2181]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_46,plain,
% 4.02/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4679,plain,
% 4.02/0.99      ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2) ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_4464,c_46]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_19,plain,
% 4.02/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 4.02/0.99      | ~ v1_relat_1(X0)
% 4.02/0.99      | ~ v1_relat_1(X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f86]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1816,plain,
% 4.02/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 4.02/0.99      | v1_relat_1(X0) != iProver_top
% 4.02/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4681,plain,
% 4.02/0.99      ( r1_tarski(k2_relat_1(k6_partfun1(sK2)),k2_relat_1(sK5)) = iProver_top
% 4.02/0.99      | v1_relat_1(sK4) != iProver_top
% 4.02/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_4679,c_1816]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_22,plain,
% 4.02/0.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f114]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4682,plain,
% 4.02/0.99      ( r1_tarski(sK2,k2_relat_1(sK5)) = iProver_top
% 4.02/0.99      | v1_relat_1(sK4) != iProver_top
% 4.02/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.02/0.99      inference(demodulation,[status(thm)],[c_4681,c_22]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3229,plain,
% 4.02/0.99      ( k2_relat_1(sK5) = sK2
% 4.02/0.99      | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top
% 4.02/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2911,c_1822]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4873,plain,
% 4.02/0.99      ( k2_relat_1(sK5) = sK2
% 4.02/0.99      | v1_relat_1(sK4) != iProver_top
% 4.02/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_4682,c_3229]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2747,plain,
% 4.02/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1802,c_1819]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_10215,plain,
% 4.02/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 4.02/0.99      | v1_relat_1(sK4) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2747,c_1798]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_10353,plain,
% 4.02/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1818,c_10215]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_12598,plain,
% 4.02/0.99      ( k2_relat_1(sK5) = sK2 ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_12469,c_4873,c_10350,c_10353]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_20,plain,
% 4.02/0.99      ( ~ v1_relat_1(X0)
% 4.02/0.99      | k2_relat_1(X0) != k1_xboole_0
% 4.02/0.99      | k1_xboole_0 = X0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f88]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1815,plain,
% 4.02/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 4.02/0.99      | k1_xboole_0 = X0
% 4.02/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_12612,plain,
% 4.02/0.99      ( sK2 != k1_xboole_0
% 4.02/0.99      | sK5 = k1_xboole_0
% 4.02/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_12598,c_1815]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_15,plain,
% 4.02/0.99      ( v5_relat_1(X0,X1)
% 4.02/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 4.02/0.99      | ~ v1_relat_1(X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f83]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_31,plain,
% 4.02/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 4.02/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 4.02/0.99      | ~ v1_relat_1(X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f122]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_38,negated_conjecture,
% 4.02/0.99      ( ~ v2_funct_2(sK5,sK2) | ~ v2_funct_1(sK4) ),
% 4.02/0.99      inference(cnf_transformation,[],[f113]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_606,plain,
% 4.02/0.99      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 4.02/0.99      | ~ v2_funct_1(sK4)
% 4.02/0.99      | ~ v1_relat_1(X0)
% 4.02/0.99      | k2_relat_1(X0) != sK2
% 4.02/0.99      | sK5 != X0 ),
% 4.02/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_38]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_607,plain,
% 4.02/0.99      ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
% 4.02/0.99      | ~ v2_funct_1(sK4)
% 4.02/0.99      | ~ v1_relat_1(sK5)
% 4.02/0.99      | k2_relat_1(sK5) != sK2 ),
% 4.02/0.99      inference(unflattening,[status(thm)],[c_606]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_660,plain,
% 4.02/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 4.02/0.99      | ~ v2_funct_1(sK4)
% 4.02/0.99      | ~ v1_relat_1(X0)
% 4.02/0.99      | ~ v1_relat_1(sK5)
% 4.02/0.99      | k2_relat_1(sK5) != X1
% 4.02/0.99      | k2_relat_1(sK5) != sK2
% 4.02/0.99      | sK5 != X0 ),
% 4.02/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_607]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_661,plain,
% 4.02/0.99      ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
% 4.02/0.99      | ~ v2_funct_1(sK4)
% 4.02/0.99      | ~ v1_relat_1(sK5)
% 4.02/0.99      | k2_relat_1(sK5) != sK2 ),
% 4.02/0.99      inference(unflattening,[status(thm)],[c_660]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_7,plain,
% 4.02/0.99      ( r1_tarski(X0,X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f119]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_671,plain,
% 4.02/0.99      ( ~ v2_funct_1(sK4) | ~ v1_relat_1(sK5) | k2_relat_1(sK5) != sK2 ),
% 4.02/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_661,c_7]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_672,plain,
% 4.02/0.99      ( k2_relat_1(sK5) != sK2
% 4.02/0.99      | v2_funct_1(sK4) != iProver_top
% 4.02/0.99      | v1_relat_1(sK5) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_24,plain,
% 4.02/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f116]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1813,plain,
% 4.02/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_37,plain,
% 4.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.02/0.99      | ~ v1_funct_2(X3,X4,X1)
% 4.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 4.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/0.99      | ~ v1_funct_1(X0)
% 4.02/0.99      | ~ v1_funct_1(X3)
% 4.02/0.99      | v2_funct_1(X3)
% 4.02/0.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 4.02/0.99      | k1_xboole_0 = X2 ),
% 4.02/0.99      inference(cnf_transformation,[],[f104]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1806,plain,
% 4.02/0.99      ( k1_xboole_0 = X0
% 4.02/0.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 4.02/0.99      | v1_funct_2(X3,X4,X2) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 4.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 4.02/0.99      | v1_funct_1(X1) != iProver_top
% 4.02/0.99      | v1_funct_1(X3) != iProver_top
% 4.02/0.99      | v2_funct_1(X3) = iProver_top
% 4.02/0.99      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3513,plain,
% 4.02/0.99      ( sK2 = k1_xboole_0
% 4.02/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 4.02/0.99      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 4.02/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 4.02/0.99      | v1_funct_1(sK4) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top
% 4.02/0.99      | v2_funct_1(k6_partfun1(sK2)) != iProver_top
% 4.02/0.99      | v2_funct_1(sK4) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2181,c_1806]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_44,negated_conjecture,
% 4.02/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 4.02/0.99      inference(cnf_transformation,[],[f107]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_47,plain,
% 4.02/0.99      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_48,plain,
% 4.02/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_41,negated_conjecture,
% 4.02/0.99      ( v1_funct_2(sK5,sK3,sK2) ),
% 4.02/0.99      inference(cnf_transformation,[],[f110]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_50,plain,
% 4.02/0.99      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_51,plain,
% 4.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8019,plain,
% 4.02/0.99      ( sK2 = k1_xboole_0
% 4.02/0.99      | v2_funct_1(k6_partfun1(sK2)) != iProver_top
% 4.02/0.99      | v2_funct_1(sK4) = iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_3513,c_46,c_47,c_48,c_49,c_50,c_51]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8023,plain,
% 4.02/0.99      ( sK2 = k1_xboole_0 | v2_funct_1(sK4) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1813,c_8019]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_13125,plain,
% 4.02/0.99      ( sK5 = k1_xboole_0 ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_12612,c_672,c_4873,c_8023,c_10350,c_10353]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_13132,plain,
% 4.02/0.99      ( k2_relat_1(k1_xboole_0) = sK2 ),
% 4.02/0.99      inference(demodulation,[status(thm)],[c_13125,c_12598]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_23,plain,
% 4.02/0.99      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f115]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_21,plain,
% 4.02/0.99      ( ~ v1_relat_1(X0)
% 4.02/0.99      | k1_relat_1(X0) != k1_xboole_0
% 4.02/0.99      | k1_xboole_0 = X0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f87]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1814,plain,
% 4.02/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 4.02/0.99      | k1_xboole_0 = X0
% 4.02/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3054,plain,
% 4.02/0.99      ( k6_partfun1(X0) = k1_xboole_0
% 4.02/0.99      | k1_xboole_0 != X0
% 4.02/0.99      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_23,c_1814]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_25,plain,
% 4.02/0.99      ( v1_relat_1(k6_partfun1(X0)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f117]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_90,plain,
% 4.02/0.99      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3073,plain,
% 4.02/0.99      ( k1_xboole_0 != X0 | k6_partfun1(X0) = k1_xboole_0 ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_3054,c_90]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3074,plain,
% 4.02/0.99      ( k6_partfun1(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_3073]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3076,plain,
% 4.02/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 4.02/0.99      inference(equality_resolution,[status(thm)],[c_3074]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3082,plain,
% 4.02/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_3076,c_22]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_13191,plain,
% 4.02/0.99      ( sK2 = k1_xboole_0 ),
% 4.02/0.99      inference(light_normalisation,[status(thm)],[c_13132,c_3082]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1,plain,
% 4.02/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f67]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1827,plain,
% 4.02/0.99      ( r2_hidden(X0,X1) != iProver_top
% 4.02/0.99      | v1_xboole_0(X1) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3001,plain,
% 4.02/0.99      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1825,c_1827]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_27,plain,
% 4.02/0.99      ( v4_relat_1(X0,X1)
% 4.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.02/0.99      inference(cnf_transformation,[],[f93]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_14,plain,
% 4.02/0.99      ( ~ v4_relat_1(X0,X1)
% 4.02/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 4.02/0.99      | ~ v1_relat_1(X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f80]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_567,plain,
% 4.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 4.02/0.99      | ~ v1_relat_1(X0) ),
% 4.02/0.99      inference(resolution,[status(thm)],[c_27,c_14]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1797,plain,
% 4.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.02/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 4.02/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3091,plain,
% 4.02/0.99      ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top
% 4.02/0.99      | v1_relat_1(sK4) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1802,c_1797]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3277,plain,
% 4.02/0.99      ( k1_relat_1(sK4) = sK2
% 4.02/0.99      | r1_tarski(sK2,k1_relat_1(sK4)) != iProver_top
% 4.02/0.99      | v1_relat_1(sK4) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_3091,c_1822]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3413,plain,
% 4.02/0.99      ( k1_relat_1(sK4) = sK2
% 4.02/0.99      | v1_relat_1(sK4) != iProver_top
% 4.02/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_3001,c_3277]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_13619,plain,
% 4.02/0.99      ( k1_relat_1(sK4) = k1_xboole_0
% 4.02/0.99      | v1_relat_1(sK4) != iProver_top
% 4.02/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.02/0.99      inference(demodulation,[status(thm)],[c_13191,c_3413]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2651,plain,
% 4.02/0.99      ( ~ v1_relat_1(k6_partfun1(X0))
% 4.02/0.99      | k1_relat_1(k6_partfun1(X0)) != k1_xboole_0
% 4.02/0.99      | k1_xboole_0 = k6_partfun1(X0) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2653,plain,
% 4.02/0.99      ( ~ v1_relat_1(k6_partfun1(k1_xboole_0))
% 4.02/0.99      | k1_relat_1(k6_partfun1(k1_xboole_0)) != k1_xboole_0
% 4.02/0.99      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_2651]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_989,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2165,plain,
% 4.02/0.99      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_989]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2646,plain,
% 4.02/0.99      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_2165]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2647,plain,
% 4.02/0.99      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_2646]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2432,plain,
% 4.02/0.99      ( r1_tarski(sK4,sK4) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1999,plain,
% 4.02/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2140,plain,
% 4.02/0.99      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1999]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2057,plain,
% 4.02/0.99      ( ~ v1_relat_1(sK4)
% 4.02/0.99      | k1_relat_1(sK4) != k1_xboole_0
% 4.02/0.99      | k1_xboole_0 = sK4 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2058,plain,
% 4.02/0.99      ( k1_relat_1(sK4) != k1_xboole_0
% 4.02/0.99      | k1_xboole_0 = sK4
% 4.02/0.99      | v1_relat_1(sK4) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2057]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1000,plain,
% 4.02/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 4.02/0.99      theory(equality) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1942,plain,
% 4.02/0.99      ( v2_funct_1(X0)
% 4.02/0.99      | ~ v2_funct_1(k6_partfun1(X1))
% 4.02/0.99      | X0 != k6_partfun1(X1) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1000]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1943,plain,
% 4.02/0.99      ( X0 != k6_partfun1(X1)
% 4.02/0.99      | v2_funct_1(X0) = iProver_top
% 4.02/0.99      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1942]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1945,plain,
% 4.02/0.99      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 4.02/0.99      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 4.02/0.99      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1943]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1888,plain,
% 4.02/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(sK4) | sK4 != X0 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1000]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1889,plain,
% 4.02/0.99      ( sK4 != X0
% 4.02/0.99      | v2_funct_1(X0) != iProver_top
% 4.02/0.99      | v2_funct_1(sK4) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1888]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1891,plain,
% 4.02/0.99      ( sK4 != k1_xboole_0
% 4.02/0.99      | v2_funct_1(sK4) = iProver_top
% 4.02/0.99      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_1889]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5,plain,
% 4.02/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f72]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_140,plain,
% 4.02/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_96,plain,
% 4.02/0.99      ( k1_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_93,plain,
% 4.02/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_95,plain,
% 4.02/0.99      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_93]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_91,plain,
% 4.02/0.99      ( v1_relat_1(k6_partfun1(k1_xboole_0)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(contradiction,plain,
% 4.02/0.99      ( $false ),
% 4.02/0.99      inference(minisat,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_13619,c_10353,c_10350,c_4873,c_2653,c_2647,c_2432,
% 4.02/0.99                 c_2140,c_2058,c_1945,c_1891,c_672,c_140,c_96,c_95,c_91]) ).
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  ------                               Statistics
% 4.02/0.99  
% 4.02/0.99  ------ General
% 4.02/0.99  
% 4.02/0.99  abstr_ref_over_cycles:                  0
% 4.02/0.99  abstr_ref_under_cycles:                 0
% 4.02/0.99  gc_basic_clause_elim:                   0
% 4.02/0.99  forced_gc_time:                         0
% 4.02/0.99  parsing_time:                           0.01
% 4.02/0.99  unif_index_cands_time:                  0.
% 4.02/0.99  unif_index_add_time:                    0.
% 4.02/0.99  orderings_time:                         0.
% 4.02/0.99  out_proof_time:                         0.017
% 4.02/0.99  total_time:                             0.422
% 4.02/0.99  num_of_symbols:                         57
% 4.02/0.99  num_of_terms:                           14332
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing
% 4.02/0.99  
% 4.02/0.99  num_of_splits:                          0
% 4.02/0.99  num_of_split_atoms:                     0
% 4.02/0.99  num_of_reused_defs:                     0
% 4.02/0.99  num_eq_ax_congr_red:                    21
% 4.02/0.99  num_of_sem_filtered_clauses:            1
% 4.02/0.99  num_of_subtypes:                        0
% 4.02/0.99  monotx_restored_types:                  0
% 4.02/0.99  sat_num_of_epr_types:                   0
% 4.02/0.99  sat_num_of_non_cyclic_types:            0
% 4.02/0.99  sat_guarded_non_collapsed_types:        0
% 4.02/0.99  num_pure_diseq_elim:                    0
% 4.02/0.99  simp_replaced_by:                       0
% 4.02/0.99  res_preprocessed:                       189
% 4.02/0.99  prep_upred:                             0
% 4.02/0.99  prep_unflattend:                        15
% 4.02/0.99  smt_new_axioms:                         0
% 4.02/0.99  pred_elim_cands:                        8
% 4.02/0.99  pred_elim:                              4
% 4.02/0.99  pred_elim_cl:                           8
% 4.02/0.99  pred_elim_cycles:                       6
% 4.02/0.99  merged_defs:                            8
% 4.02/0.99  merged_defs_ncl:                        0
% 4.02/0.99  bin_hyper_res:                          10
% 4.02/0.99  prep_cycles:                            4
% 4.02/0.99  pred_elim_time:                         0.006
% 4.02/0.99  splitting_time:                         0.
% 4.02/0.99  sem_filter_time:                        0.
% 4.02/0.99  monotx_time:                            0.001
% 4.02/0.99  subtype_inf_time:                       0.
% 4.02/0.99  
% 4.02/0.99  ------ Problem properties
% 4.02/0.99  
% 4.02/0.99  clauses:                                37
% 4.02/0.99  conjectures:                            6
% 4.02/0.99  epr:                                    11
% 4.02/0.99  horn:                                   34
% 4.02/0.99  ground:                                 9
% 4.02/0.99  unary:                                  14
% 4.02/0.99  binary:                                 7
% 4.02/0.99  lits:                                   93
% 4.02/0.99  lits_eq:                                11
% 4.02/0.99  fd_pure:                                0
% 4.02/0.99  fd_pseudo:                              0
% 4.02/0.99  fd_cond:                                3
% 4.02/0.99  fd_pseudo_cond:                         1
% 4.02/0.99  ac_symbols:                             0
% 4.02/0.99  
% 4.02/0.99  ------ Propositional Solver
% 4.02/0.99  
% 4.02/0.99  prop_solver_calls:                      32
% 4.02/0.99  prop_fast_solver_calls:                 1543
% 4.02/0.99  smt_solver_calls:                       0
% 4.02/0.99  smt_fast_solver_calls:                  0
% 4.02/0.99  prop_num_of_clauses:                    6365
% 4.02/0.99  prop_preprocess_simplified:             13684
% 4.02/0.99  prop_fo_subsumed:                       80
% 4.02/0.99  prop_solver_time:                       0.
% 4.02/0.99  smt_solver_time:                        0.
% 4.02/0.99  smt_fast_solver_time:                   0.
% 4.02/0.99  prop_fast_solver_time:                  0.
% 4.02/0.99  prop_unsat_core_time:                   0.
% 4.02/0.99  
% 4.02/0.99  ------ QBF
% 4.02/0.99  
% 4.02/0.99  qbf_q_res:                              0
% 4.02/0.99  qbf_num_tautologies:                    0
% 4.02/0.99  qbf_prep_cycles:                        0
% 4.02/0.99  
% 4.02/0.99  ------ BMC1
% 4.02/0.99  
% 4.02/0.99  bmc1_current_bound:                     -1
% 4.02/0.99  bmc1_last_solved_bound:                 -1
% 4.02/0.99  bmc1_unsat_core_size:                   -1
% 4.02/0.99  bmc1_unsat_core_parents_size:           -1
% 4.02/0.99  bmc1_merge_next_fun:                    0
% 4.02/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation
% 4.02/0.99  
% 4.02/0.99  inst_num_of_clauses:                    1607
% 4.02/0.99  inst_num_in_passive:                    712
% 4.02/0.99  inst_num_in_active:                     704
% 4.02/0.99  inst_num_in_unprocessed:                191
% 4.02/0.99  inst_num_of_loops:                      940
% 4.02/0.99  inst_num_of_learning_restarts:          0
% 4.02/0.99  inst_num_moves_active_passive:          231
% 4.02/0.99  inst_lit_activity:                      0
% 4.02/0.99  inst_lit_activity_moves:                0
% 4.02/0.99  inst_num_tautologies:                   0
% 4.02/0.99  inst_num_prop_implied:                  0
% 4.02/0.99  inst_num_existing_simplified:           0
% 4.02/0.99  inst_num_eq_res_simplified:             0
% 4.02/0.99  inst_num_child_elim:                    0
% 4.02/0.99  inst_num_of_dismatching_blockings:      485
% 4.02/0.99  inst_num_of_non_proper_insts:           2007
% 4.02/0.99  inst_num_of_duplicates:                 0
% 4.02/0.99  inst_inst_num_from_inst_to_res:         0
% 4.02/0.99  inst_dismatching_checking_time:         0.
% 4.02/0.99  
% 4.02/0.99  ------ Resolution
% 4.02/0.99  
% 4.02/0.99  res_num_of_clauses:                     0
% 4.02/0.99  res_num_in_passive:                     0
% 4.02/0.99  res_num_in_active:                      0
% 4.02/0.99  res_num_of_loops:                       193
% 4.02/0.99  res_forward_subset_subsumed:            178
% 4.02/0.99  res_backward_subset_subsumed:           0
% 4.02/0.99  res_forward_subsumed:                   0
% 4.02/0.99  res_backward_subsumed:                  1
% 4.02/0.99  res_forward_subsumption_resolution:     2
% 4.02/0.99  res_backward_subsumption_resolution:    0
% 4.02/0.99  res_clause_to_clause_subsumption:       996
% 4.02/0.99  res_orphan_elimination:                 0
% 4.02/0.99  res_tautology_del:                      95
% 4.02/0.99  res_num_eq_res_simplified:              0
% 4.02/0.99  res_num_sel_changes:                    0
% 4.02/0.99  res_moves_from_active_to_pass:          0
% 4.02/0.99  
% 4.02/0.99  ------ Superposition
% 4.02/0.99  
% 4.02/0.99  sup_time_total:                         0.
% 4.02/0.99  sup_time_generating:                    0.
% 4.02/0.99  sup_time_sim_full:                      0.
% 4.02/0.99  sup_time_sim_immed:                     0.
% 4.02/0.99  
% 4.02/0.99  sup_num_of_clauses:                     322
% 4.02/0.99  sup_num_in_active:                      73
% 4.02/0.99  sup_num_in_passive:                     249
% 4.02/0.99  sup_num_of_loops:                       186
% 4.02/0.99  sup_fw_superposition:                   236
% 4.02/0.99  sup_bw_superposition:                   187
% 4.02/0.99  sup_immediate_simplified:               108
% 4.02/0.99  sup_given_eliminated:                   0
% 4.02/0.99  comparisons_done:                       0
% 4.02/0.99  comparisons_avoided:                    0
% 4.02/0.99  
% 4.02/0.99  ------ Simplifications
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  sim_fw_subset_subsumed:                 12
% 4.02/0.99  sim_bw_subset_subsumed:                 14
% 4.02/0.99  sim_fw_subsumed:                        19
% 4.02/0.99  sim_bw_subsumed:                        7
% 4.02/0.99  sim_fw_subsumption_res:                 0
% 4.02/0.99  sim_bw_subsumption_res:                 0
% 4.02/0.99  sim_tautology_del:                      8
% 4.02/0.99  sim_eq_tautology_del:                   9
% 4.02/0.99  sim_eq_res_simp:                        1
% 4.02/0.99  sim_fw_demodulated:                     4
% 4.02/0.99  sim_bw_demodulated:                     135
% 4.02/0.99  sim_light_normalised:                   46
% 4.02/0.99  sim_joinable_taut:                      0
% 4.02/0.99  sim_joinable_simp:                      0
% 4.02/0.99  sim_ac_normalised:                      0
% 4.02/0.99  sim_smt_subsumption:                    0
% 4.02/0.99  
%------------------------------------------------------------------------------
