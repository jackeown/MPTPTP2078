%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:08 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  287 (2357 expanded)
%              Number of clauses        :  183 ( 770 expanded)
%              Number of leaves         :   31 ( 547 expanded)
%              Depth                    :   21
%              Number of atoms          :  842 (12124 expanded)
%              Number of equality atoms :  301 (1203 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f56])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f57,f58])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f118,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f97,f103])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f53,f54])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f25,conjecture,(
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

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f67,plain,(
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

fof(f66,plain,
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

fof(f68,plain,
    ( ( ~ v2_funct_2(sK5,sK2)
      | ~ v2_funct_1(sK4) )
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & v1_funct_2(sK5,sK3,sK2)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f51,f67,f66])).

fof(f111,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f68])).

fof(f106,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f107,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

fof(f108,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f68])).

fof(f109,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f110,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f16,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f116,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f93,f103])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f60])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f120,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f112,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f68])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f122,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f99])).

fof(f113,plain,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f119,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f24,axiom,(
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

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

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
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f114,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f91,f103])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1781,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1785,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_28,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1772,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1778,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2701,plain,
    ( r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1772,c_1778])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1784,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3590,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X1)) = iProver_top
    | r2_hidden(X0,k6_partfun1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2701,c_1784])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1787,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8621,plain,
    ( r2_hidden(X0,k6_partfun1(X1)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3590,c_1787])).

cnf(c_10469,plain,
    ( r1_tarski(k6_partfun1(X0),X1) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_8621])).

cnf(c_10875,plain,
    ( r1_tarski(k6_partfun1(X0),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_10469])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1780,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1766,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2702,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_1778])).

cnf(c_3591,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK3,sK2)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2702,c_1784])).

cnf(c_3830,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3591,c_1787])).

cnf(c_4774,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_3830])).

cnf(c_5571,plain,
    ( r1_tarski(sK5,X0) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_4774])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_74,plain,
    ( m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_23,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_89,plain,
    ( v2_funct_1(k6_partfun1(sK2)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_127,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_126,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_128,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_131,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_546,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_547,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_548,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_550,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_27,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_37,negated_conjecture,
    ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
    | k6_partfun1(sK2) != X3
    | sK2 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_37])).

cnf(c_564,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_29,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_36,negated_conjecture,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_582,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_36])).

cnf(c_583,plain,
    ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_636,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != X1
    | k2_relat_1(sK5) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_583])).

cnf(c_637,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_647,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_637,c_6])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1834,plain,
    ( m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_35,plain,
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

cnf(c_1842,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK4,X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(k1_partfun1(X3,X1,X1,X2,sK4,X0))
    | v2_funct_1(sK4)
    | k1_xboole_0 = X2 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_1891,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ v1_funct_2(sK5,X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,sK4,sK5))
    | v2_funct_1(sK4)
    | k1_xboole_0 = X2 ),
    inference(instantiation,[status(thm)],[c_1842])).

cnf(c_2029,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_2(sK5,sK3,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v2_funct_1(k1_partfun1(sK2,sK3,sK3,X0,sK4,sK5))
    | v2_funct_1(sK4)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_1891])).

cnf(c_2031,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v2_funct_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
    | v2_funct_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2029])).

cnf(c_961,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2008,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_2397,plain,
    ( X0 != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | X0 = k6_partfun1(sK2)
    | k6_partfun1(sK2) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2008])).

cnf(c_2449,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2)
    | k6_partfun1(sK2) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2397])).

cnf(c_960,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2824,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_960])).

cnf(c_25,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_25,c_17])).

cnf(c_1756,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_2711,plain,
    ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_1756])).

cnf(c_1783,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3468,plain,
    ( k2_relat_1(sK5) = sK2
    | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2711,c_1783])).

cnf(c_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1777,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_322,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_323,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_322])).

cnf(c_401,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_15,c_323])).

cnf(c_1759,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_3386,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2702,c_1759])).

cnf(c_3646,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_3386])).

cnf(c_3647,plain,
    ( v1_relat_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3646])).

cnf(c_1763,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_2703,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1763,c_1778])).

cnf(c_3387,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2703,c_1759])).

cnf(c_3649,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_3387])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1769,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4294,plain,
    ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_1769])).

cnf(c_47,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4307,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4294,c_47])).

cnf(c_4308,plain,
    ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4307])).

cnf(c_4316,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1763,c_4308])).

cnf(c_566,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_564,c_74])).

cnf(c_1757,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_566])).

cnf(c_2118,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1757,c_43,c_41,c_40,c_38,c_74,c_564,c_1834])).

cnf(c_4317,plain,
    ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2)
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4316,c_2118])).

cnf(c_44,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_4586,plain,
    ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4317,c_44])).

cnf(c_20,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1775,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4588,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK2)),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4586,c_1775])).

cnf(c_21,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_4589,plain,
    ( r1_tarski(sK2,k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4588,c_21])).

cnf(c_972,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1913,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_4697,plain,
    ( v2_funct_1(k1_partfun1(sK2,sK3,sK3,X0,sK4,sK5))
    | ~ v2_funct_1(k6_partfun1(X1))
    | k1_partfun1(sK2,sK3,sK3,X0,sK4,sK5) != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_1913])).

cnf(c_4699,plain,
    ( v2_funct_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
    | ~ v2_funct_1(k6_partfun1(sK2))
    | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != k6_partfun1(sK2) ),
    inference(instantiation,[status(thm)],[c_4697])).

cnf(c_4773,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_3830])).

cnf(c_5313,plain,
    ( r1_tarski(sK5,X0) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_4773])).

cnf(c_964,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5657,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_5658,plain,
    ( X0 != X1
    | k1_xboole_0 != X2
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5657])).

cnf(c_5660,plain,
    ( sK2 != sK2
    | k1_xboole_0 != sK2
    | r1_tarski(sK2,sK2) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5658])).

cnf(c_7980,plain,
    ( r1_tarski(sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5571,c_43,c_42,c_41,c_40,c_39,c_38,c_74,c_89,c_127,c_128,c_131,c_550,c_564,c_647,c_1834,c_2031,c_2449,c_2824,c_3468,c_3646,c_3647,c_3649,c_4589,c_4699,c_5313,c_5660])).

cnf(c_7987,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7980,c_1783])).

cnf(c_12205,plain,
    ( k6_partfun1(X0) = sK5
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10875,c_7987])).

cnf(c_12215,plain,
    ( k6_partfun1(sK2) = sK5
    | v1_xboole_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12205])).

cnf(c_2995,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_1787])).

cnf(c_3467,plain,
    ( k2_zfmisc_1(sK2,sK3) = sK4
    | r1_tarski(k2_zfmisc_1(sK2,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2703,c_1783])).

cnf(c_3712,plain,
    ( k2_zfmisc_1(sK2,sK3) = sK4
    | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2995,c_3467])).

cnf(c_1767,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3396,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(k6_partfun1(sK2)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2118,c_1767])).

cnf(c_45,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_46,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_48,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_49,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_88,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_90,plain,
    ( v2_funct_1(k6_partfun1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_648,plain,
    ( k2_relat_1(sK5) != sK2
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_6630,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3396,c_44,c_45,c_46,c_47,c_48,c_49,c_90,c_648,c_3468,c_3646,c_3649,c_4589])).

cnf(c_9467,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) = sK4
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3712,c_6630])).

cnf(c_9469,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) = sK4
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_9467])).

cnf(c_1782,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1758,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_2395,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1782,c_1758])).

cnf(c_9470,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) = sK4
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_9467])).

cnf(c_9555,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9469,c_2395,c_9470])).

cnf(c_9567,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9555,c_1780])).

cnf(c_8321,plain,
    ( ~ r2_hidden(sK1(X0,sK5),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8323,plain,
    ( ~ r2_hidden(sK1(sK2,sK5),sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_8321])).

cnf(c_1906,plain,
    ( k6_partfun1(X0) != X1
    | sK4 != X1
    | sK4 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_8119,plain,
    ( k6_partfun1(X0) != sK5
    | sK4 = k6_partfun1(X0)
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_1906])).

cnf(c_8120,plain,
    ( k6_partfun1(sK2) != sK5
    | sK4 = k6_partfun1(sK2)
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_8119])).

cnf(c_7966,plain,
    ( ~ r2_hidden(sK1(sK4,X0),sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7967,plain,
    ( r2_hidden(sK1(sK4,X0),sK4) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7966])).

cnf(c_7969,plain,
    ( r2_hidden(sK1(sK4,sK2),sK4) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7967])).

cnf(c_5659,plain,
    ( ~ r1_tarski(sK2,sK2)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_5657])).

cnf(c_5315,plain,
    ( r1_tarski(sK5,X0)
    | ~ v1_xboole_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5313])).

cnf(c_5317,plain,
    ( r1_tarski(sK5,sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5315])).

cnf(c_4355,plain,
    ( ~ r2_hidden(sK1(X0,sK4),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4356,plain,
    ( r2_hidden(sK1(X0,sK4),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4355])).

cnf(c_4358,plain,
    ( r2_hidden(sK1(sK2,sK4),sK2) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4356])).

cnf(c_2143,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_4166,plain,
    ( sK4 != X0
    | sK4 = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2143])).

cnf(c_4171,plain,
    ( sK4 != sK2
    | sK4 = sK5
    | sK5 != sK2 ),
    inference(instantiation,[status(thm)],[c_4166])).

cnf(c_2877,plain,
    ( r1_tarski(sK4,X0)
    | r2_hidden(sK1(sK4,X0),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2883,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | r2_hidden(sK1(sK4,X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2877])).

cnf(c_2885,plain,
    ( r1_tarski(sK4,sK2) = iProver_top
    | r2_hidden(sK1(sK4,sK2),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2883])).

cnf(c_2279,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2281,plain,
    ( ~ r1_tarski(sK2,sK5)
    | ~ r1_tarski(sK5,sK2)
    | sK5 = sK2 ),
    inference(instantiation,[status(thm)],[c_2279])).

cnf(c_2249,plain,
    ( r1_tarski(X0,sK4)
    | r2_hidden(sK1(X0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2255,plain,
    ( r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(sK1(X0,sK4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2249])).

cnf(c_2257,plain,
    ( r1_tarski(sK2,sK4) = iProver_top
    | r2_hidden(sK1(sK2,sK4),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2255])).

cnf(c_2221,plain,
    ( r1_tarski(X0,sK5)
    | r2_hidden(sK1(X0,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2228,plain,
    ( r1_tarski(sK2,sK5)
    | r2_hidden(sK1(sK2,sK5),sK2) ),
    inference(instantiation,[status(thm)],[c_2221])).

cnf(c_2070,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2071,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2070])).

cnf(c_2073,plain,
    ( sK4 = sK2
    | r1_tarski(sK4,sK2) != iProver_top
    | r1_tarski(sK2,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2071])).

cnf(c_1852,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_1859,plain,
    ( ~ v2_funct_1(k6_partfun1(X0))
    | v2_funct_1(sK4)
    | sK4 != k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_1852])).

cnf(c_1860,plain,
    ( sK4 != k6_partfun1(X0)
    | v2_funct_1(k6_partfun1(X0)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1859])).

cnf(c_1862,plain,
    ( sK4 != k6_partfun1(sK2)
    | v2_funct_1(k6_partfun1(sK2)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1860])).

cnf(c_549,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12215,c_9567,c_8323,c_8120,c_7969,c_5660,c_5659,c_5317,c_4699,c_4589,c_4358,c_4171,c_3649,c_3647,c_3646,c_3468,c_2885,c_2824,c_2449,c_2395,c_2281,c_2257,c_2228,c_2073,c_2031,c_1862,c_1834,c_648,c_647,c_564,c_550,c_549,c_131,c_128,c_127,c_90,c_89,c_74,c_38,c_39,c_40,c_41,c_42,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:32:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.59/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/0.98  
% 3.59/0.98  ------  iProver source info
% 3.59/0.98  
% 3.59/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.59/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/0.98  git: non_committed_changes: false
% 3.59/0.98  git: last_make_outside_of_git: false
% 3.59/0.98  
% 3.59/0.98  ------ 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options
% 3.59/0.98  
% 3.59/0.98  --out_options                           all
% 3.59/0.98  --tptp_safe_out                         true
% 3.59/0.98  --problem_path                          ""
% 3.59/0.98  --include_path                          ""
% 3.59/0.98  --clausifier                            res/vclausify_rel
% 3.59/0.98  --clausifier_options                    ""
% 3.59/0.98  --stdin                                 false
% 3.59/0.98  --stats_out                             all
% 3.59/0.98  
% 3.59/0.98  ------ General Options
% 3.59/0.98  
% 3.59/0.98  --fof                                   false
% 3.59/0.98  --time_out_real                         305.
% 3.59/0.98  --time_out_virtual                      -1.
% 3.59/0.98  --symbol_type_check                     false
% 3.59/0.98  --clausify_out                          false
% 3.59/0.98  --sig_cnt_out                           false
% 3.59/0.98  --trig_cnt_out                          false
% 3.59/0.98  --trig_cnt_out_tolerance                1.
% 3.59/0.98  --trig_cnt_out_sk_spl                   false
% 3.59/0.98  --abstr_cl_out                          false
% 3.59/0.98  
% 3.59/0.98  ------ Global Options
% 3.59/0.98  
% 3.59/0.98  --schedule                              default
% 3.59/0.98  --add_important_lit                     false
% 3.59/0.98  --prop_solver_per_cl                    1000
% 3.59/0.98  --min_unsat_core                        false
% 3.59/0.98  --soft_assumptions                      false
% 3.59/0.98  --soft_lemma_size                       3
% 3.59/0.98  --prop_impl_unit_size                   0
% 3.59/0.98  --prop_impl_unit                        []
% 3.59/0.98  --share_sel_clauses                     true
% 3.59/0.98  --reset_solvers                         false
% 3.59/0.98  --bc_imp_inh                            [conj_cone]
% 3.59/0.98  --conj_cone_tolerance                   3.
% 3.59/0.98  --extra_neg_conj                        none
% 3.59/0.98  --large_theory_mode                     true
% 3.59/0.98  --prolific_symb_bound                   200
% 3.59/0.98  --lt_threshold                          2000
% 3.59/0.98  --clause_weak_htbl                      true
% 3.59/0.98  --gc_record_bc_elim                     false
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing Options
% 3.59/0.98  
% 3.59/0.98  --preprocessing_flag                    true
% 3.59/0.98  --time_out_prep_mult                    0.1
% 3.59/0.98  --splitting_mode                        input
% 3.59/0.98  --splitting_grd                         true
% 3.59/0.98  --splitting_cvd                         false
% 3.59/0.98  --splitting_cvd_svl                     false
% 3.59/0.98  --splitting_nvd                         32
% 3.59/0.98  --sub_typing                            true
% 3.59/0.98  --prep_gs_sim                           true
% 3.59/0.98  --prep_unflatten                        true
% 3.59/0.98  --prep_res_sim                          true
% 3.59/0.98  --prep_upred                            true
% 3.59/0.98  --prep_sem_filter                       exhaustive
% 3.59/0.98  --prep_sem_filter_out                   false
% 3.59/0.98  --pred_elim                             true
% 3.59/0.98  --res_sim_input                         true
% 3.59/0.98  --eq_ax_congr_red                       true
% 3.59/0.98  --pure_diseq_elim                       true
% 3.59/0.98  --brand_transform                       false
% 3.59/0.98  --non_eq_to_eq                          false
% 3.59/0.98  --prep_def_merge                        true
% 3.59/0.98  --prep_def_merge_prop_impl              false
% 3.59/0.98  --prep_def_merge_mbd                    true
% 3.59/0.98  --prep_def_merge_tr_red                 false
% 3.59/0.98  --prep_def_merge_tr_cl                  false
% 3.59/0.98  --smt_preprocessing                     true
% 3.59/0.98  --smt_ac_axioms                         fast
% 3.59/0.98  --preprocessed_out                      false
% 3.59/0.98  --preprocessed_stats                    false
% 3.59/0.98  
% 3.59/0.98  ------ Abstraction refinement Options
% 3.59/0.98  
% 3.59/0.98  --abstr_ref                             []
% 3.59/0.98  --abstr_ref_prep                        false
% 3.59/0.98  --abstr_ref_until_sat                   false
% 3.59/0.98  --abstr_ref_sig_restrict                funpre
% 3.59/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/0.98  --abstr_ref_under                       []
% 3.59/0.98  
% 3.59/0.98  ------ SAT Options
% 3.59/0.98  
% 3.59/0.98  --sat_mode                              false
% 3.59/0.98  --sat_fm_restart_options                ""
% 3.59/0.98  --sat_gr_def                            false
% 3.59/0.98  --sat_epr_types                         true
% 3.59/0.98  --sat_non_cyclic_types                  false
% 3.59/0.98  --sat_finite_models                     false
% 3.59/0.98  --sat_fm_lemmas                         false
% 3.59/0.98  --sat_fm_prep                           false
% 3.59/0.98  --sat_fm_uc_incr                        true
% 3.59/0.98  --sat_out_model                         small
% 3.59/0.98  --sat_out_clauses                       false
% 3.59/0.98  
% 3.59/0.98  ------ QBF Options
% 3.59/0.98  
% 3.59/0.98  --qbf_mode                              false
% 3.59/0.98  --qbf_elim_univ                         false
% 3.59/0.98  --qbf_dom_inst                          none
% 3.59/0.98  --qbf_dom_pre_inst                      false
% 3.59/0.98  --qbf_sk_in                             false
% 3.59/0.98  --qbf_pred_elim                         true
% 3.59/0.98  --qbf_split                             512
% 3.59/0.98  
% 3.59/0.98  ------ BMC1 Options
% 3.59/0.98  
% 3.59/0.98  --bmc1_incremental                      false
% 3.59/0.98  --bmc1_axioms                           reachable_all
% 3.59/0.98  --bmc1_min_bound                        0
% 3.59/0.98  --bmc1_max_bound                        -1
% 3.59/0.98  --bmc1_max_bound_default                -1
% 3.59/0.98  --bmc1_symbol_reachability              true
% 3.59/0.98  --bmc1_property_lemmas                  false
% 3.59/0.98  --bmc1_k_induction                      false
% 3.59/0.98  --bmc1_non_equiv_states                 false
% 3.59/0.98  --bmc1_deadlock                         false
% 3.59/0.98  --bmc1_ucm                              false
% 3.59/0.98  --bmc1_add_unsat_core                   none
% 3.59/0.98  --bmc1_unsat_core_children              false
% 3.59/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/0.98  --bmc1_out_stat                         full
% 3.59/0.98  --bmc1_ground_init                      false
% 3.59/0.98  --bmc1_pre_inst_next_state              false
% 3.59/0.98  --bmc1_pre_inst_state                   false
% 3.59/0.98  --bmc1_pre_inst_reach_state             false
% 3.59/0.98  --bmc1_out_unsat_core                   false
% 3.59/0.98  --bmc1_aig_witness_out                  false
% 3.59/0.98  --bmc1_verbose                          false
% 3.59/0.98  --bmc1_dump_clauses_tptp                false
% 3.59/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.59/0.98  --bmc1_dump_file                        -
% 3.59/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.59/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.59/0.98  --bmc1_ucm_extend_mode                  1
% 3.59/0.98  --bmc1_ucm_init_mode                    2
% 3.59/0.98  --bmc1_ucm_cone_mode                    none
% 3.59/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.59/0.98  --bmc1_ucm_relax_model                  4
% 3.59/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.59/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/0.98  --bmc1_ucm_layered_model                none
% 3.59/0.98  --bmc1_ucm_max_lemma_size               10
% 3.59/0.98  
% 3.59/0.98  ------ AIG Options
% 3.59/0.98  
% 3.59/0.98  --aig_mode                              false
% 3.59/0.98  
% 3.59/0.98  ------ Instantiation Options
% 3.59/0.98  
% 3.59/0.98  --instantiation_flag                    true
% 3.59/0.98  --inst_sos_flag                         true
% 3.59/0.98  --inst_sos_phase                        true
% 3.59/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel_side                     num_symb
% 3.59/0.98  --inst_solver_per_active                1400
% 3.59/0.98  --inst_solver_calls_frac                1.
% 3.59/0.98  --inst_passive_queue_type               priority_queues
% 3.59/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/0.98  --inst_passive_queues_freq              [25;2]
% 3.59/0.98  --inst_dismatching                      true
% 3.59/0.98  --inst_eager_unprocessed_to_passive     true
% 3.59/0.98  --inst_prop_sim_given                   true
% 3.59/0.98  --inst_prop_sim_new                     false
% 3.59/0.98  --inst_subs_new                         false
% 3.59/0.98  --inst_eq_res_simp                      false
% 3.59/0.98  --inst_subs_given                       false
% 3.59/0.98  --inst_orphan_elimination               true
% 3.59/0.98  --inst_learning_loop_flag               true
% 3.59/0.98  --inst_learning_start                   3000
% 3.59/0.98  --inst_learning_factor                  2
% 3.59/0.98  --inst_start_prop_sim_after_learn       3
% 3.59/0.98  --inst_sel_renew                        solver
% 3.59/0.98  --inst_lit_activity_flag                true
% 3.59/0.98  --inst_restr_to_given                   false
% 3.59/0.98  --inst_activity_threshold               500
% 3.59/0.98  --inst_out_proof                        true
% 3.59/0.98  
% 3.59/0.98  ------ Resolution Options
% 3.59/0.98  
% 3.59/0.98  --resolution_flag                       true
% 3.59/0.98  --res_lit_sel                           adaptive
% 3.59/0.98  --res_lit_sel_side                      none
% 3.59/0.98  --res_ordering                          kbo
% 3.59/0.98  --res_to_prop_solver                    active
% 3.59/0.98  --res_prop_simpl_new                    false
% 3.59/0.98  --res_prop_simpl_given                  true
% 3.59/0.98  --res_passive_queue_type                priority_queues
% 3.59/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/0.98  --res_passive_queues_freq               [15;5]
% 3.59/0.98  --res_forward_subs                      full
% 3.59/0.98  --res_backward_subs                     full
% 3.59/0.98  --res_forward_subs_resolution           true
% 3.59/0.98  --res_backward_subs_resolution          true
% 3.59/0.98  --res_orphan_elimination                true
% 3.59/0.98  --res_time_limit                        2.
% 3.59/0.98  --res_out_proof                         true
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Options
% 3.59/0.98  
% 3.59/0.98  --superposition_flag                    true
% 3.59/0.98  --sup_passive_queue_type                priority_queues
% 3.59/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.59/0.98  --demod_completeness_check              fast
% 3.59/0.98  --demod_use_ground                      true
% 3.59/0.98  --sup_to_prop_solver                    passive
% 3.59/0.98  --sup_prop_simpl_new                    true
% 3.59/0.98  --sup_prop_simpl_given                  true
% 3.59/0.98  --sup_fun_splitting                     true
% 3.59/0.98  --sup_smt_interval                      50000
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Simplification Setup
% 3.59/0.98  
% 3.59/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.59/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.59/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.59/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.59/0.98  --sup_immed_triv                        [TrivRules]
% 3.59/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_bw_main                     []
% 3.59/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.59/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_input_bw                          []
% 3.59/0.98  
% 3.59/0.98  ------ Combination Options
% 3.59/0.98  
% 3.59/0.98  --comb_res_mult                         3
% 3.59/0.98  --comb_sup_mult                         2
% 3.59/0.98  --comb_inst_mult                        10
% 3.59/0.98  
% 3.59/0.98  ------ Debug Options
% 3.59/0.98  
% 3.59/0.98  --dbg_backtrace                         false
% 3.59/0.98  --dbg_dump_prop_clauses                 false
% 3.59/0.98  --dbg_dump_prop_clauses_file            -
% 3.59/0.98  --dbg_out_stat                          false
% 3.59/0.98  ------ Parsing...
% 3.59/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/0.98  ------ Proving...
% 3.59/0.98  ------ Problem Properties 
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  clauses                                 36
% 3.59/0.98  conjectures                             6
% 3.59/0.98  EPR                                     11
% 3.59/0.98  Horn                                    33
% 3.59/0.98  unary                                   13
% 3.59/0.98  binary                                  10
% 3.59/0.98  lits                                    89
% 3.59/0.98  lits eq                                 7
% 3.59/0.98  fd_pure                                 0
% 3.59/0.98  fd_pseudo                               0
% 3.59/0.98  fd_cond                                 1
% 3.59/0.98  fd_pseudo_cond                          1
% 3.59/0.98  AC symbols                              0
% 3.59/0.98  
% 3.59/0.98  ------ Schedule dynamic 5 is on 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  ------ 
% 3.59/0.98  Current options:
% 3.59/0.98  ------ 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options
% 3.59/0.98  
% 3.59/0.98  --out_options                           all
% 3.59/0.98  --tptp_safe_out                         true
% 3.59/0.98  --problem_path                          ""
% 3.59/0.98  --include_path                          ""
% 3.59/0.98  --clausifier                            res/vclausify_rel
% 3.59/0.98  --clausifier_options                    ""
% 3.59/0.98  --stdin                                 false
% 3.59/0.98  --stats_out                             all
% 3.59/0.98  
% 3.59/0.98  ------ General Options
% 3.59/0.98  
% 3.59/0.98  --fof                                   false
% 3.59/0.98  --time_out_real                         305.
% 3.59/0.98  --time_out_virtual                      -1.
% 3.59/0.98  --symbol_type_check                     false
% 3.59/0.98  --clausify_out                          false
% 3.59/0.98  --sig_cnt_out                           false
% 3.59/0.98  --trig_cnt_out                          false
% 3.59/0.98  --trig_cnt_out_tolerance                1.
% 3.59/0.98  --trig_cnt_out_sk_spl                   false
% 3.59/0.98  --abstr_cl_out                          false
% 3.59/0.98  
% 3.59/0.98  ------ Global Options
% 3.59/0.98  
% 3.59/0.98  --schedule                              default
% 3.59/0.98  --add_important_lit                     false
% 3.59/0.98  --prop_solver_per_cl                    1000
% 3.59/0.98  --min_unsat_core                        false
% 3.59/0.98  --soft_assumptions                      false
% 3.59/0.98  --soft_lemma_size                       3
% 3.59/0.98  --prop_impl_unit_size                   0
% 3.59/0.98  --prop_impl_unit                        []
% 3.59/0.98  --share_sel_clauses                     true
% 3.59/0.98  --reset_solvers                         false
% 3.59/0.98  --bc_imp_inh                            [conj_cone]
% 3.59/0.98  --conj_cone_tolerance                   3.
% 3.59/0.98  --extra_neg_conj                        none
% 3.59/0.98  --large_theory_mode                     true
% 3.59/0.98  --prolific_symb_bound                   200
% 3.59/0.98  --lt_threshold                          2000
% 3.59/0.98  --clause_weak_htbl                      true
% 3.59/0.98  --gc_record_bc_elim                     false
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing Options
% 3.59/0.98  
% 3.59/0.98  --preprocessing_flag                    true
% 3.59/0.98  --time_out_prep_mult                    0.1
% 3.59/0.98  --splitting_mode                        input
% 3.59/0.98  --splitting_grd                         true
% 3.59/0.98  --splitting_cvd                         false
% 3.59/0.98  --splitting_cvd_svl                     false
% 3.59/0.98  --splitting_nvd                         32
% 3.59/0.98  --sub_typing                            true
% 3.59/0.98  --prep_gs_sim                           true
% 3.59/0.98  --prep_unflatten                        true
% 3.59/0.98  --prep_res_sim                          true
% 3.59/0.98  --prep_upred                            true
% 3.59/0.98  --prep_sem_filter                       exhaustive
% 3.59/0.98  --prep_sem_filter_out                   false
% 3.59/0.98  --pred_elim                             true
% 3.59/0.98  --res_sim_input                         true
% 3.59/0.98  --eq_ax_congr_red                       true
% 3.59/0.98  --pure_diseq_elim                       true
% 3.59/0.98  --brand_transform                       false
% 3.59/0.98  --non_eq_to_eq                          false
% 3.59/0.98  --prep_def_merge                        true
% 3.59/0.98  --prep_def_merge_prop_impl              false
% 3.59/0.98  --prep_def_merge_mbd                    true
% 3.59/0.98  --prep_def_merge_tr_red                 false
% 3.59/0.98  --prep_def_merge_tr_cl                  false
% 3.59/0.98  --smt_preprocessing                     true
% 3.59/0.98  --smt_ac_axioms                         fast
% 3.59/0.98  --preprocessed_out                      false
% 3.59/0.98  --preprocessed_stats                    false
% 3.59/0.98  
% 3.59/0.98  ------ Abstraction refinement Options
% 3.59/0.98  
% 3.59/0.98  --abstr_ref                             []
% 3.59/0.98  --abstr_ref_prep                        false
% 3.59/0.98  --abstr_ref_until_sat                   false
% 3.59/0.98  --abstr_ref_sig_restrict                funpre
% 3.59/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/0.98  --abstr_ref_under                       []
% 3.59/0.98  
% 3.59/0.98  ------ SAT Options
% 3.59/0.98  
% 3.59/0.98  --sat_mode                              false
% 3.59/0.98  --sat_fm_restart_options                ""
% 3.59/0.98  --sat_gr_def                            false
% 3.59/0.98  --sat_epr_types                         true
% 3.59/0.98  --sat_non_cyclic_types                  false
% 3.59/0.98  --sat_finite_models                     false
% 3.59/0.98  --sat_fm_lemmas                         false
% 3.59/0.98  --sat_fm_prep                           false
% 3.59/0.98  --sat_fm_uc_incr                        true
% 3.59/0.98  --sat_out_model                         small
% 3.59/0.98  --sat_out_clauses                       false
% 3.59/0.98  
% 3.59/0.98  ------ QBF Options
% 3.59/0.98  
% 3.59/0.98  --qbf_mode                              false
% 3.59/0.98  --qbf_elim_univ                         false
% 3.59/0.98  --qbf_dom_inst                          none
% 3.59/0.98  --qbf_dom_pre_inst                      false
% 3.59/0.98  --qbf_sk_in                             false
% 3.59/0.98  --qbf_pred_elim                         true
% 3.59/0.98  --qbf_split                             512
% 3.59/0.98  
% 3.59/0.98  ------ BMC1 Options
% 3.59/0.98  
% 3.59/0.98  --bmc1_incremental                      false
% 3.59/0.98  --bmc1_axioms                           reachable_all
% 3.59/0.98  --bmc1_min_bound                        0
% 3.59/0.98  --bmc1_max_bound                        -1
% 3.59/0.98  --bmc1_max_bound_default                -1
% 3.59/0.98  --bmc1_symbol_reachability              true
% 3.59/0.98  --bmc1_property_lemmas                  false
% 3.59/0.98  --bmc1_k_induction                      false
% 3.59/0.98  --bmc1_non_equiv_states                 false
% 3.59/0.98  --bmc1_deadlock                         false
% 3.59/0.98  --bmc1_ucm                              false
% 3.59/0.98  --bmc1_add_unsat_core                   none
% 3.59/0.98  --bmc1_unsat_core_children              false
% 3.59/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/0.98  --bmc1_out_stat                         full
% 3.59/0.98  --bmc1_ground_init                      false
% 3.59/0.98  --bmc1_pre_inst_next_state              false
% 3.59/0.98  --bmc1_pre_inst_state                   false
% 3.59/0.98  --bmc1_pre_inst_reach_state             false
% 3.59/0.98  --bmc1_out_unsat_core                   false
% 3.59/0.98  --bmc1_aig_witness_out                  false
% 3.59/0.98  --bmc1_verbose                          false
% 3.59/0.98  --bmc1_dump_clauses_tptp                false
% 3.59/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.59/0.98  --bmc1_dump_file                        -
% 3.59/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.59/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.59/0.98  --bmc1_ucm_extend_mode                  1
% 3.59/0.98  --bmc1_ucm_init_mode                    2
% 3.59/0.98  --bmc1_ucm_cone_mode                    none
% 3.59/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.59/0.98  --bmc1_ucm_relax_model                  4
% 3.59/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.59/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/0.98  --bmc1_ucm_layered_model                none
% 3.59/0.98  --bmc1_ucm_max_lemma_size               10
% 3.59/0.98  
% 3.59/0.98  ------ AIG Options
% 3.59/0.98  
% 3.59/0.98  --aig_mode                              false
% 3.59/0.98  
% 3.59/0.98  ------ Instantiation Options
% 3.59/0.98  
% 3.59/0.98  --instantiation_flag                    true
% 3.59/0.98  --inst_sos_flag                         true
% 3.59/0.98  --inst_sos_phase                        true
% 3.59/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel_side                     none
% 3.59/0.98  --inst_solver_per_active                1400
% 3.59/0.98  --inst_solver_calls_frac                1.
% 3.59/0.98  --inst_passive_queue_type               priority_queues
% 3.59/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/0.98  --inst_passive_queues_freq              [25;2]
% 3.59/0.98  --inst_dismatching                      true
% 3.59/0.98  --inst_eager_unprocessed_to_passive     true
% 3.59/0.98  --inst_prop_sim_given                   true
% 3.59/0.98  --inst_prop_sim_new                     false
% 3.59/0.98  --inst_subs_new                         false
% 3.59/0.98  --inst_eq_res_simp                      false
% 3.59/0.98  --inst_subs_given                       false
% 3.59/0.98  --inst_orphan_elimination               true
% 3.59/0.98  --inst_learning_loop_flag               true
% 3.59/0.98  --inst_learning_start                   3000
% 3.59/0.98  --inst_learning_factor                  2
% 3.59/0.98  --inst_start_prop_sim_after_learn       3
% 3.59/0.98  --inst_sel_renew                        solver
% 3.59/0.98  --inst_lit_activity_flag                true
% 3.59/0.98  --inst_restr_to_given                   false
% 3.59/0.98  --inst_activity_threshold               500
% 3.59/0.98  --inst_out_proof                        true
% 3.59/0.98  
% 3.59/0.98  ------ Resolution Options
% 3.59/0.98  
% 3.59/0.98  --resolution_flag                       false
% 3.59/0.98  --res_lit_sel                           adaptive
% 3.59/0.98  --res_lit_sel_side                      none
% 3.59/0.98  --res_ordering                          kbo
% 3.59/0.98  --res_to_prop_solver                    active
% 3.59/0.98  --res_prop_simpl_new                    false
% 3.59/0.98  --res_prop_simpl_given                  true
% 3.59/0.98  --res_passive_queue_type                priority_queues
% 3.59/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/0.98  --res_passive_queues_freq               [15;5]
% 3.59/0.98  --res_forward_subs                      full
% 3.59/0.98  --res_backward_subs                     full
% 3.59/0.98  --res_forward_subs_resolution           true
% 3.59/0.98  --res_backward_subs_resolution          true
% 3.59/0.98  --res_orphan_elimination                true
% 3.59/0.98  --res_time_limit                        2.
% 3.59/0.98  --res_out_proof                         true
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Options
% 3.59/0.98  
% 3.59/0.98  --superposition_flag                    true
% 3.59/0.98  --sup_passive_queue_type                priority_queues
% 3.59/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.59/0.98  --demod_completeness_check              fast
% 3.59/0.98  --demod_use_ground                      true
% 3.59/0.98  --sup_to_prop_solver                    passive
% 3.59/0.98  --sup_prop_simpl_new                    true
% 3.59/0.98  --sup_prop_simpl_given                  true
% 3.59/0.98  --sup_fun_splitting                     true
% 3.59/0.98  --sup_smt_interval                      50000
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Simplification Setup
% 3.59/0.98  
% 3.59/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.59/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.59/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.59/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.59/0.98  --sup_immed_triv                        [TrivRules]
% 3.59/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_bw_main                     []
% 3.59/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.59/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_input_bw                          []
% 3.59/0.98  
% 3.59/0.98  ------ Combination Options
% 3.59/0.98  
% 3.59/0.98  --comb_res_mult                         3
% 3.59/0.98  --comb_sup_mult                         2
% 3.59/0.98  --comb_inst_mult                        10
% 3.59/0.98  
% 3.59/0.98  ------ Debug Options
% 3.59/0.98  
% 3.59/0.98  --dbg_backtrace                         false
% 3.59/0.98  --dbg_dump_prop_clauses                 false
% 3.59/0.98  --dbg_dump_prop_clauses_file            -
% 3.59/0.98  --dbg_out_stat                          false
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  ------ Proving...
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  % SZS status Theorem for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  fof(f6,axiom,(
% 3.59/0.98    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f31,plain,(
% 3.59/0.98    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 3.59/0.98    inference(ennf_transformation,[],[f6])).
% 3.59/0.98  
% 3.59/0.98  fof(f79,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f31])).
% 3.59/0.98  
% 3.59/0.98  fof(f2,axiom,(
% 3.59/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f28,plain,(
% 3.59/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.59/0.98    inference(ennf_transformation,[],[f2])).
% 3.59/0.98  
% 3.59/0.98  fof(f56,plain,(
% 3.59/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.59/0.98    inference(nnf_transformation,[],[f28])).
% 3.59/0.98  
% 3.59/0.98  fof(f57,plain,(
% 3.59/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.59/0.98    inference(rectify,[],[f56])).
% 3.59/0.98  
% 3.59/0.98  fof(f58,plain,(
% 3.59/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.59/0.98    introduced(choice_axiom,[])).
% 3.59/0.98  
% 3.59/0.98  fof(f59,plain,(
% 3.59/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f57,f58])).
% 3.59/0.98  
% 3.59/0.98  fof(f72,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f59])).
% 3.59/0.98  
% 3.59/0.98  fof(f19,axiom,(
% 3.59/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f97,plain,(
% 3.59/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f19])).
% 3.59/0.98  
% 3.59/0.98  fof(f23,axiom,(
% 3.59/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f103,plain,(
% 3.59/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f23])).
% 3.59/0.98  
% 3.59/0.98  fof(f118,plain,(
% 3.59/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.59/0.98    inference(definition_unfolding,[],[f97,f103])).
% 3.59/0.98  
% 3.59/0.98  fof(f9,axiom,(
% 3.59/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f62,plain,(
% 3.59/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.59/0.98    inference(nnf_transformation,[],[f9])).
% 3.59/0.98  
% 3.59/0.98  fof(f82,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f62])).
% 3.59/0.98  
% 3.59/0.98  fof(f71,plain,(
% 3.59/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f59])).
% 3.59/0.98  
% 3.59/0.98  fof(f1,axiom,(
% 3.59/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f52,plain,(
% 3.59/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.59/0.98    inference(nnf_transformation,[],[f1])).
% 3.59/0.98  
% 3.59/0.98  fof(f53,plain,(
% 3.59/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.59/0.98    inference(rectify,[],[f52])).
% 3.59/0.98  
% 3.59/0.98  fof(f54,plain,(
% 3.59/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.59/0.98    introduced(choice_axiom,[])).
% 3.59/0.98  
% 3.59/0.98  fof(f55,plain,(
% 3.59/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f53,f54])).
% 3.59/0.98  
% 3.59/0.98  fof(f69,plain,(
% 3.59/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f55])).
% 3.59/0.98  
% 3.59/0.98  fof(f7,axiom,(
% 3.59/0.98    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f32,plain,(
% 3.59/0.98    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.59/0.98    inference(ennf_transformation,[],[f7])).
% 3.59/0.98  
% 3.59/0.98  fof(f80,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f32])).
% 3.59/0.98  
% 3.59/0.98  fof(f25,conjecture,(
% 3.59/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f26,negated_conjecture,(
% 3.59/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.59/0.98    inference(negated_conjecture,[],[f25])).
% 3.59/0.98  
% 3.59/0.98  fof(f50,plain,(
% 3.59/0.98    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.59/0.98    inference(ennf_transformation,[],[f26])).
% 3.59/0.98  
% 3.59/0.98  fof(f51,plain,(
% 3.59/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.59/0.98    inference(flattening,[],[f50])).
% 3.59/0.98  
% 3.59/0.98  fof(f67,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK5,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK5),k6_partfun1(X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK5,X1,X0) & v1_funct_1(sK5))) )),
% 3.59/0.98    introduced(choice_axiom,[])).
% 3.59/0.98  
% 3.59/0.98  fof(f66,plain,(
% 3.59/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(X3,sK3,sK2) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.59/0.98    introduced(choice_axiom,[])).
% 3.59/0.98  
% 3.59/0.98  fof(f68,plain,(
% 3.59/0.98    ((~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f51,f67,f66])).
% 3.59/0.98  
% 3.59/0.98  fof(f111,plain,(
% 3.59/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 3.59/0.98    inference(cnf_transformation,[],[f68])).
% 3.59/0.98  
% 3.59/0.98  fof(f106,plain,(
% 3.59/0.98    v1_funct_1(sK4)),
% 3.59/0.98    inference(cnf_transformation,[],[f68])).
% 3.59/0.98  
% 3.59/0.98  fof(f107,plain,(
% 3.59/0.98    v1_funct_2(sK4,sK2,sK3)),
% 3.59/0.98    inference(cnf_transformation,[],[f68])).
% 3.59/0.98  
% 3.59/0.98  fof(f108,plain,(
% 3.59/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.59/0.98    inference(cnf_transformation,[],[f68])).
% 3.59/0.98  
% 3.59/0.98  fof(f109,plain,(
% 3.59/0.98    v1_funct_1(sK5)),
% 3.59/0.98    inference(cnf_transformation,[],[f68])).
% 3.59/0.98  
% 3.59/0.98  fof(f110,plain,(
% 3.59/0.98    v1_funct_2(sK5,sK3,sK2)),
% 3.59/0.98    inference(cnf_transformation,[],[f68])).
% 3.59/0.98  
% 3.59/0.98  fof(f16,axiom,(
% 3.59/0.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f93,plain,(
% 3.59/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f16])).
% 3.59/0.98  
% 3.59/0.98  fof(f116,plain,(
% 3.59/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.59/0.98    inference(definition_unfolding,[],[f93,f103])).
% 3.59/0.98  
% 3.59/0.98  fof(f3,axiom,(
% 3.59/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f60,plain,(
% 3.59/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.98    inference(nnf_transformation,[],[f3])).
% 3.59/0.98  
% 3.59/0.98  fof(f61,plain,(
% 3.59/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.98    inference(flattening,[],[f60])).
% 3.59/0.98  
% 3.59/0.98  fof(f74,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.59/0.98    inference(cnf_transformation,[],[f61])).
% 3.59/0.98  
% 3.59/0.98  fof(f120,plain,(
% 3.59/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.59/0.98    inference(equality_resolution,[],[f74])).
% 3.59/0.98  
% 3.59/0.98  fof(f76,plain,(
% 3.59/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f61])).
% 3.59/0.98  
% 3.59/0.98  fof(f4,axiom,(
% 3.59/0.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f77,plain,(
% 3.59/0.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f4])).
% 3.59/0.98  
% 3.59/0.98  fof(f5,axiom,(
% 3.59/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f29,plain,(
% 3.59/0.98    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.59/0.98    inference(ennf_transformation,[],[f5])).
% 3.59/0.98  
% 3.59/0.98  fof(f30,plain,(
% 3.59/0.98    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.59/0.98    inference(flattening,[],[f29])).
% 3.59/0.98  
% 3.59/0.98  fof(f78,plain,(
% 3.59/0.98    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f30])).
% 3.59/0.98  
% 3.59/0.98  fof(f18,axiom,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f40,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.59/0.98    inference(ennf_transformation,[],[f18])).
% 3.59/0.98  
% 3.59/0.98  fof(f41,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(flattening,[],[f40])).
% 3.59/0.98  
% 3.59/0.98  fof(f64,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(nnf_transformation,[],[f41])).
% 3.59/0.98  
% 3.59/0.98  fof(f95,plain,(
% 3.59/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f64])).
% 3.59/0.98  
% 3.59/0.98  fof(f112,plain,(
% 3.59/0.98    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))),
% 3.59/0.98    inference(cnf_transformation,[],[f68])).
% 3.59/0.98  
% 3.59/0.98  fof(f11,axiom,(
% 3.59/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f35,plain,(
% 3.59/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(ennf_transformation,[],[f11])).
% 3.59/0.98  
% 3.59/0.98  fof(f63,plain,(
% 3.59/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(nnf_transformation,[],[f35])).
% 3.59/0.98  
% 3.59/0.98  fof(f86,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f63])).
% 3.59/0.98  
% 3.59/0.98  fof(f20,axiom,(
% 3.59/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f42,plain,(
% 3.59/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.59/0.98    inference(ennf_transformation,[],[f20])).
% 3.59/0.98  
% 3.59/0.98  fof(f43,plain,(
% 3.59/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(flattening,[],[f42])).
% 3.59/0.98  
% 3.59/0.98  fof(f65,plain,(
% 3.59/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(nnf_transformation,[],[f43])).
% 3.59/0.98  
% 3.59/0.98  fof(f99,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f65])).
% 3.59/0.98  
% 3.59/0.98  fof(f122,plain,(
% 3.59/0.98    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(equality_resolution,[],[f99])).
% 3.59/0.98  
% 3.59/0.98  fof(f113,plain,(
% 3.59/0.98    ~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)),
% 3.59/0.98    inference(cnf_transformation,[],[f68])).
% 3.59/0.98  
% 3.59/0.98  fof(f75,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.59/0.98    inference(cnf_transformation,[],[f61])).
% 3.59/0.98  
% 3.59/0.98  fof(f119,plain,(
% 3.59/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.59/0.98    inference(equality_resolution,[],[f75])).
% 3.59/0.98  
% 3.59/0.98  fof(f21,axiom,(
% 3.59/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f44,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.59/0.98    inference(ennf_transformation,[],[f21])).
% 3.59/0.98  
% 3.59/0.98  fof(f45,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.59/0.98    inference(flattening,[],[f44])).
% 3.59/0.98  
% 3.59/0.98  fof(f101,plain,(
% 3.59/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f45])).
% 3.59/0.98  
% 3.59/0.98  fof(f24,axiom,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f48,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.59/0.98    inference(ennf_transformation,[],[f24])).
% 3.59/0.98  
% 3.59/0.98  fof(f49,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.59/0.98    inference(flattening,[],[f48])).
% 3.59/0.98  
% 3.59/0.98  fof(f104,plain,(
% 3.59/0.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f49])).
% 3.59/0.98  
% 3.59/0.98  fof(f17,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f27,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.59/0.98    inference(pure_predicate_removal,[],[f17])).
% 3.59/0.98  
% 3.59/0.98  fof(f39,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(ennf_transformation,[],[f27])).
% 3.59/0.98  
% 3.59/0.98  fof(f94,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f39])).
% 3.59/0.98  
% 3.59/0.98  fof(f85,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f63])).
% 3.59/0.98  
% 3.59/0.98  fof(f12,axiom,(
% 3.59/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f87,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f12])).
% 3.59/0.98  
% 3.59/0.98  fof(f10,axiom,(
% 3.59/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f34,plain,(
% 3.59/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.59/0.98    inference(ennf_transformation,[],[f10])).
% 3.59/0.98  
% 3.59/0.98  fof(f84,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f34])).
% 3.59/0.98  
% 3.59/0.98  fof(f83,plain,(
% 3.59/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f62])).
% 3.59/0.98  
% 3.59/0.98  fof(f22,axiom,(
% 3.59/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f46,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.59/0.98    inference(ennf_transformation,[],[f22])).
% 3.59/0.98  
% 3.59/0.98  fof(f47,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.59/0.98    inference(flattening,[],[f46])).
% 3.59/0.98  
% 3.59/0.98  fof(f102,plain,(
% 3.59/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f47])).
% 3.59/0.98  
% 3.59/0.98  fof(f14,axiom,(
% 3.59/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f38,plain,(
% 3.59/0.98    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.59/0.98    inference(ennf_transformation,[],[f14])).
% 3.59/0.98  
% 3.59/0.98  fof(f89,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f38])).
% 3.59/0.98  
% 3.59/0.98  fof(f15,axiom,(
% 3.59/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f91,plain,(
% 3.59/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.59/0.98    inference(cnf_transformation,[],[f15])).
% 3.59/0.98  
% 3.59/0.98  fof(f114,plain,(
% 3.59/0.98    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.59/0.98    inference(definition_unfolding,[],[f91,f103])).
% 3.59/0.98  
% 3.59/0.98  cnf(c_10,plain,
% 3.59/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1781,plain,
% 3.59/0.98      ( v1_xboole_0(X0) != iProver_top
% 3.59/0.98      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3,plain,
% 3.59/0.98      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1785,plain,
% 3.59/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.59/0.98      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_28,plain,
% 3.59/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f118]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1772,plain,
% 3.59/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_14,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1778,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.59/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2701,plain,
% 3.59/0.98      ( r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1772,c_1778]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1784,plain,
% 3.59/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.59/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.59/0.98      | r2_hidden(X2,X1) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3590,plain,
% 3.59/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X1)) = iProver_top
% 3.59/0.98      | r2_hidden(X0,k6_partfun1(X1)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2701,c_1784]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1,plain,
% 3.59/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1787,plain,
% 3.59/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.59/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8621,plain,
% 3.59/0.98      ( r2_hidden(X0,k6_partfun1(X1)) != iProver_top
% 3.59/0.98      | v1_xboole_0(k2_zfmisc_1(X1,X1)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_3590,c_1787]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_10469,plain,
% 3.59/0.98      ( r1_tarski(k6_partfun1(X0),X1) = iProver_top
% 3.59/0.98      | v1_xboole_0(k2_zfmisc_1(X0,X0)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1785,c_8621]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_10875,plain,
% 3.59/0.98      ( r1_tarski(k6_partfun1(X0),X1) = iProver_top
% 3.59/0.98      | v1_xboole_0(X0) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1781,c_10469]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_11,plain,
% 3.59/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1780,plain,
% 3.59/0.98      ( v1_xboole_0(X0) != iProver_top
% 3.59/0.98      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_38,negated_conjecture,
% 3.59/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f111]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1766,plain,
% 3.59/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2702,plain,
% 3.59/0.98      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK2)) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1766,c_1778]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3591,plain,
% 3.59/0.98      ( r2_hidden(X0,k2_zfmisc_1(sK3,sK2)) = iProver_top
% 3.59/0.98      | r2_hidden(X0,sK5) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2702,c_1784]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3830,plain,
% 3.59/0.98      ( r2_hidden(X0,sK5) != iProver_top
% 3.59/0.98      | v1_xboole_0(k2_zfmisc_1(sK3,sK2)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_3591,c_1787]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4774,plain,
% 3.59/0.98      ( r2_hidden(X0,sK5) != iProver_top
% 3.59/0.98      | v1_xboole_0(sK3) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1780,c_3830]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5571,plain,
% 3.59/0.98      ( r1_tarski(sK5,X0) = iProver_top
% 3.59/0.98      | v1_xboole_0(sK3) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1785,c_4774]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_43,negated_conjecture,
% 3.59/0.98      ( v1_funct_1(sK4) ),
% 3.59/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_42,negated_conjecture,
% 3.59/0.98      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.59/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_41,negated_conjecture,
% 3.59/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_40,negated_conjecture,
% 3.59/0.98      ( v1_funct_1(sK5) ),
% 3.59/0.98      inference(cnf_transformation,[],[f109]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_39,negated_conjecture,
% 3.59/0.98      ( v1_funct_2(sK5,sK3,sK2) ),
% 3.59/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_74,plain,
% 3.59/0.98      ( m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_28]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_23,plain,
% 3.59/0.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f116]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_89,plain,
% 3.59/0.98      ( v2_funct_1(k6_partfun1(sK2)) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7,plain,
% 3.59/0.98      ( r1_tarski(X0,X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f120]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_127,plain,
% 3.59/0.98      ( r1_tarski(sK2,sK2) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_126,plain,
% 3.59/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_128,plain,
% 3.59/0.98      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_126]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_131,plain,
% 3.59/0.98      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8,plain,
% 3.59/0.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_9,plain,
% 3.59/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_546,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1)
% 3.59/0.98      | v1_xboole_0(X0)
% 3.59/0.98      | X0 != X2
% 3.59/0.98      | k1_xboole_0 != X1 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_547,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_546]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_548,plain,
% 3.59/0.98      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.59/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_550,plain,
% 3.59/0.98      ( r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.59/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_548]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_27,plain,
% 3.59/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.59/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.59/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.59/0.98      | X3 = X2 ),
% 3.59/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_37,negated_conjecture,
% 3.59/0.98      ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f112]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_563,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | X3 = X0
% 3.59/0.98      | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
% 3.59/0.98      | k6_partfun1(sK2) != X3
% 3.59/0.98      | sK2 != X2
% 3.59/0.98      | sK2 != X1 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_37]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_564,plain,
% 3.59/0.98      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 3.59/0.98      | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 3.59/0.98      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_563]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_16,plain,
% 3.59/0.98      ( v5_relat_1(X0,X1)
% 3.59/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_29,plain,
% 3.59/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.59/0.98      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f122]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_36,negated_conjecture,
% 3.59/0.98      ( ~ v2_funct_2(sK5,sK2) | ~ v2_funct_1(sK4) ),
% 3.59/0.98      inference(cnf_transformation,[],[f113]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_582,plain,
% 3.59/0.98      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.59/0.98      | ~ v2_funct_1(sK4)
% 3.59/0.98      | ~ v1_relat_1(X0)
% 3.59/0.98      | k2_relat_1(X0) != sK2
% 3.59/0.98      | sK5 != X0 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_36]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_583,plain,
% 3.59/0.98      ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
% 3.59/0.98      | ~ v2_funct_1(sK4)
% 3.59/0.98      | ~ v1_relat_1(sK5)
% 3.59/0.98      | k2_relat_1(sK5) != sK2 ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_582]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_636,plain,
% 3.59/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.59/0.98      | ~ v2_funct_1(sK4)
% 3.59/0.98      | ~ v1_relat_1(X0)
% 3.59/0.98      | ~ v1_relat_1(sK5)
% 3.59/0.98      | k2_relat_1(sK5) != X1
% 3.59/0.98      | k2_relat_1(sK5) != sK2
% 3.59/0.98      | sK5 != X0 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_583]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_637,plain,
% 3.59/0.98      ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
% 3.59/0.98      | ~ v2_funct_1(sK4)
% 3.59/0.98      | ~ v1_relat_1(sK5)
% 3.59/0.98      | k2_relat_1(sK5) != sK2 ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_636]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6,plain,
% 3.59/0.98      ( r1_tarski(X0,X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f119]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_647,plain,
% 3.59/0.98      ( ~ v2_funct_1(sK4) | ~ v1_relat_1(sK5) | k2_relat_1(sK5) != sK2 ),
% 3.59/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_637,c_6]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_31,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.59/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.59/0.98      | ~ v1_funct_1(X0)
% 3.59/0.98      | ~ v1_funct_1(X3) ),
% 3.59/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1834,plain,
% 3.59/0.98      ( m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 3.59/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.59/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.59/0.98      | ~ v1_funct_1(sK4)
% 3.59/0.98      | ~ v1_funct_1(sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_31]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_35,plain,
% 3.59/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.59/0.98      | ~ v1_funct_2(X3,X4,X1)
% 3.59/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ v1_funct_1(X0)
% 3.59/0.98      | ~ v1_funct_1(X3)
% 3.59/0.98      | v2_funct_1(X3)
% 3.59/0.98      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.59/0.98      | k1_xboole_0 = X2 ),
% 3.59/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1842,plain,
% 3.59/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.59/0.98      | ~ v1_funct_2(sK4,X3,X1)
% 3.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.59/0.98      | ~ v1_funct_1(X0)
% 3.59/0.98      | ~ v1_funct_1(sK4)
% 3.59/0.98      | ~ v2_funct_1(k1_partfun1(X3,X1,X1,X2,sK4,X0))
% 3.59/0.98      | v2_funct_1(sK4)
% 3.59/0.98      | k1_xboole_0 = X2 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_35]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1891,plain,
% 3.59/0.98      ( ~ v1_funct_2(sK4,X0,X1)
% 3.59/0.98      | ~ v1_funct_2(sK5,X1,X2)
% 3.59/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.59/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ v1_funct_1(sK4)
% 3.59/0.98      | ~ v1_funct_1(sK5)
% 3.59/0.98      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,sK4,sK5))
% 3.59/0.98      | v2_funct_1(sK4)
% 3.59/0.98      | k1_xboole_0 = X2 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1842]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2029,plain,
% 3.59/0.98      ( ~ v1_funct_2(sK4,sK2,sK3)
% 3.59/0.98      | ~ v1_funct_2(sK5,sK3,X0)
% 3.59/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.59/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
% 3.59/0.98      | ~ v1_funct_1(sK4)
% 3.59/0.98      | ~ v1_funct_1(sK5)
% 3.59/0.98      | ~ v2_funct_1(k1_partfun1(sK2,sK3,sK3,X0,sK4,sK5))
% 3.59/0.98      | v2_funct_1(sK4)
% 3.59/0.98      | k1_xboole_0 = X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1891]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2031,plain,
% 3.59/0.98      ( ~ v1_funct_2(sK4,sK2,sK3)
% 3.59/0.98      | ~ v1_funct_2(sK5,sK3,sK2)
% 3.59/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.59/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.59/0.98      | ~ v1_funct_1(sK4)
% 3.59/0.98      | ~ v1_funct_1(sK5)
% 3.59/0.98      | ~ v2_funct_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
% 3.59/0.98      | v2_funct_1(sK4)
% 3.59/0.98      | k1_xboole_0 = sK2 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2029]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_961,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2008,plain,
% 3.59/0.98      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_961]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2397,plain,
% 3.59/0.98      ( X0 != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
% 3.59/0.98      | X0 = k6_partfun1(sK2)
% 3.59/0.98      | k6_partfun1(sK2) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2008]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2449,plain,
% 3.59/0.98      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
% 3.59/0.98      | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2)
% 3.59/0.98      | k6_partfun1(sK2) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2397]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_960,plain,( X0 = X0 ),theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2824,plain,
% 3.59/0.98      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_960]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_25,plain,
% 3.59/0.98      ( v5_relat_1(X0,X1)
% 3.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_17,plain,
% 3.59/0.98      ( ~ v5_relat_1(X0,X1)
% 3.59/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_603,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_25,c_17]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1756,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2711,plain,
% 3.59/0.98      ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
% 3.59/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1766,c_1756]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1783,plain,
% 3.59/0.98      ( X0 = X1
% 3.59/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.59/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3468,plain,
% 3.59/0.98      ( k2_relat_1(sK5) = sK2
% 3.59/0.98      | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top
% 3.59/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2711,c_1783]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_18,plain,
% 3.59/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1777,plain,
% 3.59/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_15,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.59/0.98      | ~ v1_relat_1(X1)
% 3.59/0.98      | v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_13,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_322,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.59/0.98      inference(prop_impl,[status(thm)],[c_13]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_323,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_322]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_401,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.59/0.98      inference(bin_hyper_res,[status(thm)],[c_15,c_323]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1759,plain,
% 3.59/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.59/0.98      | v1_relat_1(X1) != iProver_top
% 3.59/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3386,plain,
% 3.59/0.98      ( v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top
% 3.59/0.98      | v1_relat_1(sK5) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2702,c_1759]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3646,plain,
% 3.59/0.98      ( v1_relat_1(sK5) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1777,c_3386]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3647,plain,
% 3.59/0.98      ( v1_relat_1(sK5) ),
% 3.59/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3646]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1763,plain,
% 3.59/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2703,plain,
% 3.59/0.98      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1763,c_1778]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3387,plain,
% 3.59/0.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 3.59/0.98      | v1_relat_1(sK4) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2703,c_1759]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3649,plain,
% 3.59/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1777,c_3387]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_33,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.59/0.98      | ~ v1_funct_1(X0)
% 3.59/0.98      | ~ v1_funct_1(X3)
% 3.59/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1769,plain,
% 3.59/0.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.59/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.59/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/0.98      | v1_funct_1(X5) != iProver_top
% 3.59/0.98      | v1_funct_1(X4) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4294,plain,
% 3.59/0.98      ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
% 3.59/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/0.98      | v1_funct_1(X2) != iProver_top
% 3.59/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1766,c_1769]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_47,plain,
% 3.59/0.98      ( v1_funct_1(sK5) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4307,plain,
% 3.59/0.98      ( v1_funct_1(X2) != iProver_top
% 3.59/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/0.98      | k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_4294,c_47]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4308,plain,
% 3.59/0.98      ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
% 3.59/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_4307]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4316,plain,
% 3.59/0.98      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
% 3.59/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1763,c_4308]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_566,plain,
% 3.59/0.98      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 3.59/0.98      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_564,c_74]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1757,plain,
% 3.59/0.98      ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
% 3.59/0.98      | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_566]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2118,plain,
% 3.59/0.98      ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_1757,c_43,c_41,c_40,c_38,c_74,c_564,c_1834]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4317,plain,
% 3.59/0.98      ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2)
% 3.59/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.59/0.98      inference(light_normalisation,[status(thm)],[c_4316,c_2118]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_44,plain,
% 3.59/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4586,plain,
% 3.59/0.98      ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_4317,c_44]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_20,plain,
% 3.59/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.59/0.98      | ~ v1_relat_1(X0)
% 3.59/0.98      | ~ v1_relat_1(X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1775,plain,
% 3.59/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top
% 3.59/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4588,plain,
% 3.59/0.98      ( r1_tarski(k2_relat_1(k6_partfun1(sK2)),k2_relat_1(sK5)) = iProver_top
% 3.59/0.98      | v1_relat_1(sK4) != iProver_top
% 3.59/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_4586,c_1775]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_21,plain,
% 3.59/0.98      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f114]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4589,plain,
% 3.59/0.98      ( r1_tarski(sK2,k2_relat_1(sK5)) = iProver_top
% 3.59/0.98      | v1_relat_1(sK4) != iProver_top
% 3.59/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_4588,c_21]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_972,plain,
% 3.59/0.98      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.59/0.98      theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1913,plain,
% 3.59/0.98      ( v2_funct_1(X0)
% 3.59/0.98      | ~ v2_funct_1(k6_partfun1(X1))
% 3.59/0.98      | X0 != k6_partfun1(X1) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_972]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4697,plain,
% 3.59/0.98      ( v2_funct_1(k1_partfun1(sK2,sK3,sK3,X0,sK4,sK5))
% 3.59/0.98      | ~ v2_funct_1(k6_partfun1(X1))
% 3.59/0.98      | k1_partfun1(sK2,sK3,sK3,X0,sK4,sK5) != k6_partfun1(X1) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1913]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4699,plain,
% 3.59/0.98      ( v2_funct_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
% 3.59/0.98      | ~ v2_funct_1(k6_partfun1(sK2))
% 3.59/0.98      | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != k6_partfun1(sK2) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_4697]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4773,plain,
% 3.59/0.98      ( r2_hidden(X0,sK5) != iProver_top
% 3.59/0.98      | v1_xboole_0(sK2) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1781,c_3830]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5313,plain,
% 3.59/0.98      ( r1_tarski(sK5,X0) = iProver_top
% 3.59/0.98      | v1_xboole_0(sK2) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1785,c_4773]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_964,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.59/0.98      theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5657,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1)
% 3.59/0.98      | r1_tarski(X2,k1_xboole_0)
% 3.59/0.98      | X2 != X0
% 3.59/0.98      | k1_xboole_0 != X1 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_964]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5658,plain,
% 3.59/0.98      ( X0 != X1
% 3.59/0.98      | k1_xboole_0 != X2
% 3.59/0.98      | r1_tarski(X1,X2) != iProver_top
% 3.59/0.98      | r1_tarski(X0,k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_5657]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5660,plain,
% 3.59/0.98      ( sK2 != sK2
% 3.59/0.98      | k1_xboole_0 != sK2
% 3.59/0.98      | r1_tarski(sK2,sK2) != iProver_top
% 3.59/0.98      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_5658]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7980,plain,
% 3.59/0.98      ( r1_tarski(sK5,X0) = iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_5571,c_43,c_42,c_41,c_40,c_39,c_38,c_74,c_89,c_127,
% 3.59/0.98                 c_128,c_131,c_550,c_564,c_647,c_1834,c_2031,c_2449,
% 3.59/0.98                 c_2824,c_3468,c_3646,c_3647,c_3649,c_4589,c_4699,c_5313,
% 3.59/0.98                 c_5660]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7987,plain,
% 3.59/0.98      ( sK5 = X0 | r1_tarski(X0,sK5) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_7980,c_1783]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12205,plain,
% 3.59/0.98      ( k6_partfun1(X0) = sK5 | v1_xboole_0(X0) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_10875,c_7987]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12215,plain,
% 3.59/0.98      ( k6_partfun1(sK2) = sK5 | v1_xboole_0(sK2) != iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_12205]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2995,plain,
% 3.59/0.98      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1785,c_1787]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3467,plain,
% 3.59/0.98      ( k2_zfmisc_1(sK2,sK3) = sK4
% 3.59/0.98      | r1_tarski(k2_zfmisc_1(sK2,sK3),sK4) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2703,c_1783]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3712,plain,
% 3.59/0.98      ( k2_zfmisc_1(sK2,sK3) = sK4
% 3.59/0.98      | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2995,c_3467]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1767,plain,
% 3.59/0.98      ( k1_xboole_0 = X0
% 3.59/0.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.59/0.98      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.59/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.59/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.59/0.99      | v1_funct_1(X1) != iProver_top
% 3.59/0.99      | v1_funct_1(X3) != iProver_top
% 3.59/0.99      | v2_funct_1(X3) = iProver_top
% 3.59/0.99      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3396,plain,
% 3.59/0.99      ( sK2 = k1_xboole_0
% 3.59/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.59/0.99      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 3.59/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.59/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.59/0.99      | v1_funct_1(sK4) != iProver_top
% 3.59/0.99      | v1_funct_1(sK5) != iProver_top
% 3.59/0.99      | v2_funct_1(k6_partfun1(sK2)) != iProver_top
% 3.59/0.99      | v2_funct_1(sK4) = iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_2118,c_1767]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_45,plain,
% 3.59/0.99      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_46,plain,
% 3.59/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_48,plain,
% 3.59/0.99      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_49,plain,
% 3.59/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_88,plain,
% 3.59/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_90,plain,
% 3.59/0.99      ( v2_funct_1(k6_partfun1(sK2)) = iProver_top ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_88]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_648,plain,
% 3.59/0.99      ( k2_relat_1(sK5) != sK2
% 3.59/0.99      | v2_funct_1(sK4) != iProver_top
% 3.59/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_6630,plain,
% 3.59/0.99      ( sK2 = k1_xboole_0 ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_3396,c_44,c_45,c_46,c_47,c_48,c_49,c_90,c_648,c_3468,
% 3.59/0.99                 c_3646,c_3649,c_4589]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_9467,plain,
% 3.59/0.99      ( k2_zfmisc_1(k1_xboole_0,sK3) = sK4
% 3.59/0.99      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK3)) != iProver_top ),
% 3.59/0.99      inference(light_normalisation,[status(thm)],[c_3712,c_6630]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_9469,plain,
% 3.59/0.99      ( k2_zfmisc_1(k1_xboole_0,sK3) = sK4
% 3.59/0.99      | v1_xboole_0(sK3) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1781,c_9467]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1782,plain,
% 3.59/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1758,plain,
% 3.59/0.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.59/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2395,plain,
% 3.59/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1782,c_1758]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_9470,plain,
% 3.59/0.99      ( k2_zfmisc_1(k1_xboole_0,sK3) = sK4
% 3.59/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1780,c_9467]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_9555,plain,
% 3.59/0.99      ( k2_zfmisc_1(k1_xboole_0,sK3) = sK4 ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_9469,c_2395,c_9470]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_9567,plain,
% 3.59/0.99      ( v1_xboole_0(sK4) = iProver_top
% 3.59/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_9555,c_1780]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8321,plain,
% 3.59/0.99      ( ~ r2_hidden(sK1(X0,sK5),X0) | ~ v1_xboole_0(X0) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8323,plain,
% 3.59/0.99      ( ~ r2_hidden(sK1(sK2,sK5),sK2) | ~ v1_xboole_0(sK2) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_8321]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1906,plain,
% 3.59/0.99      ( k6_partfun1(X0) != X1 | sK4 != X1 | sK4 = k6_partfun1(X0) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_961]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8119,plain,
% 3.59/0.99      ( k6_partfun1(X0) != sK5 | sK4 = k6_partfun1(X0) | sK4 != sK5 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_1906]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8120,plain,
% 3.59/0.99      ( k6_partfun1(sK2) != sK5 | sK4 = k6_partfun1(sK2) | sK4 != sK5 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_8119]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_7966,plain,
% 3.59/0.99      ( ~ r2_hidden(sK1(sK4,X0),sK4) | ~ v1_xboole_0(sK4) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_7967,plain,
% 3.59/0.99      ( r2_hidden(sK1(sK4,X0),sK4) != iProver_top
% 3.59/0.99      | v1_xboole_0(sK4) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_7966]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_7969,plain,
% 3.59/0.99      ( r2_hidden(sK1(sK4,sK2),sK4) != iProver_top
% 3.59/0.99      | v1_xboole_0(sK4) != iProver_top ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_7967]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5659,plain,
% 3.59/0.99      ( ~ r1_tarski(sK2,sK2)
% 3.59/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.59/0.99      | sK2 != sK2
% 3.59/0.99      | k1_xboole_0 != sK2 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_5657]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5315,plain,
% 3.59/0.99      ( r1_tarski(sK5,X0) | ~ v1_xboole_0(sK2) ),
% 3.59/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5313]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5317,plain,
% 3.59/0.99      ( r1_tarski(sK5,sK2) | ~ v1_xboole_0(sK2) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_5315]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4355,plain,
% 3.59/0.99      ( ~ r2_hidden(sK1(X0,sK4),X0) | ~ v1_xboole_0(X0) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4356,plain,
% 3.59/0.99      ( r2_hidden(sK1(X0,sK4),X0) != iProver_top
% 3.59/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_4355]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4358,plain,
% 3.59/0.99      ( r2_hidden(sK1(sK2,sK4),sK2) != iProver_top
% 3.59/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_4356]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2143,plain,
% 3.59/0.99      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_961]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4166,plain,
% 3.59/0.99      ( sK4 != X0 | sK4 = sK5 | sK5 != X0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2143]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4171,plain,
% 3.59/0.99      ( sK4 != sK2 | sK4 = sK5 | sK5 != sK2 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_4166]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2877,plain,
% 3.59/0.99      ( r1_tarski(sK4,X0) | r2_hidden(sK1(sK4,X0),sK4) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2883,plain,
% 3.59/0.99      ( r1_tarski(sK4,X0) = iProver_top
% 3.59/0.99      | r2_hidden(sK1(sK4,X0),sK4) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2877]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2885,plain,
% 3.59/0.99      ( r1_tarski(sK4,sK2) = iProver_top
% 3.59/0.99      | r2_hidden(sK1(sK4,sK2),sK4) = iProver_top ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2883]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2279,plain,
% 3.59/0.99      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2281,plain,
% 3.59/0.99      ( ~ r1_tarski(sK2,sK5) | ~ r1_tarski(sK5,sK2) | sK5 = sK2 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2279]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2249,plain,
% 3.59/0.99      ( r1_tarski(X0,sK4) | r2_hidden(sK1(X0,sK4),X0) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2255,plain,
% 3.59/0.99      ( r1_tarski(X0,sK4) = iProver_top
% 3.59/0.99      | r2_hidden(sK1(X0,sK4),X0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2249]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2257,plain,
% 3.59/0.99      ( r1_tarski(sK2,sK4) = iProver_top
% 3.59/0.99      | r2_hidden(sK1(sK2,sK4),sK2) = iProver_top ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2255]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2221,plain,
% 3.59/0.99      ( r1_tarski(X0,sK5) | r2_hidden(sK1(X0,sK5),X0) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2228,plain,
% 3.59/0.99      ( r1_tarski(sK2,sK5) | r2_hidden(sK1(sK2,sK5),sK2) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2221]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2070,plain,
% 3.59/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2071,plain,
% 3.59/0.99      ( sK4 = X0
% 3.59/0.99      | r1_tarski(X0,sK4) != iProver_top
% 3.59/0.99      | r1_tarski(sK4,X0) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2070]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2073,plain,
% 3.59/0.99      ( sK4 = sK2
% 3.59/0.99      | r1_tarski(sK4,sK2) != iProver_top
% 3.59/0.99      | r1_tarski(sK2,sK4) != iProver_top ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2071]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1852,plain,
% 3.59/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(sK4) | sK4 != X0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_972]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1859,plain,
% 3.59/0.99      ( ~ v2_funct_1(k6_partfun1(X0))
% 3.59/0.99      | v2_funct_1(sK4)
% 3.59/0.99      | sK4 != k6_partfun1(X0) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_1852]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1860,plain,
% 3.59/0.99      ( sK4 != k6_partfun1(X0)
% 3.59/0.99      | v2_funct_1(k6_partfun1(X0)) != iProver_top
% 3.59/0.99      | v2_funct_1(sK4) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1859]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1862,plain,
% 3.59/0.99      ( sK4 != k6_partfun1(sK2)
% 3.59/0.99      | v2_funct_1(k6_partfun1(sK2)) != iProver_top
% 3.59/0.99      | v2_funct_1(sK4) = iProver_top ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_1860]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_549,plain,
% 3.59/0.99      ( ~ r1_tarski(sK2,k1_xboole_0) | v1_xboole_0(sK2) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_547]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(contradiction,plain,
% 3.59/0.99      ( $false ),
% 3.59/0.99      inference(minisat,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_12215,c_9567,c_8323,c_8120,c_7969,c_5660,c_5659,
% 3.59/0.99                 c_5317,c_4699,c_4589,c_4358,c_4171,c_3649,c_3647,c_3646,
% 3.59/0.99                 c_3468,c_2885,c_2824,c_2449,c_2395,c_2281,c_2257,c_2228,
% 3.59/0.99                 c_2073,c_2031,c_1862,c_1834,c_648,c_647,c_564,c_550,
% 3.59/0.99                 c_549,c_131,c_128,c_127,c_90,c_89,c_74,c_38,c_39,c_40,
% 3.59/0.99                 c_41,c_42,c_43]) ).
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/0.99  
% 3.59/0.99  ------                               Statistics
% 3.59/0.99  
% 3.59/0.99  ------ General
% 3.59/0.99  
% 3.59/0.99  abstr_ref_over_cycles:                  0
% 3.59/0.99  abstr_ref_under_cycles:                 0
% 3.59/0.99  gc_basic_clause_elim:                   0
% 3.59/0.99  forced_gc_time:                         0
% 3.59/0.99  parsing_time:                           0.009
% 3.59/0.99  unif_index_cands_time:                  0.
% 3.59/0.99  unif_index_add_time:                    0.
% 3.59/0.99  orderings_time:                         0.
% 3.59/0.99  out_proof_time:                         0.016
% 3.59/0.99  total_time:                             0.403
% 3.59/0.99  num_of_symbols:                         57
% 3.59/0.99  num_of_terms:                           17039
% 3.59/0.99  
% 3.59/0.99  ------ Preprocessing
% 3.59/0.99  
% 3.59/0.99  num_of_splits:                          0
% 3.59/0.99  num_of_split_atoms:                     0
% 3.59/0.99  num_of_reused_defs:                     0
% 3.59/0.99  num_eq_ax_congr_red:                    20
% 3.59/0.99  num_of_sem_filtered_clauses:            1
% 3.59/0.99  num_of_subtypes:                        0
% 3.59/0.99  monotx_restored_types:                  0
% 3.59/0.99  sat_num_of_epr_types:                   0
% 3.59/0.99  sat_num_of_non_cyclic_types:            0
% 3.59/0.99  sat_guarded_non_collapsed_types:        0
% 3.59/0.99  num_pure_diseq_elim:                    0
% 3.59/0.99  simp_replaced_by:                       0
% 3.59/0.99  res_preprocessed:                       184
% 3.59/0.99  prep_upred:                             0
% 3.59/0.99  prep_unflattend:                        17
% 3.59/0.99  smt_new_axioms:                         0
% 3.59/0.99  pred_elim_cands:                        8
% 3.59/0.99  pred_elim:                              4
% 3.59/0.99  pred_elim_cl:                           7
% 3.59/0.99  pred_elim_cycles:                       6
% 3.59/0.99  merged_defs:                            8
% 3.59/0.99  merged_defs_ncl:                        0
% 3.59/0.99  bin_hyper_res:                          10
% 3.59/0.99  prep_cycles:                            4
% 3.59/0.99  pred_elim_time:                         0.003
% 3.59/0.99  splitting_time:                         0.
% 3.59/0.99  sem_filter_time:                        0.
% 3.59/0.99  monotx_time:                            0.
% 3.59/0.99  subtype_inf_time:                       0.
% 3.59/0.99  
% 3.59/0.99  ------ Problem properties
% 3.59/0.99  
% 3.59/0.99  clauses:                                36
% 3.59/0.99  conjectures:                            6
% 3.59/0.99  epr:                                    11
% 3.59/0.99  horn:                                   33
% 3.59/0.99  ground:                                 8
% 3.59/0.99  unary:                                  13
% 3.59/0.99  binary:                                 10
% 3.59/0.99  lits:                                   89
% 3.59/0.99  lits_eq:                                7
% 3.59/0.99  fd_pure:                                0
% 3.59/0.99  fd_pseudo:                              0
% 3.59/0.99  fd_cond:                                1
% 3.59/0.99  fd_pseudo_cond:                         1
% 3.59/0.99  ac_symbols:                             0
% 3.59/0.99  
% 3.59/0.99  ------ Propositional Solver
% 3.59/0.99  
% 3.59/0.99  prop_solver_calls:                      33
% 3.59/0.99  prop_fast_solver_calls:                 1392
% 3.59/0.99  smt_solver_calls:                       0
% 3.59/0.99  smt_fast_solver_calls:                  0
% 3.59/0.99  prop_num_of_clauses:                    5457
% 3.59/0.99  prop_preprocess_simplified:             13371
% 3.59/0.99  prop_fo_subsumed:                       69
% 3.59/0.99  prop_solver_time:                       0.
% 3.59/0.99  smt_solver_time:                        0.
% 3.59/0.99  smt_fast_solver_time:                   0.
% 3.59/0.99  prop_fast_solver_time:                  0.
% 3.59/0.99  prop_unsat_core_time:                   0.
% 3.59/0.99  
% 3.59/0.99  ------ QBF
% 3.59/0.99  
% 3.59/0.99  qbf_q_res:                              0
% 3.59/0.99  qbf_num_tautologies:                    0
% 3.59/0.99  qbf_prep_cycles:                        0
% 3.59/0.99  
% 3.59/0.99  ------ BMC1
% 3.59/0.99  
% 3.59/0.99  bmc1_current_bound:                     -1
% 3.59/0.99  bmc1_last_solved_bound:                 -1
% 3.59/0.99  bmc1_unsat_core_size:                   -1
% 3.59/0.99  bmc1_unsat_core_parents_size:           -1
% 3.59/0.99  bmc1_merge_next_fun:                    0
% 3.59/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.59/0.99  
% 3.59/0.99  ------ Instantiation
% 3.59/0.99  
% 3.59/0.99  inst_num_of_clauses:                    1450
% 3.59/0.99  inst_num_in_passive:                    816
% 3.59/0.99  inst_num_in_active:                     548
% 3.59/0.99  inst_num_in_unprocessed:                86
% 3.59/0.99  inst_num_of_loops:                      730
% 3.59/0.99  inst_num_of_learning_restarts:          0
% 3.59/0.99  inst_num_moves_active_passive:          177
% 3.59/0.99  inst_lit_activity:                      0
% 3.59/0.99  inst_lit_activity_moves:                0
% 3.59/0.99  inst_num_tautologies:                   0
% 3.59/0.99  inst_num_prop_implied:                  0
% 3.59/0.99  inst_num_existing_simplified:           0
% 3.59/0.99  inst_num_eq_res_simplified:             0
% 3.59/0.99  inst_num_child_elim:                    0
% 3.59/0.99  inst_num_of_dismatching_blockings:      339
% 3.59/0.99  inst_num_of_non_proper_insts:           1300
% 3.59/0.99  inst_num_of_duplicates:                 0
% 3.59/0.99  inst_inst_num_from_inst_to_res:         0
% 3.59/0.99  inst_dismatching_checking_time:         0.
% 3.59/0.99  
% 3.59/0.99  ------ Resolution
% 3.59/0.99  
% 3.59/0.99  res_num_of_clauses:                     0
% 3.59/0.99  res_num_in_passive:                     0
% 3.59/0.99  res_num_in_active:                      0
% 3.59/0.99  res_num_of_loops:                       188
% 3.59/0.99  res_forward_subset_subsumed:            106
% 3.59/0.99  res_backward_subset_subsumed:           0
% 3.59/0.99  res_forward_subsumed:                   0
% 3.59/0.99  res_backward_subsumed:                  1
% 3.59/0.99  res_forward_subsumption_resolution:     1
% 3.59/0.99  res_backward_subsumption_resolution:    0
% 3.59/0.99  res_clause_to_clause_subsumption:       613
% 3.59/0.99  res_orphan_elimination:                 0
% 3.59/0.99  res_tautology_del:                      74
% 3.59/0.99  res_num_eq_res_simplified:              0
% 3.59/0.99  res_num_sel_changes:                    0
% 3.59/0.99  res_moves_from_active_to_pass:          0
% 3.59/0.99  
% 3.59/0.99  ------ Superposition
% 3.59/0.99  
% 3.59/0.99  sup_time_total:                         0.
% 3.59/0.99  sup_time_generating:                    0.
% 3.59/0.99  sup_time_sim_full:                      0.
% 3.59/0.99  sup_time_sim_immed:                     0.
% 3.59/0.99  
% 3.59/0.99  sup_num_of_clauses:                     220
% 3.59/0.99  sup_num_in_active:                      93
% 3.59/0.99  sup_num_in_passive:                     127
% 3.59/0.99  sup_num_of_loops:                       144
% 3.59/0.99  sup_fw_superposition:                   122
% 3.59/0.99  sup_bw_superposition:                   192
% 3.59/0.99  sup_immediate_simplified:               62
% 3.59/0.99  sup_given_eliminated:                   0
% 3.59/0.99  comparisons_done:                       0
% 3.59/0.99  comparisons_avoided:                    0
% 3.59/0.99  
% 3.59/0.99  ------ Simplifications
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  sim_fw_subset_subsumed:                 24
% 3.59/0.99  sim_bw_subset_subsumed:                 17
% 3.59/0.99  sim_fw_subsumed:                        19
% 3.59/0.99  sim_bw_subsumed:                        7
% 3.59/0.99  sim_fw_subsumption_res:                 0
% 3.59/0.99  sim_bw_subsumption_res:                 0
% 3.59/0.99  sim_tautology_del:                      7
% 3.59/0.99  sim_eq_tautology_del:                   7
% 3.59/0.99  sim_eq_res_simp:                        1
% 3.59/0.99  sim_fw_demodulated:                     3
% 3.59/0.99  sim_bw_demodulated:                     43
% 3.59/0.99  sim_light_normalised:                   44
% 3.59/0.99  sim_joinable_taut:                      0
% 3.59/0.99  sim_joinable_simp:                      0
% 3.59/0.99  sim_ac_normalised:                      0
% 3.59/0.99  sim_smt_subsumption:                    0
% 3.59/0.99  
%------------------------------------------------------------------------------
