%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:33 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 289 expanded)
%              Number of clauses        :   80 ( 121 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  422 ( 866 expanded)
%              Number of equality atoms :  150 ( 246 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f42])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f44])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
            & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k1_relset_1(X0,X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK3,sK4,sK5))
          | ~ m1_subset_1(X3,sK4) )
      & k1_xboole_0 != k1_relset_1(sK3,sK4,sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK3,sK4,sK5))
        | ~ m1_subset_1(X3,sK4) )
    & k1_xboole_0 != k1_relset_1(sK3,sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f50])).

fof(f77,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK3,sK4,sK5))
      | ~ m1_subset_1(X3,sK4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
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

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1510,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_3497,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(sK5))
    | r1_xboole_0(X1,k1_relat_1(sK5))
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1510])).

cnf(c_6115,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(sK5))
    | r1_xboole_0(k1_relset_1(sK3,sK4,sK5),k1_relat_1(sK5))
    | k1_relset_1(sK3,sK4,sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_3497])).

cnf(c_7722,plain,
    ( r1_xboole_0(k1_relset_1(sK3,sK4,sK5),k1_relat_1(sK5))
    | ~ r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5))
    | k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_6115])).

cnf(c_1506,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6131,plain,
    ( sK2(k1_relat_1(sK5)) = sK2(k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_1509,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2948,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(k1_relat_1(sK5)),k1_relat_1(sK5))
    | X1 != k1_relat_1(sK5)
    | X0 != sK2(k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_3555,plain,
    ( r2_hidden(X0,k1_relset_1(sK3,sK4,sK5))
    | ~ r2_hidden(sK2(k1_relat_1(sK5)),k1_relat_1(sK5))
    | X0 != sK2(k1_relat_1(sK5))
    | k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2948])).

cnf(c_5232,plain,
    ( r2_hidden(sK2(k1_relat_1(sK5)),k1_relset_1(sK3,sK4,sK5))
    | ~ r2_hidden(sK2(k1_relat_1(sK5)),k1_relat_1(sK5))
    | k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5)
    | sK2(k1_relat_1(sK5)) != sK2(k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_3555])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2958,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(sK5))
    | ~ r2_hidden(sK2(k1_relat_1(sK5)),X0)
    | ~ r2_hidden(sK2(k1_relat_1(sK5)),k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5230,plain,
    ( ~ r1_xboole_0(k1_relset_1(sK3,sK4,sK5),k1_relat_1(sK5))
    | ~ r2_hidden(sK2(k1_relat_1(sK5)),k1_relset_1(sK3,sK4,sK5))
    | ~ r2_hidden(sK2(k1_relat_1(sK5)),k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2958])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2120,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2119,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2117,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4292,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2119,c_2117])).

cnf(c_5090,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(sK2(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2120,c_4292])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2104,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2106,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3001,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2104,c_2106])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2105,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2507,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k1_xboole_0
    | m1_subset_1(sK2(k2_relset_1(sK3,sK4,sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2120,c_2105])).

cnf(c_3288,plain,
    ( k2_relat_1(sK5) = k1_xboole_0
    | m1_subset_1(sK2(k2_relat_1(sK5)),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3001,c_2507])).

cnf(c_5141,plain,
    ( k2_relat_1(sK5) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5090,c_3288])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2118,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2373,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2104,c_2118])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_223,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_224,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_274,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_224])).

cnf(c_2103,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_4411,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2373,c_2103])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2114,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4438,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4411,c_2114])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2125,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2126,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2818,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2125,c_2126])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2116,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3790,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2818,c_2116])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2113,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4042,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3790,c_2113])).

cnf(c_4440,plain,
    ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_4438,c_4042])).

cnf(c_20,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2109,plain,
    ( k7_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4653,plain,
    ( sK5 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4440,c_2109])).

cnf(c_4654,plain,
    ( r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | sK5 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4653])).

cnf(c_4439,plain,
    ( v1_relat_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4438])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3351,plain,
    ( ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3355,plain,
    ( k2_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 = sK5
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3351])).

cnf(c_1507,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2643,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_3224,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2643])).

cnf(c_3225,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3224])).

cnf(c_2641,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_2534,plain,
    ( r2_hidden(sK2(k1_relat_1(sK5)),k1_relat_1(sK5))
    | k1_xboole_0 = k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2354,plain,
    ( k1_relset_1(sK3,sK4,sK5) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relset_1(sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_2441,plain,
    ( k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5)
    | k1_xboole_0 = k1_relset_1(sK3,sK4,sK5)
    | k1_xboole_0 != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2354])).

cnf(c_21,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_14,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_14])).

cnf(c_2102,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_2420,plain,
    ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2104,c_2102])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2367,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7722,c_6131,c_5232,c_5230,c_5141,c_4654,c_4439,c_4438,c_3355,c_3225,c_2641,c_2534,c_2441,c_2420,c_2367,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:42:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.12/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.01  
% 2.12/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.12/1.01  
% 2.12/1.01  ------  iProver source info
% 2.12/1.01  
% 2.12/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.12/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.12/1.01  git: non_committed_changes: false
% 2.12/1.01  git: last_make_outside_of_git: false
% 2.12/1.01  
% 2.12/1.01  ------ 
% 2.12/1.01  
% 2.12/1.01  ------ Input Options
% 2.12/1.01  
% 2.12/1.01  --out_options                           all
% 2.12/1.01  --tptp_safe_out                         true
% 2.12/1.01  --problem_path                          ""
% 2.12/1.01  --include_path                          ""
% 2.12/1.01  --clausifier                            res/vclausify_rel
% 2.12/1.01  --clausifier_options                    --mode clausify
% 2.12/1.01  --stdin                                 false
% 2.12/1.01  --stats_out                             all
% 2.12/1.01  
% 2.12/1.01  ------ General Options
% 2.12/1.01  
% 2.12/1.01  --fof                                   false
% 2.12/1.01  --time_out_real                         305.
% 2.12/1.01  --time_out_virtual                      -1.
% 2.12/1.01  --symbol_type_check                     false
% 2.12/1.01  --clausify_out                          false
% 2.12/1.01  --sig_cnt_out                           false
% 2.12/1.01  --trig_cnt_out                          false
% 2.12/1.01  --trig_cnt_out_tolerance                1.
% 2.12/1.01  --trig_cnt_out_sk_spl                   false
% 2.12/1.01  --abstr_cl_out                          false
% 2.12/1.01  
% 2.12/1.01  ------ Global Options
% 2.12/1.01  
% 2.12/1.01  --schedule                              default
% 2.12/1.01  --add_important_lit                     false
% 2.12/1.01  --prop_solver_per_cl                    1000
% 2.12/1.01  --min_unsat_core                        false
% 2.12/1.01  --soft_assumptions                      false
% 2.12/1.01  --soft_lemma_size                       3
% 2.12/1.01  --prop_impl_unit_size                   0
% 2.12/1.01  --prop_impl_unit                        []
% 2.12/1.01  --share_sel_clauses                     true
% 2.12/1.01  --reset_solvers                         false
% 2.12/1.01  --bc_imp_inh                            [conj_cone]
% 2.12/1.01  --conj_cone_tolerance                   3.
% 2.12/1.01  --extra_neg_conj                        none
% 2.12/1.01  --large_theory_mode                     true
% 2.12/1.01  --prolific_symb_bound                   200
% 2.12/1.01  --lt_threshold                          2000
% 2.12/1.01  --clause_weak_htbl                      true
% 2.12/1.01  --gc_record_bc_elim                     false
% 2.12/1.01  
% 2.12/1.01  ------ Preprocessing Options
% 2.12/1.01  
% 2.12/1.01  --preprocessing_flag                    true
% 2.12/1.01  --time_out_prep_mult                    0.1
% 2.12/1.01  --splitting_mode                        input
% 2.12/1.01  --splitting_grd                         true
% 2.12/1.01  --splitting_cvd                         false
% 2.12/1.01  --splitting_cvd_svl                     false
% 2.12/1.01  --splitting_nvd                         32
% 2.12/1.01  --sub_typing                            true
% 2.12/1.01  --prep_gs_sim                           true
% 2.12/1.01  --prep_unflatten                        true
% 2.12/1.01  --prep_res_sim                          true
% 2.12/1.01  --prep_upred                            true
% 2.12/1.01  --prep_sem_filter                       exhaustive
% 2.12/1.01  --prep_sem_filter_out                   false
% 2.12/1.01  --pred_elim                             true
% 2.12/1.01  --res_sim_input                         true
% 2.12/1.01  --eq_ax_congr_red                       true
% 2.12/1.01  --pure_diseq_elim                       true
% 2.12/1.01  --brand_transform                       false
% 2.12/1.01  --non_eq_to_eq                          false
% 2.12/1.01  --prep_def_merge                        true
% 2.12/1.01  --prep_def_merge_prop_impl              false
% 2.12/1.01  --prep_def_merge_mbd                    true
% 2.12/1.01  --prep_def_merge_tr_red                 false
% 2.12/1.01  --prep_def_merge_tr_cl                  false
% 2.12/1.01  --smt_preprocessing                     true
% 2.12/1.01  --smt_ac_axioms                         fast
% 2.12/1.01  --preprocessed_out                      false
% 2.12/1.01  --preprocessed_stats                    false
% 2.12/1.01  
% 2.12/1.01  ------ Abstraction refinement Options
% 2.12/1.01  
% 2.12/1.01  --abstr_ref                             []
% 2.12/1.01  --abstr_ref_prep                        false
% 2.12/1.01  --abstr_ref_until_sat                   false
% 2.12/1.01  --abstr_ref_sig_restrict                funpre
% 2.12/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.12/1.01  --abstr_ref_under                       []
% 2.12/1.01  
% 2.12/1.01  ------ SAT Options
% 2.12/1.01  
% 2.12/1.01  --sat_mode                              false
% 2.12/1.01  --sat_fm_restart_options                ""
% 2.12/1.01  --sat_gr_def                            false
% 2.12/1.01  --sat_epr_types                         true
% 2.12/1.01  --sat_non_cyclic_types                  false
% 2.12/1.01  --sat_finite_models                     false
% 2.12/1.01  --sat_fm_lemmas                         false
% 2.12/1.01  --sat_fm_prep                           false
% 2.12/1.01  --sat_fm_uc_incr                        true
% 2.12/1.01  --sat_out_model                         small
% 2.12/1.01  --sat_out_clauses                       false
% 2.12/1.01  
% 2.12/1.01  ------ QBF Options
% 2.12/1.01  
% 2.12/1.01  --qbf_mode                              false
% 2.12/1.01  --qbf_elim_univ                         false
% 2.12/1.01  --qbf_dom_inst                          none
% 2.12/1.01  --qbf_dom_pre_inst                      false
% 2.12/1.01  --qbf_sk_in                             false
% 2.12/1.01  --qbf_pred_elim                         true
% 2.12/1.01  --qbf_split                             512
% 2.12/1.01  
% 2.12/1.01  ------ BMC1 Options
% 2.12/1.01  
% 2.12/1.01  --bmc1_incremental                      false
% 2.12/1.01  --bmc1_axioms                           reachable_all
% 2.12/1.01  --bmc1_min_bound                        0
% 2.12/1.01  --bmc1_max_bound                        -1
% 2.12/1.01  --bmc1_max_bound_default                -1
% 2.12/1.01  --bmc1_symbol_reachability              true
% 2.12/1.01  --bmc1_property_lemmas                  false
% 2.12/1.01  --bmc1_k_induction                      false
% 2.12/1.01  --bmc1_non_equiv_states                 false
% 2.12/1.01  --bmc1_deadlock                         false
% 2.12/1.01  --bmc1_ucm                              false
% 2.12/1.01  --bmc1_add_unsat_core                   none
% 2.12/1.01  --bmc1_unsat_core_children              false
% 2.12/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.12/1.01  --bmc1_out_stat                         full
% 2.12/1.01  --bmc1_ground_init                      false
% 2.12/1.01  --bmc1_pre_inst_next_state              false
% 2.12/1.01  --bmc1_pre_inst_state                   false
% 2.12/1.01  --bmc1_pre_inst_reach_state             false
% 2.12/1.01  --bmc1_out_unsat_core                   false
% 2.12/1.01  --bmc1_aig_witness_out                  false
% 2.12/1.01  --bmc1_verbose                          false
% 2.12/1.01  --bmc1_dump_clauses_tptp                false
% 2.12/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.12/1.01  --bmc1_dump_file                        -
% 2.12/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.12/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.12/1.01  --bmc1_ucm_extend_mode                  1
% 2.12/1.01  --bmc1_ucm_init_mode                    2
% 2.12/1.01  --bmc1_ucm_cone_mode                    none
% 2.12/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.12/1.01  --bmc1_ucm_relax_model                  4
% 2.12/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.12/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.12/1.01  --bmc1_ucm_layered_model                none
% 2.12/1.01  --bmc1_ucm_max_lemma_size               10
% 2.12/1.01  
% 2.12/1.01  ------ AIG Options
% 2.12/1.01  
% 2.12/1.01  --aig_mode                              false
% 2.12/1.01  
% 2.12/1.01  ------ Instantiation Options
% 2.12/1.01  
% 2.12/1.01  --instantiation_flag                    true
% 2.12/1.01  --inst_sos_flag                         false
% 2.12/1.01  --inst_sos_phase                        true
% 2.12/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.12/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.12/1.01  --inst_lit_sel_side                     num_symb
% 2.12/1.01  --inst_solver_per_active                1400
% 2.12/1.01  --inst_solver_calls_frac                1.
% 2.12/1.01  --inst_passive_queue_type               priority_queues
% 2.12/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.12/1.01  --inst_passive_queues_freq              [25;2]
% 2.12/1.01  --inst_dismatching                      true
% 2.12/1.01  --inst_eager_unprocessed_to_passive     true
% 2.12/1.01  --inst_prop_sim_given                   true
% 2.12/1.01  --inst_prop_sim_new                     false
% 2.12/1.01  --inst_subs_new                         false
% 2.12/1.01  --inst_eq_res_simp                      false
% 2.12/1.01  --inst_subs_given                       false
% 2.12/1.01  --inst_orphan_elimination               true
% 2.12/1.01  --inst_learning_loop_flag               true
% 2.12/1.01  --inst_learning_start                   3000
% 2.12/1.01  --inst_learning_factor                  2
% 2.12/1.01  --inst_start_prop_sim_after_learn       3
% 2.12/1.01  --inst_sel_renew                        solver
% 2.12/1.01  --inst_lit_activity_flag                true
% 2.12/1.01  --inst_restr_to_given                   false
% 2.12/1.01  --inst_activity_threshold               500
% 2.12/1.01  --inst_out_proof                        true
% 2.12/1.01  
% 2.12/1.01  ------ Resolution Options
% 2.12/1.01  
% 2.12/1.01  --resolution_flag                       true
% 2.12/1.01  --res_lit_sel                           adaptive
% 2.12/1.01  --res_lit_sel_side                      none
% 2.12/1.01  --res_ordering                          kbo
% 2.12/1.01  --res_to_prop_solver                    active
% 2.12/1.01  --res_prop_simpl_new                    false
% 2.12/1.01  --res_prop_simpl_given                  true
% 2.12/1.01  --res_passive_queue_type                priority_queues
% 2.12/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.12/1.01  --res_passive_queues_freq               [15;5]
% 2.12/1.01  --res_forward_subs                      full
% 2.12/1.01  --res_backward_subs                     full
% 2.12/1.01  --res_forward_subs_resolution           true
% 2.12/1.01  --res_backward_subs_resolution          true
% 2.12/1.01  --res_orphan_elimination                true
% 2.12/1.01  --res_time_limit                        2.
% 2.12/1.01  --res_out_proof                         true
% 2.12/1.01  
% 2.12/1.01  ------ Superposition Options
% 2.12/1.01  
% 2.12/1.01  --superposition_flag                    true
% 2.12/1.01  --sup_passive_queue_type                priority_queues
% 2.12/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.12/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.12/1.01  --demod_completeness_check              fast
% 2.12/1.01  --demod_use_ground                      true
% 2.12/1.01  --sup_to_prop_solver                    passive
% 2.12/1.01  --sup_prop_simpl_new                    true
% 2.12/1.01  --sup_prop_simpl_given                  true
% 2.12/1.01  --sup_fun_splitting                     false
% 2.12/1.01  --sup_smt_interval                      50000
% 2.12/1.01  
% 2.12/1.01  ------ Superposition Simplification Setup
% 2.12/1.01  
% 2.12/1.01  --sup_indices_passive                   []
% 2.12/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.12/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/1.01  --sup_full_bw                           [BwDemod]
% 2.12/1.01  --sup_immed_triv                        [TrivRules]
% 2.12/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.12/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/1.01  --sup_immed_bw_main                     []
% 2.12/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.12/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.12/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.12/1.01  
% 2.12/1.01  ------ Combination Options
% 2.12/1.01  
% 2.12/1.01  --comb_res_mult                         3
% 2.12/1.01  --comb_sup_mult                         2
% 2.12/1.01  --comb_inst_mult                        10
% 2.12/1.01  
% 2.12/1.01  ------ Debug Options
% 2.12/1.01  
% 2.12/1.01  --dbg_backtrace                         false
% 2.12/1.01  --dbg_dump_prop_clauses                 false
% 2.12/1.01  --dbg_dump_prop_clauses_file            -
% 2.12/1.01  --dbg_out_stat                          false
% 2.12/1.01  ------ Parsing...
% 2.12/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.12/1.01  
% 2.12/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.12/1.01  
% 2.12/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.12/1.01  
% 2.12/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.12/1.01  ------ Proving...
% 2.12/1.01  ------ Problem Properties 
% 2.12/1.01  
% 2.12/1.01  
% 2.12/1.01  clauses                                 26
% 2.12/1.01  conjectures                             3
% 2.12/1.01  EPR                                     3
% 2.12/1.01  Horn                                    22
% 2.12/1.01  unary                                   3
% 2.12/1.01  binary                                  11
% 2.12/1.01  lits                                    61
% 2.12/1.01  lits eq                                 11
% 2.12/1.01  fd_pure                                 0
% 2.12/1.01  fd_pseudo                               0
% 2.12/1.01  fd_cond                                 3
% 2.12/1.01  fd_pseudo_cond                          0
% 2.12/1.01  AC symbols                              0
% 2.12/1.01  
% 2.12/1.01  ------ Schedule dynamic 5 is on 
% 2.12/1.01  
% 2.12/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.12/1.01  
% 2.12/1.01  
% 2.12/1.01  ------ 
% 2.12/1.01  Current options:
% 2.12/1.01  ------ 
% 2.12/1.01  
% 2.12/1.01  ------ Input Options
% 2.12/1.01  
% 2.12/1.01  --out_options                           all
% 2.12/1.01  --tptp_safe_out                         true
% 2.12/1.01  --problem_path                          ""
% 2.12/1.01  --include_path                          ""
% 2.12/1.01  --clausifier                            res/vclausify_rel
% 2.12/1.01  --clausifier_options                    --mode clausify
% 2.12/1.01  --stdin                                 false
% 2.12/1.01  --stats_out                             all
% 2.12/1.01  
% 2.12/1.01  ------ General Options
% 2.12/1.01  
% 2.12/1.01  --fof                                   false
% 2.12/1.01  --time_out_real                         305.
% 2.12/1.01  --time_out_virtual                      -1.
% 2.12/1.01  --symbol_type_check                     false
% 2.12/1.01  --clausify_out                          false
% 2.12/1.01  --sig_cnt_out                           false
% 2.12/1.01  --trig_cnt_out                          false
% 2.12/1.01  --trig_cnt_out_tolerance                1.
% 2.12/1.01  --trig_cnt_out_sk_spl                   false
% 2.12/1.01  --abstr_cl_out                          false
% 2.12/1.01  
% 2.12/1.01  ------ Global Options
% 2.12/1.01  
% 2.12/1.01  --schedule                              default
% 2.12/1.01  --add_important_lit                     false
% 2.12/1.01  --prop_solver_per_cl                    1000
% 2.12/1.01  --min_unsat_core                        false
% 2.12/1.01  --soft_assumptions                      false
% 2.12/1.01  --soft_lemma_size                       3
% 2.12/1.01  --prop_impl_unit_size                   0
% 2.12/1.01  --prop_impl_unit                        []
% 2.12/1.01  --share_sel_clauses                     true
% 2.12/1.01  --reset_solvers                         false
% 2.12/1.01  --bc_imp_inh                            [conj_cone]
% 2.12/1.01  --conj_cone_tolerance                   3.
% 2.12/1.01  --extra_neg_conj                        none
% 2.12/1.01  --large_theory_mode                     true
% 2.12/1.01  --prolific_symb_bound                   200
% 2.12/1.01  --lt_threshold                          2000
% 2.12/1.01  --clause_weak_htbl                      true
% 2.12/1.01  --gc_record_bc_elim                     false
% 2.12/1.01  
% 2.12/1.01  ------ Preprocessing Options
% 2.12/1.01  
% 2.12/1.01  --preprocessing_flag                    true
% 2.12/1.01  --time_out_prep_mult                    0.1
% 2.12/1.01  --splitting_mode                        input
% 2.12/1.01  --splitting_grd                         true
% 2.12/1.01  --splitting_cvd                         false
% 2.12/1.01  --splitting_cvd_svl                     false
% 2.12/1.01  --splitting_nvd                         32
% 2.12/1.01  --sub_typing                            true
% 2.12/1.01  --prep_gs_sim                           true
% 2.12/1.01  --prep_unflatten                        true
% 2.12/1.01  --prep_res_sim                          true
% 2.12/1.01  --prep_upred                            true
% 2.12/1.01  --prep_sem_filter                       exhaustive
% 2.12/1.01  --prep_sem_filter_out                   false
% 2.12/1.01  --pred_elim                             true
% 2.12/1.01  --res_sim_input                         true
% 2.12/1.01  --eq_ax_congr_red                       true
% 2.12/1.01  --pure_diseq_elim                       true
% 2.12/1.01  --brand_transform                       false
% 2.12/1.01  --non_eq_to_eq                          false
% 2.12/1.01  --prep_def_merge                        true
% 2.12/1.01  --prep_def_merge_prop_impl              false
% 2.12/1.01  --prep_def_merge_mbd                    true
% 2.12/1.01  --prep_def_merge_tr_red                 false
% 2.12/1.01  --prep_def_merge_tr_cl                  false
% 2.12/1.01  --smt_preprocessing                     true
% 2.12/1.01  --smt_ac_axioms                         fast
% 2.12/1.01  --preprocessed_out                      false
% 2.12/1.01  --preprocessed_stats                    false
% 2.12/1.01  
% 2.12/1.01  ------ Abstraction refinement Options
% 2.12/1.01  
% 2.12/1.01  --abstr_ref                             []
% 2.12/1.01  --abstr_ref_prep                        false
% 2.12/1.01  --abstr_ref_until_sat                   false
% 2.12/1.01  --abstr_ref_sig_restrict                funpre
% 2.12/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.12/1.01  --abstr_ref_under                       []
% 2.12/1.01  
% 2.12/1.01  ------ SAT Options
% 2.12/1.01  
% 2.12/1.01  --sat_mode                              false
% 2.12/1.01  --sat_fm_restart_options                ""
% 2.12/1.01  --sat_gr_def                            false
% 2.12/1.01  --sat_epr_types                         true
% 2.12/1.01  --sat_non_cyclic_types                  false
% 2.12/1.01  --sat_finite_models                     false
% 2.12/1.01  --sat_fm_lemmas                         false
% 2.12/1.01  --sat_fm_prep                           false
% 2.12/1.01  --sat_fm_uc_incr                        true
% 2.12/1.01  --sat_out_model                         small
% 2.12/1.01  --sat_out_clauses                       false
% 2.12/1.01  
% 2.12/1.01  ------ QBF Options
% 2.12/1.01  
% 2.12/1.01  --qbf_mode                              false
% 2.12/1.01  --qbf_elim_univ                         false
% 2.12/1.01  --qbf_dom_inst                          none
% 2.12/1.01  --qbf_dom_pre_inst                      false
% 2.12/1.01  --qbf_sk_in                             false
% 2.12/1.01  --qbf_pred_elim                         true
% 2.12/1.01  --qbf_split                             512
% 2.12/1.01  
% 2.12/1.01  ------ BMC1 Options
% 2.12/1.01  
% 2.12/1.01  --bmc1_incremental                      false
% 2.12/1.01  --bmc1_axioms                           reachable_all
% 2.12/1.01  --bmc1_min_bound                        0
% 2.12/1.01  --bmc1_max_bound                        -1
% 2.12/1.01  --bmc1_max_bound_default                -1
% 2.12/1.01  --bmc1_symbol_reachability              true
% 2.12/1.01  --bmc1_property_lemmas                  false
% 2.12/1.01  --bmc1_k_induction                      false
% 2.12/1.01  --bmc1_non_equiv_states                 false
% 2.12/1.01  --bmc1_deadlock                         false
% 2.12/1.01  --bmc1_ucm                              false
% 2.12/1.01  --bmc1_add_unsat_core                   none
% 2.12/1.01  --bmc1_unsat_core_children              false
% 2.12/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.12/1.01  --bmc1_out_stat                         full
% 2.12/1.01  --bmc1_ground_init                      false
% 2.12/1.01  --bmc1_pre_inst_next_state              false
% 2.12/1.01  --bmc1_pre_inst_state                   false
% 2.12/1.01  --bmc1_pre_inst_reach_state             false
% 2.12/1.01  --bmc1_out_unsat_core                   false
% 2.12/1.01  --bmc1_aig_witness_out                  false
% 2.12/1.01  --bmc1_verbose                          false
% 2.12/1.01  --bmc1_dump_clauses_tptp                false
% 2.12/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.12/1.01  --bmc1_dump_file                        -
% 2.12/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.12/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.12/1.01  --bmc1_ucm_extend_mode                  1
% 2.12/1.01  --bmc1_ucm_init_mode                    2
% 2.12/1.01  --bmc1_ucm_cone_mode                    none
% 2.12/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.12/1.01  --bmc1_ucm_relax_model                  4
% 2.12/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.12/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.12/1.01  --bmc1_ucm_layered_model                none
% 2.12/1.01  --bmc1_ucm_max_lemma_size               10
% 2.12/1.01  
% 2.12/1.01  ------ AIG Options
% 2.12/1.01  
% 2.12/1.01  --aig_mode                              false
% 2.12/1.01  
% 2.12/1.01  ------ Instantiation Options
% 2.12/1.01  
% 2.12/1.01  --instantiation_flag                    true
% 2.12/1.01  --inst_sos_flag                         false
% 2.12/1.01  --inst_sos_phase                        true
% 2.12/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.12/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.12/1.01  --inst_lit_sel_side                     none
% 2.12/1.01  --inst_solver_per_active                1400
% 2.12/1.01  --inst_solver_calls_frac                1.
% 2.12/1.01  --inst_passive_queue_type               priority_queues
% 2.12/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.12/1.01  --inst_passive_queues_freq              [25;2]
% 2.12/1.01  --inst_dismatching                      true
% 2.12/1.01  --inst_eager_unprocessed_to_passive     true
% 2.12/1.01  --inst_prop_sim_given                   true
% 2.12/1.01  --inst_prop_sim_new                     false
% 2.12/1.01  --inst_subs_new                         false
% 2.12/1.01  --inst_eq_res_simp                      false
% 2.12/1.01  --inst_subs_given                       false
% 2.12/1.01  --inst_orphan_elimination               true
% 2.12/1.01  --inst_learning_loop_flag               true
% 2.12/1.01  --inst_learning_start                   3000
% 2.12/1.01  --inst_learning_factor                  2
% 2.12/1.01  --inst_start_prop_sim_after_learn       3
% 2.12/1.01  --inst_sel_renew                        solver
% 2.12/1.01  --inst_lit_activity_flag                true
% 2.12/1.01  --inst_restr_to_given                   false
% 2.12/1.01  --inst_activity_threshold               500
% 2.12/1.01  --inst_out_proof                        true
% 2.12/1.01  
% 2.12/1.01  ------ Resolution Options
% 2.12/1.01  
% 2.12/1.01  --resolution_flag                       false
% 2.12/1.01  --res_lit_sel                           adaptive
% 2.12/1.01  --res_lit_sel_side                      none
% 2.12/1.01  --res_ordering                          kbo
% 2.12/1.01  --res_to_prop_solver                    active
% 2.12/1.01  --res_prop_simpl_new                    false
% 2.12/1.01  --res_prop_simpl_given                  true
% 2.12/1.01  --res_passive_queue_type                priority_queues
% 2.12/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.12/1.01  --res_passive_queues_freq               [15;5]
% 2.12/1.01  --res_forward_subs                      full
% 2.12/1.01  --res_backward_subs                     full
% 2.12/1.01  --res_forward_subs_resolution           true
% 2.12/1.01  --res_backward_subs_resolution          true
% 2.12/1.01  --res_orphan_elimination                true
% 2.12/1.01  --res_time_limit                        2.
% 2.12/1.01  --res_out_proof                         true
% 2.12/1.01  
% 2.12/1.01  ------ Superposition Options
% 2.12/1.01  
% 2.12/1.01  --superposition_flag                    true
% 2.12/1.01  --sup_passive_queue_type                priority_queues
% 2.12/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.12/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.12/1.01  --demod_completeness_check              fast
% 2.12/1.01  --demod_use_ground                      true
% 2.12/1.01  --sup_to_prop_solver                    passive
% 2.12/1.01  --sup_prop_simpl_new                    true
% 2.12/1.01  --sup_prop_simpl_given                  true
% 2.12/1.01  --sup_fun_splitting                     false
% 2.12/1.01  --sup_smt_interval                      50000
% 2.12/1.01  
% 2.12/1.01  ------ Superposition Simplification Setup
% 2.12/1.01  
% 2.12/1.01  --sup_indices_passive                   []
% 2.12/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.12/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.12/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/1.01  --sup_full_bw                           [BwDemod]
% 2.12/1.01  --sup_immed_triv                        [TrivRules]
% 2.12/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.12/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/1.01  --sup_immed_bw_main                     []
% 2.12/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.12/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.12/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.12/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.12/1.01  
% 2.12/1.01  ------ Combination Options
% 2.12/1.01  
% 2.12/1.01  --comb_res_mult                         3
% 2.12/1.01  --comb_sup_mult                         2
% 2.12/1.01  --comb_inst_mult                        10
% 2.12/1.01  
% 2.12/1.01  ------ Debug Options
% 2.12/1.01  
% 2.12/1.01  --dbg_backtrace                         false
% 2.12/1.01  --dbg_dump_prop_clauses                 false
% 2.12/1.01  --dbg_dump_prop_clauses_file            -
% 2.12/1.01  --dbg_out_stat                          false
% 2.12/1.01  
% 2.12/1.01  
% 2.12/1.01  
% 2.12/1.01  
% 2.12/1.01  ------ Proving...
% 2.12/1.01  
% 2.12/1.01  
% 2.12/1.01  % SZS status Theorem for theBenchmark.p
% 2.12/1.01  
% 2.12/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.12/1.01  
% 2.12/1.01  fof(f2,axiom,(
% 2.12/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f18,plain,(
% 2.12/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.12/1.01    inference(rectify,[],[f2])).
% 2.12/1.01  
% 2.12/1.01  fof(f21,plain,(
% 2.12/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.12/1.01    inference(ennf_transformation,[],[f18])).
% 2.12/1.01  
% 2.12/1.01  fof(f42,plain,(
% 2.12/1.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.12/1.01    introduced(choice_axiom,[])).
% 2.12/1.01  
% 2.12/1.01  fof(f43,plain,(
% 2.12/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.12/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f42])).
% 2.12/1.01  
% 2.12/1.01  fof(f57,plain,(
% 2.12/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.12/1.01    inference(cnf_transformation,[],[f43])).
% 2.12/1.01  
% 2.12/1.01  fof(f3,axiom,(
% 2.12/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f22,plain,(
% 2.12/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.12/1.01    inference(ennf_transformation,[],[f3])).
% 2.12/1.01  
% 2.12/1.01  fof(f44,plain,(
% 2.12/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.12/1.01    introduced(choice_axiom,[])).
% 2.12/1.01  
% 2.12/1.01  fof(f45,plain,(
% 2.12/1.01    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.12/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f44])).
% 2.12/1.01  
% 2.12/1.01  fof(f58,plain,(
% 2.12/1.01    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.12/1.01    inference(cnf_transformation,[],[f45])).
% 2.12/1.01  
% 2.12/1.01  fof(f4,axiom,(
% 2.12/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f46,plain,(
% 2.12/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.12/1.01    inference(nnf_transformation,[],[f4])).
% 2.12/1.01  
% 2.12/1.01  fof(f60,plain,(
% 2.12/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.12/1.01    inference(cnf_transformation,[],[f46])).
% 2.12/1.01  
% 2.12/1.01  fof(f5,axiom,(
% 2.12/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f23,plain,(
% 2.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.12/1.01    inference(ennf_transformation,[],[f5])).
% 2.12/1.01  
% 2.12/1.01  fof(f24,plain,(
% 2.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.12/1.01    inference(flattening,[],[f23])).
% 2.12/1.01  
% 2.12/1.01  fof(f61,plain,(
% 2.12/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.12/1.01    inference(cnf_transformation,[],[f24])).
% 2.12/1.01  
% 2.12/1.01  fof(f16,conjecture,(
% 2.12/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f17,negated_conjecture,(
% 2.12/1.01    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 2.12/1.01    inference(negated_conjecture,[],[f16])).
% 2.12/1.01  
% 2.12/1.01  fof(f19,plain,(
% 2.12/1.01    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))),
% 2.12/1.01    inference(pure_predicate_removal,[],[f17])).
% 2.12/1.01  
% 2.12/1.01  fof(f36,plain,(
% 2.12/1.01    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/1.01    inference(ennf_transformation,[],[f19])).
% 2.12/1.01  
% 2.12/1.01  fof(f37,plain,(
% 2.12/1.01    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/1.01    inference(flattening,[],[f36])).
% 2.12/1.01  
% 2.12/1.01  fof(f50,plain,(
% 2.12/1.01    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK3,sK4,sK5)) | ~m1_subset_1(X3,sK4)) & k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))))),
% 2.12/1.01    introduced(choice_axiom,[])).
% 2.12/1.01  
% 2.12/1.01  fof(f51,plain,(
% 2.12/1.01    ! [X3] : (~r2_hidden(X3,k2_relset_1(sK3,sK4,sK5)) | ~m1_subset_1(X3,sK4)) & k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.12/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f50])).
% 2.12/1.01  
% 2.12/1.01  fof(f77,plain,(
% 2.12/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.12/1.01    inference(cnf_transformation,[],[f51])).
% 2.12/1.01  
% 2.12/1.01  fof(f15,axiom,(
% 2.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f35,plain,(
% 2.12/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/1.01    inference(ennf_transformation,[],[f15])).
% 2.12/1.01  
% 2.12/1.01  fof(f76,plain,(
% 2.12/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.12/1.01    inference(cnf_transformation,[],[f35])).
% 2.12/1.01  
% 2.12/1.01  fof(f79,plain,(
% 2.12/1.01    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK3,sK4,sK5)) | ~m1_subset_1(X3,sK4)) )),
% 2.12/1.01    inference(cnf_transformation,[],[f51])).
% 2.12/1.01  
% 2.12/1.01  fof(f59,plain,(
% 2.12/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.12/1.01    inference(cnf_transformation,[],[f46])).
% 2.12/1.01  
% 2.12/1.01  fof(f6,axiom,(
% 2.12/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f25,plain,(
% 2.12/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.12/1.01    inference(ennf_transformation,[],[f6])).
% 2.12/1.01  
% 2.12/1.01  fof(f62,plain,(
% 2.12/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.12/1.01    inference(cnf_transformation,[],[f25])).
% 2.12/1.01  
% 2.12/1.01  fof(f9,axiom,(
% 2.12/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f67,plain,(
% 2.12/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.12/1.01    inference(cnf_transformation,[],[f9])).
% 2.12/1.01  
% 2.12/1.01  fof(f1,axiom,(
% 2.12/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f20,plain,(
% 2.12/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.12/1.01    inference(ennf_transformation,[],[f1])).
% 2.12/1.01  
% 2.12/1.01  fof(f38,plain,(
% 2.12/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.12/1.01    inference(nnf_transformation,[],[f20])).
% 2.12/1.01  
% 2.12/1.01  fof(f39,plain,(
% 2.12/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.12/1.01    inference(rectify,[],[f38])).
% 2.12/1.01  
% 2.12/1.01  fof(f40,plain,(
% 2.12/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.12/1.01    introduced(choice_axiom,[])).
% 2.12/1.01  
% 2.12/1.01  fof(f41,plain,(
% 2.12/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.12/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 2.12/1.01  
% 2.12/1.01  fof(f53,plain,(
% 2.12/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.12/1.01    inference(cnf_transformation,[],[f41])).
% 2.12/1.01  
% 2.12/1.01  fof(f54,plain,(
% 2.12/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.12/1.01    inference(cnf_transformation,[],[f41])).
% 2.12/1.01  
% 2.12/1.01  fof(f7,axiom,(
% 2.12/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f26,plain,(
% 2.12/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.12/1.01    inference(ennf_transformation,[],[f7])).
% 2.12/1.01  
% 2.12/1.01  fof(f47,plain,(
% 2.12/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.12/1.01    inference(nnf_transformation,[],[f26])).
% 2.12/1.01  
% 2.12/1.01  fof(f64,plain,(
% 2.12/1.01    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.12/1.01    inference(cnf_transformation,[],[f47])).
% 2.12/1.01  
% 2.12/1.01  fof(f10,axiom,(
% 2.12/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f28,plain,(
% 2.12/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.12/1.01    inference(ennf_transformation,[],[f10])).
% 2.12/1.01  
% 2.12/1.01  fof(f29,plain,(
% 2.12/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.12/1.01    inference(flattening,[],[f28])).
% 2.12/1.01  
% 2.12/1.01  fof(f68,plain,(
% 2.12/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.12/1.01    inference(cnf_transformation,[],[f29])).
% 2.12/1.01  
% 2.12/1.01  fof(f12,axiom,(
% 2.12/1.01    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f32,plain,(
% 2.12/1.01    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.12/1.01    inference(ennf_transformation,[],[f12])).
% 2.12/1.01  
% 2.12/1.01  fof(f49,plain,(
% 2.12/1.01    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.12/1.01    inference(nnf_transformation,[],[f32])).
% 2.12/1.01  
% 2.12/1.01  fof(f71,plain,(
% 2.12/1.01    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.12/1.01    inference(cnf_transformation,[],[f49])).
% 2.12/1.01  
% 2.12/1.01  fof(f11,axiom,(
% 2.12/1.01    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f30,plain,(
% 2.12/1.01    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.12/1.01    inference(ennf_transformation,[],[f11])).
% 2.12/1.01  
% 2.12/1.01  fof(f31,plain,(
% 2.12/1.01    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.12/1.01    inference(flattening,[],[f30])).
% 2.12/1.01  
% 2.12/1.01  fof(f70,plain,(
% 2.12/1.01    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.12/1.01    inference(cnf_transformation,[],[f31])).
% 2.12/1.01  
% 2.12/1.01  fof(f13,axiom,(
% 2.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f33,plain,(
% 2.12/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/1.01    inference(ennf_transformation,[],[f13])).
% 2.12/1.01  
% 2.12/1.01  fof(f74,plain,(
% 2.12/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.12/1.01    inference(cnf_transformation,[],[f33])).
% 2.12/1.01  
% 2.12/1.01  fof(f8,axiom,(
% 2.12/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f27,plain,(
% 2.12/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.12/1.01    inference(ennf_transformation,[],[f8])).
% 2.12/1.01  
% 2.12/1.01  fof(f48,plain,(
% 2.12/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.12/1.01    inference(nnf_transformation,[],[f27])).
% 2.12/1.01  
% 2.12/1.01  fof(f65,plain,(
% 2.12/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.12/1.01    inference(cnf_transformation,[],[f48])).
% 2.12/1.01  
% 2.12/1.01  fof(f14,axiom,(
% 2.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.12/1.01  
% 2.12/1.01  fof(f34,plain,(
% 2.12/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.12/1.01    inference(ennf_transformation,[],[f14])).
% 2.12/1.01  
% 2.12/1.01  fof(f75,plain,(
% 2.12/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.12/1.01    inference(cnf_transformation,[],[f34])).
% 2.12/1.01  
% 2.12/1.01  fof(f78,plain,(
% 2.12/1.01    k1_xboole_0 != k1_relset_1(sK3,sK4,sK5)),
% 2.12/1.01    inference(cnf_transformation,[],[f51])).
% 2.12/1.01  
% 2.12/1.01  cnf(c_1510,plain,
% 2.12/1.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 2.12/1.01      theory(equality) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_3497,plain,
% 2.12/1.01      ( ~ r1_xboole_0(X0,k1_relat_1(sK5))
% 2.12/1.01      | r1_xboole_0(X1,k1_relat_1(sK5))
% 2.12/1.01      | X1 != X0 ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_1510]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_6115,plain,
% 2.12/1.01      ( ~ r1_xboole_0(X0,k1_relat_1(sK5))
% 2.12/1.01      | r1_xboole_0(k1_relset_1(sK3,sK4,sK5),k1_relat_1(sK5))
% 2.12/1.01      | k1_relset_1(sK3,sK4,sK5) != X0 ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_3497]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_7722,plain,
% 2.12/1.01      ( r1_xboole_0(k1_relset_1(sK3,sK4,sK5),k1_relat_1(sK5))
% 2.12/1.01      | ~ r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5))
% 2.12/1.01      | k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5) ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_6115]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_1506,plain,( X0 = X0 ),theory(equality) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_6131,plain,
% 2.12/1.01      ( sK2(k1_relat_1(sK5)) = sK2(k1_relat_1(sK5)) ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_1506]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_1509,plain,
% 2.12/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.12/1.01      theory(equality) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2948,plain,
% 2.12/1.01      ( r2_hidden(X0,X1)
% 2.12/1.01      | ~ r2_hidden(sK2(k1_relat_1(sK5)),k1_relat_1(sK5))
% 2.12/1.01      | X1 != k1_relat_1(sK5)
% 2.12/1.01      | X0 != sK2(k1_relat_1(sK5)) ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_1509]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_3555,plain,
% 2.12/1.01      ( r2_hidden(X0,k1_relset_1(sK3,sK4,sK5))
% 2.12/1.01      | ~ r2_hidden(sK2(k1_relat_1(sK5)),k1_relat_1(sK5))
% 2.12/1.01      | X0 != sK2(k1_relat_1(sK5))
% 2.12/1.01      | k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5) ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_2948]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_5232,plain,
% 2.12/1.01      ( r2_hidden(sK2(k1_relat_1(sK5)),k1_relset_1(sK3,sK4,sK5))
% 2.12/1.01      | ~ r2_hidden(sK2(k1_relat_1(sK5)),k1_relat_1(sK5))
% 2.12/1.01      | k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5)
% 2.12/1.01      | sK2(k1_relat_1(sK5)) != sK2(k1_relat_1(sK5)) ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_3555]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_3,plain,
% 2.12/1.01      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 2.12/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2958,plain,
% 2.12/1.01      ( ~ r1_xboole_0(X0,k1_relat_1(sK5))
% 2.12/1.01      | ~ r2_hidden(sK2(k1_relat_1(sK5)),X0)
% 2.12/1.01      | ~ r2_hidden(sK2(k1_relat_1(sK5)),k1_relat_1(sK5)) ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_5230,plain,
% 2.12/1.01      ( ~ r1_xboole_0(k1_relset_1(sK3,sK4,sK5),k1_relat_1(sK5))
% 2.12/1.01      | ~ r2_hidden(sK2(k1_relat_1(sK5)),k1_relset_1(sK3,sK4,sK5))
% 2.12/1.01      | ~ r2_hidden(sK2(k1_relat_1(sK5)),k1_relat_1(sK5)) ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_2958]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_6,plain,
% 2.12/1.01      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.12/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2120,plain,
% 2.12/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_7,plain,
% 2.12/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.12/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2119,plain,
% 2.12/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.12/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_9,plain,
% 2.12/1.01      ( m1_subset_1(X0,X1)
% 2.12/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.12/1.01      | ~ r2_hidden(X0,X2) ),
% 2.12/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2117,plain,
% 2.12/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.12/1.01      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.12/1.01      | r2_hidden(X0,X2) != iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_4292,plain,
% 2.12/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.12/1.01      | r2_hidden(X0,X2) != iProver_top
% 2.12/1.01      | r1_tarski(X2,X1) != iProver_top ),
% 2.12/1.01      inference(superposition,[status(thm)],[c_2119,c_2117]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_5090,plain,
% 2.12/1.01      ( k1_xboole_0 = X0
% 2.12/1.01      | m1_subset_1(sK2(X0),X1) = iProver_top
% 2.12/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.12/1.01      inference(superposition,[status(thm)],[c_2120,c_4292]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_27,negated_conjecture,
% 2.12/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.12/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2104,plain,
% 2.12/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_24,plain,
% 2.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.12/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2106,plain,
% 2.12/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.12/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_3001,plain,
% 2.12/1.01      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 2.12/1.01      inference(superposition,[status(thm)],[c_2104,c_2106]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_25,negated_conjecture,
% 2.12/1.01      ( ~ m1_subset_1(X0,sK4)
% 2.12/1.01      | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) ),
% 2.12/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2105,plain,
% 2.12/1.01      ( m1_subset_1(X0,sK4) != iProver_top
% 2.12/1.01      | r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2507,plain,
% 2.12/1.01      ( k2_relset_1(sK3,sK4,sK5) = k1_xboole_0
% 2.12/1.01      | m1_subset_1(sK2(k2_relset_1(sK3,sK4,sK5)),sK4) != iProver_top ),
% 2.12/1.01      inference(superposition,[status(thm)],[c_2120,c_2105]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_3288,plain,
% 2.12/1.01      ( k2_relat_1(sK5) = k1_xboole_0
% 2.12/1.01      | m1_subset_1(sK2(k2_relat_1(sK5)),sK4) != iProver_top ),
% 2.12/1.01      inference(demodulation,[status(thm)],[c_3001,c_2507]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_5141,plain,
% 2.12/1.01      ( k2_relat_1(sK5) = k1_xboole_0
% 2.12/1.01      | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top ),
% 2.12/1.01      inference(superposition,[status(thm)],[c_5090,c_3288]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_8,plain,
% 2.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.12/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2118,plain,
% 2.12/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.12/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2373,plain,
% 2.12/1.01      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 2.12/1.01      inference(superposition,[status(thm)],[c_2104,c_2118]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_10,plain,
% 2.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.12/1.01      | ~ v1_relat_1(X1)
% 2.12/1.01      | v1_relat_1(X0) ),
% 2.12/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_223,plain,
% 2.12/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.12/1.01      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_224,plain,
% 2.12/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.12/1.01      inference(renaming,[status(thm)],[c_223]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_274,plain,
% 2.12/1.01      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.12/1.01      inference(bin_hyper_res,[status(thm)],[c_10,c_224]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2103,plain,
% 2.12/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.12/1.01      | v1_relat_1(X1) != iProver_top
% 2.12/1.01      | v1_relat_1(X0) = iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_4411,plain,
% 2.12/1.01      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 2.12/1.01      | v1_relat_1(sK5) = iProver_top ),
% 2.12/1.01      inference(superposition,[status(thm)],[c_2373,c_2103]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_15,plain,
% 2.12/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.12/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2114,plain,
% 2.12/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_4438,plain,
% 2.12/1.01      ( v1_relat_1(sK5) = iProver_top ),
% 2.12/1.01      inference(forward_subsumption_resolution,
% 2.12/1.01                [status(thm)],
% 2.12/1.01                [c_4411,c_2114]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_1,plain,
% 2.12/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.12/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2125,plain,
% 2.12/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.12/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_0,plain,
% 2.12/1.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.12/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2126,plain,
% 2.12/1.01      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.12/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2818,plain,
% 2.12/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 2.12/1.01      inference(superposition,[status(thm)],[c_2125,c_2126]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_11,plain,
% 2.12/1.01      ( v4_relat_1(X0,X1)
% 2.12/1.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.12/1.01      | ~ v1_relat_1(X0) ),
% 2.12/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2116,plain,
% 2.12/1.01      ( v4_relat_1(X0,X1) = iProver_top
% 2.12/1.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.12/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_3790,plain,
% 2.12/1.01      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 2.12/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.12/1.01      inference(superposition,[status(thm)],[c_2818,c_2116]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_16,plain,
% 2.12/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.12/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2113,plain,
% 2.12/1.01      ( k7_relat_1(X0,X1) = X0
% 2.12/1.01      | v4_relat_1(X0,X1) != iProver_top
% 2.12/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_4042,plain,
% 2.12/1.01      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 2.12/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.12/1.01      inference(superposition,[status(thm)],[c_3790,c_2113]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_4440,plain,
% 2.12/1.01      ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
% 2.12/1.01      inference(superposition,[status(thm)],[c_4438,c_4042]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_20,plain,
% 2.12/1.01      ( r1_xboole_0(k1_relat_1(X0),X1)
% 2.12/1.01      | ~ v1_relat_1(X0)
% 2.12/1.01      | k7_relat_1(X0,X1) != k1_xboole_0 ),
% 2.12/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2109,plain,
% 2.12/1.01      ( k7_relat_1(X0,X1) != k1_xboole_0
% 2.12/1.01      | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
% 2.12/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_4653,plain,
% 2.12/1.01      ( sK5 != k1_xboole_0
% 2.12/1.01      | r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top
% 2.12/1.01      | v1_relat_1(sK5) != iProver_top ),
% 2.12/1.01      inference(superposition,[status(thm)],[c_4440,c_2109]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_4654,plain,
% 2.12/1.01      ( r1_xboole_0(k1_relat_1(sK5),k1_relat_1(sK5))
% 2.12/1.01      | ~ v1_relat_1(sK5)
% 2.12/1.01      | sK5 != k1_xboole_0 ),
% 2.12/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_4653]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_4439,plain,
% 2.12/1.01      ( v1_relat_1(sK5) ),
% 2.12/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_4438]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_17,plain,
% 2.12/1.01      ( ~ v1_relat_1(X0)
% 2.12/1.01      | k2_relat_1(X0) != k1_xboole_0
% 2.12/1.01      | k1_xboole_0 = X0 ),
% 2.12/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_3351,plain,
% 2.12/1.01      ( ~ v1_relat_1(sK5)
% 2.12/1.01      | k2_relat_1(sK5) != k1_xboole_0
% 2.12/1.01      | k1_xboole_0 = sK5 ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_3355,plain,
% 2.12/1.01      ( k2_relat_1(sK5) != k1_xboole_0
% 2.12/1.01      | k1_xboole_0 = sK5
% 2.12/1.01      | v1_relat_1(sK5) != iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_3351]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_1507,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2643,plain,
% 2.12/1.01      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_1507]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_3224,plain,
% 2.12/1.01      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_2643]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_3225,plain,
% 2.12/1.01      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_3224]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2641,plain,
% 2.12/1.01      ( sK5 = sK5 ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_1506]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2534,plain,
% 2.12/1.01      ( r2_hidden(sK2(k1_relat_1(sK5)),k1_relat_1(sK5))
% 2.12/1.01      | k1_xboole_0 = k1_relat_1(sK5) ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2354,plain,
% 2.12/1.01      ( k1_relset_1(sK3,sK4,sK5) != X0
% 2.12/1.01      | k1_xboole_0 != X0
% 2.12/1.01      | k1_xboole_0 = k1_relset_1(sK3,sK4,sK5) ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_1507]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2441,plain,
% 2.12/1.01      ( k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5)
% 2.12/1.01      | k1_xboole_0 = k1_relset_1(sK3,sK4,sK5)
% 2.12/1.01      | k1_xboole_0 != k1_relat_1(sK5) ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_2354]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_21,plain,
% 2.12/1.01      ( v5_relat_1(X0,X1)
% 2.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.12/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_14,plain,
% 2.12/1.01      ( ~ v5_relat_1(X0,X1)
% 2.12/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 2.12/1.01      | ~ v1_relat_1(X0) ),
% 2.12/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_368,plain,
% 2.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 2.12/1.01      | ~ v1_relat_1(X0) ),
% 2.12/1.01      inference(resolution,[status(thm)],[c_21,c_14]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2102,plain,
% 2.12/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.12/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 2.12/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.12/1.01      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2420,plain,
% 2.12/1.01      ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
% 2.12/1.01      | v1_relat_1(sK5) != iProver_top ),
% 2.12/1.01      inference(superposition,[status(thm)],[c_2104,c_2102]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_23,plain,
% 2.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.12/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.12/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_2367,plain,
% 2.12/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.12/1.01      | k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 2.12/1.01      inference(instantiation,[status(thm)],[c_23]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(c_26,negated_conjecture,
% 2.12/1.01      ( k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) ),
% 2.12/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.12/1.01  
% 2.12/1.01  cnf(contradiction,plain,
% 2.12/1.01      ( $false ),
% 2.12/1.01      inference(minisat,
% 2.12/1.01                [status(thm)],
% 2.12/1.01                [c_7722,c_6131,c_5232,c_5230,c_5141,c_4654,c_4439,c_4438,
% 2.12/1.01                 c_3355,c_3225,c_2641,c_2534,c_2441,c_2420,c_2367,c_26,
% 2.12/1.01                 c_27]) ).
% 2.12/1.01  
% 2.12/1.01  
% 2.12/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.12/1.01  
% 2.12/1.01  ------                               Statistics
% 2.12/1.01  
% 2.12/1.01  ------ General
% 2.12/1.01  
% 2.12/1.01  abstr_ref_over_cycles:                  0
% 2.12/1.01  abstr_ref_under_cycles:                 0
% 2.12/1.01  gc_basic_clause_elim:                   0
% 2.12/1.01  forced_gc_time:                         0
% 2.12/1.01  parsing_time:                           0.012
% 2.12/1.01  unif_index_cands_time:                  0.
% 2.12/1.01  unif_index_add_time:                    0.
% 2.12/1.01  orderings_time:                         0.
% 2.12/1.01  out_proof_time:                         0.017
% 2.12/1.01  total_time:                             0.291
% 2.12/1.01  num_of_symbols:                         52
% 2.12/1.01  num_of_terms:                           5261
% 2.12/1.01  
% 2.12/1.01  ------ Preprocessing
% 2.12/1.01  
% 2.12/1.01  num_of_splits:                          0
% 2.12/1.01  num_of_split_atoms:                     0
% 2.12/1.01  num_of_reused_defs:                     0
% 2.12/1.01  num_eq_ax_congr_red:                    41
% 2.12/1.01  num_of_sem_filtered_clauses:            1
% 2.12/1.01  num_of_subtypes:                        0
% 2.12/1.01  monotx_restored_types:                  0
% 2.12/1.01  sat_num_of_epr_types:                   0
% 2.12/1.01  sat_num_of_non_cyclic_types:            0
% 2.12/1.01  sat_guarded_non_collapsed_types:        0
% 2.12/1.01  num_pure_diseq_elim:                    0
% 2.12/1.01  simp_replaced_by:                       0
% 2.12/1.01  res_preprocessed:                       129
% 2.12/1.01  prep_upred:                             0
% 2.12/1.01  prep_unflattend:                        62
% 2.12/1.01  smt_new_axioms:                         0
% 2.12/1.01  pred_elim_cands:                        6
% 2.12/1.01  pred_elim:                              1
% 2.12/1.01  pred_elim_cl:                           2
% 2.12/1.01  pred_elim_cycles:                       7
% 2.12/1.01  merged_defs:                            8
% 2.12/1.01  merged_defs_ncl:                        0
% 2.12/1.01  bin_hyper_res:                          9
% 2.12/1.01  prep_cycles:                            4
% 2.12/1.01  pred_elim_time:                         0.013
% 2.12/1.01  splitting_time:                         0.
% 2.12/1.01  sem_filter_time:                        0.
% 2.12/1.01  monotx_time:                            0.
% 2.12/1.01  subtype_inf_time:                       0.
% 2.12/1.01  
% 2.12/1.01  ------ Problem properties
% 2.12/1.01  
% 2.12/1.01  clauses:                                26
% 2.12/1.01  conjectures:                            3
% 2.12/1.01  epr:                                    3
% 2.12/1.01  horn:                                   22
% 2.12/1.01  ground:                                 2
% 2.12/1.01  unary:                                  3
% 2.12/1.01  binary:                                 11
% 2.12/1.01  lits:                                   61
% 2.12/1.01  lits_eq:                                11
% 2.12/1.01  fd_pure:                                0
% 2.12/1.01  fd_pseudo:                              0
% 2.12/1.01  fd_cond:                                3
% 2.12/1.01  fd_pseudo_cond:                         0
% 2.12/1.01  ac_symbols:                             0
% 2.12/1.01  
% 2.12/1.01  ------ Propositional Solver
% 2.12/1.01  
% 2.12/1.01  prop_solver_calls:                      30
% 2.12/1.01  prop_fast_solver_calls:                 1044
% 2.12/1.01  smt_solver_calls:                       0
% 2.12/1.01  smt_fast_solver_calls:                  0
% 2.12/1.01  prop_num_of_clauses:                    2559
% 2.12/1.01  prop_preprocess_simplified:             7164
% 2.12/1.01  prop_fo_subsumed:                       10
% 2.12/1.01  prop_solver_time:                       0.
% 2.12/1.01  smt_solver_time:                        0.
% 2.12/1.01  smt_fast_solver_time:                   0.
% 2.12/1.01  prop_fast_solver_time:                  0.
% 2.12/1.01  prop_unsat_core_time:                   0.
% 2.12/1.01  
% 2.12/1.01  ------ QBF
% 2.12/1.01  
% 2.12/1.01  qbf_q_res:                              0
% 2.12/1.01  qbf_num_tautologies:                    0
% 2.12/1.01  qbf_prep_cycles:                        0
% 2.12/1.01  
% 2.12/1.01  ------ BMC1
% 2.12/1.01  
% 2.12/1.01  bmc1_current_bound:                     -1
% 2.12/1.01  bmc1_last_solved_bound:                 -1
% 2.12/1.01  bmc1_unsat_core_size:                   -1
% 2.12/1.01  bmc1_unsat_core_parents_size:           -1
% 2.12/1.01  bmc1_merge_next_fun:                    0
% 2.12/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.12/1.01  
% 2.12/1.01  ------ Instantiation
% 2.12/1.01  
% 2.12/1.01  inst_num_of_clauses:                    760
% 2.12/1.01  inst_num_in_passive:                    186
% 2.12/1.01  inst_num_in_active:                     440
% 2.12/1.01  inst_num_in_unprocessed:                133
% 2.12/1.01  inst_num_of_loops:                      528
% 2.12/1.01  inst_num_of_learning_restarts:          0
% 2.12/1.01  inst_num_moves_active_passive:          83
% 2.12/1.01  inst_lit_activity:                      0
% 2.12/1.01  inst_lit_activity_moves:                0
% 2.12/1.01  inst_num_tautologies:                   0
% 2.12/1.01  inst_num_prop_implied:                  0
% 2.12/1.01  inst_num_existing_simplified:           0
% 2.12/1.01  inst_num_eq_res_simplified:             0
% 2.12/1.01  inst_num_child_elim:                    0
% 2.12/1.01  inst_num_of_dismatching_blockings:      188
% 2.12/1.01  inst_num_of_non_proper_insts:           820
% 2.12/1.01  inst_num_of_duplicates:                 0
% 2.12/1.01  inst_inst_num_from_inst_to_res:         0
% 2.12/1.01  inst_dismatching_checking_time:         0.
% 2.12/1.01  
% 2.12/1.01  ------ Resolution
% 2.12/1.01  
% 2.12/1.01  res_num_of_clauses:                     0
% 2.12/1.01  res_num_in_passive:                     0
% 2.12/1.01  res_num_in_active:                      0
% 2.12/1.01  res_num_of_loops:                       133
% 2.12/1.01  res_forward_subset_subsumed:            36
% 2.12/1.01  res_backward_subset_subsumed:           0
% 2.12/1.01  res_forward_subsumed:                   0
% 2.12/1.01  res_backward_subsumed:                  0
% 2.12/1.01  res_forward_subsumption_resolution:     0
% 2.12/1.01  res_backward_subsumption_resolution:    0
% 2.12/1.01  res_clause_to_clause_subsumption:       402
% 2.12/1.01  res_orphan_elimination:                 0
% 2.12/1.01  res_tautology_del:                      100
% 2.12/1.01  res_num_eq_res_simplified:              0
% 2.12/1.01  res_num_sel_changes:                    0
% 2.12/1.01  res_moves_from_active_to_pass:          0
% 2.12/1.01  
% 2.12/1.01  ------ Superposition
% 2.12/1.01  
% 2.12/1.01  sup_time_total:                         0.
% 2.12/1.01  sup_time_generating:                    0.
% 2.12/1.01  sup_time_sim_full:                      0.
% 2.12/1.01  sup_time_sim_immed:                     0.
% 2.12/1.01  
% 2.12/1.01  sup_num_of_clauses:                     133
% 2.12/1.01  sup_num_in_active:                      70
% 2.12/1.01  sup_num_in_passive:                     63
% 2.12/1.01  sup_num_of_loops:                       104
% 2.12/1.01  sup_fw_superposition:                   66
% 2.12/1.01  sup_bw_superposition:                   83
% 2.12/1.01  sup_immediate_simplified:               6
% 2.12/1.01  sup_given_eliminated:                   0
% 2.12/1.01  comparisons_done:                       0
% 2.12/1.01  comparisons_avoided:                    0
% 2.12/1.01  
% 2.12/1.01  ------ Simplifications
% 2.12/1.01  
% 2.12/1.01  
% 2.12/1.01  sim_fw_subset_subsumed:                 4
% 2.12/1.01  sim_bw_subset_subsumed:                 3
% 2.12/1.01  sim_fw_subsumed:                        1
% 2.12/1.01  sim_bw_subsumed:                        0
% 2.12/1.01  sim_fw_subsumption_res:                 1
% 2.12/1.01  sim_bw_subsumption_res:                 0
% 2.12/1.01  sim_tautology_del:                      3
% 2.12/1.01  sim_eq_tautology_del:                   4
% 2.12/1.01  sim_eq_res_simp:                        2
% 2.12/1.01  sim_fw_demodulated:                     0
% 2.12/1.01  sim_bw_demodulated:                     32
% 2.12/1.01  sim_light_normalised:                   3
% 2.12/1.01  sim_joinable_taut:                      0
% 2.12/1.01  sim_joinable_simp:                      0
% 2.12/1.01  sim_ac_normalised:                      0
% 2.12/1.01  sim_smt_subsumption:                    0
% 2.12/1.01  
%------------------------------------------------------------------------------
