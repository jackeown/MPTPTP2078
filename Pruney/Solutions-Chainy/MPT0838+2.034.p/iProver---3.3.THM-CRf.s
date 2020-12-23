%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:32 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 389 expanded)
%              Number of clauses        :   79 ( 157 expanded)
%              Number of leaves         :   27 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          :  454 (1380 expanded)
%              Number of equality atoms :  145 ( 304 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
              | ~ m1_subset_1(X3,X1) )
          & k1_xboole_0 != k1_relset_1(X0,X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(X0,X1,sK6))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k1_relset_1(X0,X1,sK6)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(X0,sK5,X2))
                | ~ m1_subset_1(X3,sK5) )
            & k1_xboole_0 != k1_relset_1(X0,sK5,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK5))) )
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK4,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK4,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK4,sK5,sK6))
        | ~ m1_subset_1(X3,sK5) )
    & k1_xboole_0 != k1_relset_1(sK4,sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f53,f52,f51])).

fof(f86,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f38])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f42])).

fof(f46,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f46,f45,f44])).

fof(f61,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f61])).

fof(f4,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK4,sK5,sK6))
      | ~ m1_subset_1(X3,sK5) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    k1_xboole_0 != k1_relset_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2138,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2149,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2670,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2138,c_2149])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_262,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_263,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_262])).

cnf(c_320,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_263])).

cnf(c_2137,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_17880,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2670,c_2137])).

cnf(c_2440,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_320])).

cnf(c_3068,plain,
    ( ~ r1_tarski(sK6,k2_zfmisc_1(sK4,sK5))
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2440])).

cnf(c_3070,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3068])).

cnf(c_21,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3104,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3105,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3104])).

cnf(c_17976,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17880,c_2670,c_3070,c_3105])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2158,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2148,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4194,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2158,c_2148])).

cnf(c_24,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2143,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4512,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4194,c_2143])).

cnf(c_17981,plain,
    ( k7_relat_1(sK6,k1_relat_1(sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_17976,c_4512])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2145,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17982,plain,
    ( k2_relat_1(k7_relat_1(sK6,X0)) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_17976,c_2145])).

cnf(c_18074,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_17981,c_17982])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2160,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_25,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_20,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_25,c_20])).

cnf(c_2134,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_3201,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2138,c_2134])).

cnf(c_3678,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3201,c_2670,c_3070,c_3105])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_998,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_999,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_998])).

cnf(c_1050,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_429,c_999])).

cnf(c_2133,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1050])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2154,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4733,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(k1_zfmisc_1(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2133,c_2154])).

cnf(c_10,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4737,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4733,c_10])).

cnf(c_4876,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3678,c_4737])).

cnf(c_5230,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(sK6)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2160,c_4876])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2151,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6137,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | m1_subset_1(sK0(k2_relat_1(sK6)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5230,c_2151])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2140,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3403,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2138,c_2140])).

cnf(c_29,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,k2_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2139,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,k2_relset_1(sK4,sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2503,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k1_xboole_0
    | m1_subset_1(sK0(k2_relset_1(sK4,sK5,sK6)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2160,c_2139])).

cnf(c_3531,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | m1_subset_1(sK0(k2_relat_1(sK6)),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3403,c_2503])).

cnf(c_6306,plain,
    ( k2_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6137,c_3531])).

cnf(c_18076,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_18074,c_6306])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2637,plain,
    ( ~ r1_tarski(k1_relat_1(sK6),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(sK6)) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_4451,plain,
    ( ~ r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k9_relat_1(sK6,k1_relat_1(sK6)) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_3080,plain,
    ( r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2671,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2670])).

cnf(c_1489,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2415,plain,
    ( k1_relset_1(sK4,sK5,sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relset_1(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_2491,plain,
    ( k1_relset_1(sK4,sK5,sK6) != k1_relat_1(sK6)
    | k1_xboole_0 = k1_relset_1(sK4,sK5,sK6)
    | k1_xboole_0 != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2415])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2418,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != k1_relset_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18076,c_4451,c_3104,c_3080,c_3068,c_2671,c_2491,c_2418,c_30,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.77/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/0.99  
% 3.77/0.99  ------  iProver source info
% 3.77/0.99  
% 3.77/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.77/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/0.99  git: non_committed_changes: false
% 3.77/0.99  git: last_make_outside_of_git: false
% 3.77/0.99  
% 3.77/0.99  ------ 
% 3.77/0.99  
% 3.77/0.99  ------ Input Options
% 3.77/0.99  
% 3.77/0.99  --out_options                           all
% 3.77/0.99  --tptp_safe_out                         true
% 3.77/0.99  --problem_path                          ""
% 3.77/0.99  --include_path                          ""
% 3.77/0.99  --clausifier                            res/vclausify_rel
% 3.77/0.99  --clausifier_options                    --mode clausify
% 3.77/0.99  --stdin                                 false
% 3.77/0.99  --stats_out                             all
% 3.77/0.99  
% 3.77/0.99  ------ General Options
% 3.77/0.99  
% 3.77/0.99  --fof                                   false
% 3.77/0.99  --time_out_real                         305.
% 3.77/0.99  --time_out_virtual                      -1.
% 3.77/0.99  --symbol_type_check                     false
% 3.77/0.99  --clausify_out                          false
% 3.77/0.99  --sig_cnt_out                           false
% 3.77/0.99  --trig_cnt_out                          false
% 3.77/0.99  --trig_cnt_out_tolerance                1.
% 3.77/0.99  --trig_cnt_out_sk_spl                   false
% 3.77/0.99  --abstr_cl_out                          false
% 3.77/0.99  
% 3.77/0.99  ------ Global Options
% 3.77/0.99  
% 3.77/0.99  --schedule                              default
% 3.77/0.99  --add_important_lit                     false
% 3.77/0.99  --prop_solver_per_cl                    1000
% 3.77/0.99  --min_unsat_core                        false
% 3.77/0.99  --soft_assumptions                      false
% 3.77/0.99  --soft_lemma_size                       3
% 3.77/0.99  --prop_impl_unit_size                   0
% 3.77/0.99  --prop_impl_unit                        []
% 3.77/0.99  --share_sel_clauses                     true
% 3.77/0.99  --reset_solvers                         false
% 3.77/0.99  --bc_imp_inh                            [conj_cone]
% 3.77/0.99  --conj_cone_tolerance                   3.
% 3.77/0.99  --extra_neg_conj                        none
% 3.77/0.99  --large_theory_mode                     true
% 3.77/0.99  --prolific_symb_bound                   200
% 3.77/0.99  --lt_threshold                          2000
% 3.77/0.99  --clause_weak_htbl                      true
% 3.77/0.99  --gc_record_bc_elim                     false
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing Options
% 3.77/0.99  
% 3.77/0.99  --preprocessing_flag                    true
% 3.77/0.99  --time_out_prep_mult                    0.1
% 3.77/0.99  --splitting_mode                        input
% 3.77/0.99  --splitting_grd                         true
% 3.77/0.99  --splitting_cvd                         false
% 3.77/0.99  --splitting_cvd_svl                     false
% 3.77/0.99  --splitting_nvd                         32
% 3.77/0.99  --sub_typing                            true
% 3.77/0.99  --prep_gs_sim                           true
% 3.77/0.99  --prep_unflatten                        true
% 3.77/0.99  --prep_res_sim                          true
% 3.77/0.99  --prep_upred                            true
% 3.77/0.99  --prep_sem_filter                       exhaustive
% 3.77/0.99  --prep_sem_filter_out                   false
% 3.77/0.99  --pred_elim                             true
% 3.77/0.99  --res_sim_input                         true
% 3.77/0.99  --eq_ax_congr_red                       true
% 3.77/0.99  --pure_diseq_elim                       true
% 3.77/0.99  --brand_transform                       false
% 3.77/0.99  --non_eq_to_eq                          false
% 3.77/0.99  --prep_def_merge                        true
% 3.77/0.99  --prep_def_merge_prop_impl              false
% 3.77/0.99  --prep_def_merge_mbd                    true
% 3.77/0.99  --prep_def_merge_tr_red                 false
% 3.77/0.99  --prep_def_merge_tr_cl                  false
% 3.77/0.99  --smt_preprocessing                     true
% 3.77/0.99  --smt_ac_axioms                         fast
% 3.77/0.99  --preprocessed_out                      false
% 3.77/0.99  --preprocessed_stats                    false
% 3.77/0.99  
% 3.77/0.99  ------ Abstraction refinement Options
% 3.77/0.99  
% 3.77/0.99  --abstr_ref                             []
% 3.77/0.99  --abstr_ref_prep                        false
% 3.77/0.99  --abstr_ref_until_sat                   false
% 3.77/0.99  --abstr_ref_sig_restrict                funpre
% 3.77/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/0.99  --abstr_ref_under                       []
% 3.77/0.99  
% 3.77/0.99  ------ SAT Options
% 3.77/0.99  
% 3.77/0.99  --sat_mode                              false
% 3.77/0.99  --sat_fm_restart_options                ""
% 3.77/0.99  --sat_gr_def                            false
% 3.77/0.99  --sat_epr_types                         true
% 3.77/0.99  --sat_non_cyclic_types                  false
% 3.77/0.99  --sat_finite_models                     false
% 3.77/0.99  --sat_fm_lemmas                         false
% 3.77/0.99  --sat_fm_prep                           false
% 3.77/0.99  --sat_fm_uc_incr                        true
% 3.77/0.99  --sat_out_model                         small
% 3.77/0.99  --sat_out_clauses                       false
% 3.77/0.99  
% 3.77/0.99  ------ QBF Options
% 3.77/0.99  
% 3.77/0.99  --qbf_mode                              false
% 3.77/0.99  --qbf_elim_univ                         false
% 3.77/0.99  --qbf_dom_inst                          none
% 3.77/0.99  --qbf_dom_pre_inst                      false
% 3.77/0.99  --qbf_sk_in                             false
% 3.77/0.99  --qbf_pred_elim                         true
% 3.77/0.99  --qbf_split                             512
% 3.77/0.99  
% 3.77/0.99  ------ BMC1 Options
% 3.77/0.99  
% 3.77/0.99  --bmc1_incremental                      false
% 3.77/0.99  --bmc1_axioms                           reachable_all
% 3.77/0.99  --bmc1_min_bound                        0
% 3.77/0.99  --bmc1_max_bound                        -1
% 3.77/0.99  --bmc1_max_bound_default                -1
% 3.77/0.99  --bmc1_symbol_reachability              true
% 3.77/0.99  --bmc1_property_lemmas                  false
% 3.77/0.99  --bmc1_k_induction                      false
% 3.77/0.99  --bmc1_non_equiv_states                 false
% 3.77/0.99  --bmc1_deadlock                         false
% 3.77/0.99  --bmc1_ucm                              false
% 3.77/0.99  --bmc1_add_unsat_core                   none
% 3.77/0.99  --bmc1_unsat_core_children              false
% 3.77/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/0.99  --bmc1_out_stat                         full
% 3.77/0.99  --bmc1_ground_init                      false
% 3.77/0.99  --bmc1_pre_inst_next_state              false
% 3.77/0.99  --bmc1_pre_inst_state                   false
% 3.77/0.99  --bmc1_pre_inst_reach_state             false
% 3.77/0.99  --bmc1_out_unsat_core                   false
% 3.77/0.99  --bmc1_aig_witness_out                  false
% 3.77/0.99  --bmc1_verbose                          false
% 3.77/0.99  --bmc1_dump_clauses_tptp                false
% 3.77/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.77/0.99  --bmc1_dump_file                        -
% 3.77/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.77/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.77/0.99  --bmc1_ucm_extend_mode                  1
% 3.77/0.99  --bmc1_ucm_init_mode                    2
% 3.77/0.99  --bmc1_ucm_cone_mode                    none
% 3.77/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.77/0.99  --bmc1_ucm_relax_model                  4
% 3.77/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.77/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/0.99  --bmc1_ucm_layered_model                none
% 3.77/0.99  --bmc1_ucm_max_lemma_size               10
% 3.77/0.99  
% 3.77/0.99  ------ AIG Options
% 3.77/0.99  
% 3.77/0.99  --aig_mode                              false
% 3.77/0.99  
% 3.77/0.99  ------ Instantiation Options
% 3.77/0.99  
% 3.77/0.99  --instantiation_flag                    true
% 3.77/0.99  --inst_sos_flag                         false
% 3.77/0.99  --inst_sos_phase                        true
% 3.77/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/0.99  --inst_lit_sel_side                     num_symb
% 3.77/0.99  --inst_solver_per_active                1400
% 3.77/0.99  --inst_solver_calls_frac                1.
% 3.77/0.99  --inst_passive_queue_type               priority_queues
% 3.77/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/0.99  --inst_passive_queues_freq              [25;2]
% 3.77/0.99  --inst_dismatching                      true
% 3.77/0.99  --inst_eager_unprocessed_to_passive     true
% 3.77/0.99  --inst_prop_sim_given                   true
% 3.77/0.99  --inst_prop_sim_new                     false
% 3.77/0.99  --inst_subs_new                         false
% 3.77/0.99  --inst_eq_res_simp                      false
% 3.77/0.99  --inst_subs_given                       false
% 3.77/0.99  --inst_orphan_elimination               true
% 3.77/0.99  --inst_learning_loop_flag               true
% 3.77/0.99  --inst_learning_start                   3000
% 3.77/0.99  --inst_learning_factor                  2
% 3.77/0.99  --inst_start_prop_sim_after_learn       3
% 3.77/0.99  --inst_sel_renew                        solver
% 3.77/0.99  --inst_lit_activity_flag                true
% 3.77/0.99  --inst_restr_to_given                   false
% 3.77/0.99  --inst_activity_threshold               500
% 3.77/0.99  --inst_out_proof                        true
% 3.77/0.99  
% 3.77/0.99  ------ Resolution Options
% 3.77/0.99  
% 3.77/0.99  --resolution_flag                       true
% 3.77/0.99  --res_lit_sel                           adaptive
% 3.77/0.99  --res_lit_sel_side                      none
% 3.77/0.99  --res_ordering                          kbo
% 3.77/0.99  --res_to_prop_solver                    active
% 3.77/0.99  --res_prop_simpl_new                    false
% 3.77/0.99  --res_prop_simpl_given                  true
% 3.77/0.99  --res_passive_queue_type                priority_queues
% 3.77/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/0.99  --res_passive_queues_freq               [15;5]
% 3.77/0.99  --res_forward_subs                      full
% 3.77/0.99  --res_backward_subs                     full
% 3.77/0.99  --res_forward_subs_resolution           true
% 3.77/0.99  --res_backward_subs_resolution          true
% 3.77/0.99  --res_orphan_elimination                true
% 3.77/0.99  --res_time_limit                        2.
% 3.77/0.99  --res_out_proof                         true
% 3.77/0.99  
% 3.77/0.99  ------ Superposition Options
% 3.77/0.99  
% 3.77/0.99  --superposition_flag                    true
% 3.77/0.99  --sup_passive_queue_type                priority_queues
% 3.77/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.77/0.99  --demod_completeness_check              fast
% 3.77/0.99  --demod_use_ground                      true
% 3.77/0.99  --sup_to_prop_solver                    passive
% 3.77/0.99  --sup_prop_simpl_new                    true
% 3.77/0.99  --sup_prop_simpl_given                  true
% 3.77/0.99  --sup_fun_splitting                     false
% 3.77/0.99  --sup_smt_interval                      50000
% 3.77/0.99  
% 3.77/0.99  ------ Superposition Simplification Setup
% 3.77/0.99  
% 3.77/0.99  --sup_indices_passive                   []
% 3.77/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/0.99  --sup_full_bw                           [BwDemod]
% 3.77/0.99  --sup_immed_triv                        [TrivRules]
% 3.77/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/0.99  --sup_immed_bw_main                     []
% 3.77/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.77/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.77/0.99  
% 3.77/0.99  ------ Combination Options
% 3.77/0.99  
% 3.77/0.99  --comb_res_mult                         3
% 3.77/0.99  --comb_sup_mult                         2
% 3.77/0.99  --comb_inst_mult                        10
% 3.77/0.99  
% 3.77/0.99  ------ Debug Options
% 3.77/0.99  
% 3.77/0.99  --dbg_backtrace                         false
% 3.77/0.99  --dbg_dump_prop_clauses                 false
% 3.77/0.99  --dbg_dump_prop_clauses_file            -
% 3.77/0.99  --dbg_out_stat                          false
% 3.77/0.99  ------ Parsing...
% 3.77/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/0.99  ------ Proving...
% 3.77/0.99  ------ Problem Properties 
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  clauses                                 30
% 3.77/0.99  conjectures                             3
% 3.77/0.99  EPR                                     6
% 3.77/0.99  Horn                                    27
% 3.77/0.99  unary                                   5
% 3.77/0.99  binary                                  14
% 3.77/0.99  lits                                    68
% 3.77/0.99  lits eq                                 13
% 3.77/0.99  fd_pure                                 0
% 3.77/0.99  fd_pseudo                               0
% 3.77/0.99  fd_cond                                 2
% 3.77/0.99  fd_pseudo_cond                          4
% 3.77/0.99  AC symbols                              0
% 3.77/0.99  
% 3.77/0.99  ------ Schedule dynamic 5 is on 
% 3.77/0.99  
% 3.77/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  ------ 
% 3.77/0.99  Current options:
% 3.77/0.99  ------ 
% 3.77/0.99  
% 3.77/0.99  ------ Input Options
% 3.77/0.99  
% 3.77/0.99  --out_options                           all
% 3.77/0.99  --tptp_safe_out                         true
% 3.77/0.99  --problem_path                          ""
% 3.77/0.99  --include_path                          ""
% 3.77/0.99  --clausifier                            res/vclausify_rel
% 3.77/0.99  --clausifier_options                    --mode clausify
% 3.77/0.99  --stdin                                 false
% 3.77/0.99  --stats_out                             all
% 3.77/0.99  
% 3.77/0.99  ------ General Options
% 3.77/0.99  
% 3.77/0.99  --fof                                   false
% 3.77/0.99  --time_out_real                         305.
% 3.77/0.99  --time_out_virtual                      -1.
% 3.77/0.99  --symbol_type_check                     false
% 3.77/0.99  --clausify_out                          false
% 3.77/0.99  --sig_cnt_out                           false
% 3.77/0.99  --trig_cnt_out                          false
% 3.77/0.99  --trig_cnt_out_tolerance                1.
% 3.77/0.99  --trig_cnt_out_sk_spl                   false
% 3.77/0.99  --abstr_cl_out                          false
% 3.77/0.99  
% 3.77/0.99  ------ Global Options
% 3.77/0.99  
% 3.77/0.99  --schedule                              default
% 3.77/0.99  --add_important_lit                     false
% 3.77/0.99  --prop_solver_per_cl                    1000
% 3.77/0.99  --min_unsat_core                        false
% 3.77/0.99  --soft_assumptions                      false
% 3.77/0.99  --soft_lemma_size                       3
% 3.77/0.99  --prop_impl_unit_size                   0
% 3.77/0.99  --prop_impl_unit                        []
% 3.77/0.99  --share_sel_clauses                     true
% 3.77/0.99  --reset_solvers                         false
% 3.77/0.99  --bc_imp_inh                            [conj_cone]
% 3.77/0.99  --conj_cone_tolerance                   3.
% 3.77/0.99  --extra_neg_conj                        none
% 3.77/0.99  --large_theory_mode                     true
% 3.77/0.99  --prolific_symb_bound                   200
% 3.77/0.99  --lt_threshold                          2000
% 3.77/0.99  --clause_weak_htbl                      true
% 3.77/0.99  --gc_record_bc_elim                     false
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing Options
% 3.77/0.99  
% 3.77/0.99  --preprocessing_flag                    true
% 3.77/0.99  --time_out_prep_mult                    0.1
% 3.77/0.99  --splitting_mode                        input
% 3.77/0.99  --splitting_grd                         true
% 3.77/0.99  --splitting_cvd                         false
% 3.77/0.99  --splitting_cvd_svl                     false
% 3.77/0.99  --splitting_nvd                         32
% 3.77/0.99  --sub_typing                            true
% 3.77/0.99  --prep_gs_sim                           true
% 3.77/0.99  --prep_unflatten                        true
% 3.77/0.99  --prep_res_sim                          true
% 3.77/0.99  --prep_upred                            true
% 3.77/0.99  --prep_sem_filter                       exhaustive
% 3.77/0.99  --prep_sem_filter_out                   false
% 3.77/0.99  --pred_elim                             true
% 3.77/0.99  --res_sim_input                         true
% 3.77/0.99  --eq_ax_congr_red                       true
% 3.77/0.99  --pure_diseq_elim                       true
% 3.77/0.99  --brand_transform                       false
% 3.77/0.99  --non_eq_to_eq                          false
% 3.77/0.99  --prep_def_merge                        true
% 3.77/0.99  --prep_def_merge_prop_impl              false
% 3.77/0.99  --prep_def_merge_mbd                    true
% 3.77/0.99  --prep_def_merge_tr_red                 false
% 3.77/0.99  --prep_def_merge_tr_cl                  false
% 3.77/0.99  --smt_preprocessing                     true
% 3.77/0.99  --smt_ac_axioms                         fast
% 3.77/0.99  --preprocessed_out                      false
% 3.77/0.99  --preprocessed_stats                    false
% 3.77/0.99  
% 3.77/0.99  ------ Abstraction refinement Options
% 3.77/0.99  
% 3.77/0.99  --abstr_ref                             []
% 3.77/0.99  --abstr_ref_prep                        false
% 3.77/0.99  --abstr_ref_until_sat                   false
% 3.77/0.99  --abstr_ref_sig_restrict                funpre
% 3.77/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/0.99  --abstr_ref_under                       []
% 3.77/0.99  
% 3.77/0.99  ------ SAT Options
% 3.77/0.99  
% 3.77/0.99  --sat_mode                              false
% 3.77/0.99  --sat_fm_restart_options                ""
% 3.77/0.99  --sat_gr_def                            false
% 3.77/0.99  --sat_epr_types                         true
% 3.77/0.99  --sat_non_cyclic_types                  false
% 3.77/0.99  --sat_finite_models                     false
% 3.77/0.99  --sat_fm_lemmas                         false
% 3.77/0.99  --sat_fm_prep                           false
% 3.77/0.99  --sat_fm_uc_incr                        true
% 3.77/0.99  --sat_out_model                         small
% 3.77/0.99  --sat_out_clauses                       false
% 3.77/0.99  
% 3.77/0.99  ------ QBF Options
% 3.77/0.99  
% 3.77/0.99  --qbf_mode                              false
% 3.77/0.99  --qbf_elim_univ                         false
% 3.77/0.99  --qbf_dom_inst                          none
% 3.77/0.99  --qbf_dom_pre_inst                      false
% 3.77/0.99  --qbf_sk_in                             false
% 3.77/0.99  --qbf_pred_elim                         true
% 3.77/0.99  --qbf_split                             512
% 3.77/0.99  
% 3.77/0.99  ------ BMC1 Options
% 3.77/0.99  
% 3.77/0.99  --bmc1_incremental                      false
% 3.77/0.99  --bmc1_axioms                           reachable_all
% 3.77/0.99  --bmc1_min_bound                        0
% 3.77/0.99  --bmc1_max_bound                        -1
% 3.77/0.99  --bmc1_max_bound_default                -1
% 3.77/0.99  --bmc1_symbol_reachability              true
% 3.77/0.99  --bmc1_property_lemmas                  false
% 3.77/0.99  --bmc1_k_induction                      false
% 3.77/0.99  --bmc1_non_equiv_states                 false
% 3.77/0.99  --bmc1_deadlock                         false
% 3.77/0.99  --bmc1_ucm                              false
% 3.77/0.99  --bmc1_add_unsat_core                   none
% 3.77/0.99  --bmc1_unsat_core_children              false
% 3.77/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/0.99  --bmc1_out_stat                         full
% 3.77/0.99  --bmc1_ground_init                      false
% 3.77/0.99  --bmc1_pre_inst_next_state              false
% 3.77/0.99  --bmc1_pre_inst_state                   false
% 3.77/0.99  --bmc1_pre_inst_reach_state             false
% 3.77/0.99  --bmc1_out_unsat_core                   false
% 3.77/0.99  --bmc1_aig_witness_out                  false
% 3.77/0.99  --bmc1_verbose                          false
% 3.77/0.99  --bmc1_dump_clauses_tptp                false
% 3.77/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.77/0.99  --bmc1_dump_file                        -
% 3.77/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.77/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.77/0.99  --bmc1_ucm_extend_mode                  1
% 3.77/0.99  --bmc1_ucm_init_mode                    2
% 3.77/0.99  --bmc1_ucm_cone_mode                    none
% 3.77/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.77/0.99  --bmc1_ucm_relax_model                  4
% 3.77/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.77/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/0.99  --bmc1_ucm_layered_model                none
% 3.77/0.99  --bmc1_ucm_max_lemma_size               10
% 3.77/0.99  
% 3.77/0.99  ------ AIG Options
% 3.77/0.99  
% 3.77/0.99  --aig_mode                              false
% 3.77/0.99  
% 3.77/0.99  ------ Instantiation Options
% 3.77/0.99  
% 3.77/0.99  --instantiation_flag                    true
% 3.77/0.99  --inst_sos_flag                         false
% 3.77/0.99  --inst_sos_phase                        true
% 3.77/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/0.99  --inst_lit_sel_side                     none
% 3.77/0.99  --inst_solver_per_active                1400
% 3.77/0.99  --inst_solver_calls_frac                1.
% 3.77/0.99  --inst_passive_queue_type               priority_queues
% 3.77/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/0.99  --inst_passive_queues_freq              [25;2]
% 3.77/0.99  --inst_dismatching                      true
% 3.77/0.99  --inst_eager_unprocessed_to_passive     true
% 3.77/0.99  --inst_prop_sim_given                   true
% 3.77/0.99  --inst_prop_sim_new                     false
% 3.77/0.99  --inst_subs_new                         false
% 3.77/0.99  --inst_eq_res_simp                      false
% 3.77/0.99  --inst_subs_given                       false
% 3.77/0.99  --inst_orphan_elimination               true
% 3.77/0.99  --inst_learning_loop_flag               true
% 3.77/0.99  --inst_learning_start                   3000
% 3.77/0.99  --inst_learning_factor                  2
% 3.77/0.99  --inst_start_prop_sim_after_learn       3
% 3.77/0.99  --inst_sel_renew                        solver
% 3.77/0.99  --inst_lit_activity_flag                true
% 3.77/0.99  --inst_restr_to_given                   false
% 3.77/0.99  --inst_activity_threshold               500
% 3.77/0.99  --inst_out_proof                        true
% 3.77/0.99  
% 3.77/0.99  ------ Resolution Options
% 3.77/0.99  
% 3.77/0.99  --resolution_flag                       false
% 3.77/0.99  --res_lit_sel                           adaptive
% 3.77/0.99  --res_lit_sel_side                      none
% 3.77/0.99  --res_ordering                          kbo
% 3.77/0.99  --res_to_prop_solver                    active
% 3.77/0.99  --res_prop_simpl_new                    false
% 3.77/0.99  --res_prop_simpl_given                  true
% 3.77/0.99  --res_passive_queue_type                priority_queues
% 3.77/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/0.99  --res_passive_queues_freq               [15;5]
% 3.77/0.99  --res_forward_subs                      full
% 3.77/0.99  --res_backward_subs                     full
% 3.77/0.99  --res_forward_subs_resolution           true
% 3.77/0.99  --res_backward_subs_resolution          true
% 3.77/0.99  --res_orphan_elimination                true
% 3.77/0.99  --res_time_limit                        2.
% 3.77/0.99  --res_out_proof                         true
% 3.77/0.99  
% 3.77/0.99  ------ Superposition Options
% 3.77/0.99  
% 3.77/0.99  --superposition_flag                    true
% 3.77/0.99  --sup_passive_queue_type                priority_queues
% 3.77/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.77/0.99  --demod_completeness_check              fast
% 3.77/0.99  --demod_use_ground                      true
% 3.77/0.99  --sup_to_prop_solver                    passive
% 3.77/0.99  --sup_prop_simpl_new                    true
% 3.77/0.99  --sup_prop_simpl_given                  true
% 3.77/0.99  --sup_fun_splitting                     false
% 3.77/0.99  --sup_smt_interval                      50000
% 3.77/0.99  
% 3.77/0.99  ------ Superposition Simplification Setup
% 3.77/0.99  
% 3.77/0.99  --sup_indices_passive                   []
% 3.77/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/0.99  --sup_full_bw                           [BwDemod]
% 3.77/0.99  --sup_immed_triv                        [TrivRules]
% 3.77/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/0.99  --sup_immed_bw_main                     []
% 3.77/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.77/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.77/0.99  
% 3.77/0.99  ------ Combination Options
% 3.77/0.99  
% 3.77/0.99  --comb_res_mult                         3
% 3.77/0.99  --comb_sup_mult                         2
% 3.77/0.99  --comb_inst_mult                        10
% 3.77/0.99  
% 3.77/0.99  ------ Debug Options
% 3.77/0.99  
% 3.77/0.99  --dbg_backtrace                         false
% 3.77/0.99  --dbg_dump_prop_clauses                 false
% 3.77/0.99  --dbg_dump_prop_clauses_file            -
% 3.77/0.99  --dbg_out_stat                          false
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  ------ Proving...
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  % SZS status Theorem for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  fof(f19,conjecture,(
% 3.77/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f20,negated_conjecture,(
% 3.77/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 3.77/0.99    inference(negated_conjecture,[],[f19])).
% 3.77/0.99  
% 3.77/0.99  fof(f36,plain,(
% 3.77/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f20])).
% 3.77/0.99  
% 3.77/0.99  fof(f37,plain,(
% 3.77/0.99    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.77/0.99    inference(flattening,[],[f36])).
% 3.77/0.99  
% 3.77/0.99  fof(f53,plain,(
% 3.77/0.99    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,sK6)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) )),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f52,plain,(
% 3.77/0.99    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,sK5,X2)) | ~m1_subset_1(X3,sK5)) & k1_xboole_0 != k1_relset_1(X0,sK5,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK5)))) & ~v1_xboole_0(sK5))) )),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f51,plain,(
% 3.77/0.99    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK4,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK4,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK4))),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f54,plain,(
% 3.77/0.99    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK4,sK5,sK6)) | ~m1_subset_1(X3,sK5)) & k1_xboole_0 != k1_relset_1(sK4,sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)),
% 3.77/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f53,f52,f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f86,plain,(
% 3.77/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.77/0.99    inference(cnf_transformation,[],[f54])).
% 3.77/0.99  
% 3.77/0.99  fof(f8,axiom,(
% 3.77/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f48,plain,(
% 3.77/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.77/0.99    inference(nnf_transformation,[],[f8])).
% 3.77/0.99  
% 3.77/0.99  fof(f69,plain,(
% 3.77/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f48])).
% 3.77/0.99  
% 3.77/0.99  fof(f9,axiom,(
% 3.77/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f25,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f9])).
% 3.77/0.99  
% 3.77/0.99  fof(f71,plain,(
% 3.77/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f25])).
% 3.77/0.99  
% 3.77/0.99  fof(f70,plain,(
% 3.77/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f48])).
% 3.77/0.99  
% 3.77/0.99  fof(f12,axiom,(
% 3.77/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f76,plain,(
% 3.77/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f12])).
% 3.77/0.99  
% 3.77/0.99  fof(f2,axiom,(
% 3.77/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f40,plain,(
% 3.77/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/0.99    inference(nnf_transformation,[],[f2])).
% 3.77/0.99  
% 3.77/0.99  fof(f41,plain,(
% 3.77/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/0.99    inference(flattening,[],[f40])).
% 3.77/0.99  
% 3.77/0.99  fof(f56,plain,(
% 3.77/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.77/0.99    inference(cnf_transformation,[],[f41])).
% 3.77/0.99  
% 3.77/0.99  fof(f90,plain,(
% 3.77/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.77/0.99    inference(equality_resolution,[],[f56])).
% 3.77/0.99  
% 3.77/0.99  fof(f10,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f26,plain,(
% 3.77/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f10])).
% 3.77/0.99  
% 3.77/0.99  fof(f49,plain,(
% 3.77/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(nnf_transformation,[],[f26])).
% 3.77/0.99  
% 3.77/0.99  fof(f73,plain,(
% 3.77/0.99    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f49])).
% 3.77/0.99  
% 3.77/0.99  fof(f15,axiom,(
% 3.77/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f31,plain,(
% 3.77/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.77/0.99    inference(ennf_transformation,[],[f15])).
% 3.77/0.99  
% 3.77/0.99  fof(f32,plain,(
% 3.77/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(flattening,[],[f31])).
% 3.77/0.99  
% 3.77/0.99  fof(f79,plain,(
% 3.77/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f32])).
% 3.77/0.99  
% 3.77/0.99  fof(f13,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f28,plain,(
% 3.77/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f13])).
% 3.77/0.99  
% 3.77/0.99  fof(f77,plain,(
% 3.77/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f28])).
% 3.77/0.99  
% 3.77/0.99  fof(f1,axiom,(
% 3.77/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f21,plain,(
% 3.77/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.77/0.99    inference(ennf_transformation,[],[f1])).
% 3.77/0.99  
% 3.77/0.99  fof(f38,plain,(
% 3.77/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f39,plain,(
% 3.77/0.99    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 3.77/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f38])).
% 3.77/0.99  
% 3.77/0.99  fof(f55,plain,(
% 3.77/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.77/0.99    inference(cnf_transformation,[],[f39])).
% 3.77/0.99  
% 3.77/0.99  fof(f16,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f33,plain,(
% 3.77/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(ennf_transformation,[],[f16])).
% 3.77/0.99  
% 3.77/0.99  fof(f81,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f33])).
% 3.77/0.99  
% 3.77/0.99  fof(f11,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f27,plain,(
% 3.77/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f11])).
% 3.77/0.99  
% 3.77/0.99  fof(f50,plain,(
% 3.77/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(nnf_transformation,[],[f27])).
% 3.77/0.99  
% 3.77/0.99  fof(f74,plain,(
% 3.77/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f50])).
% 3.77/0.99  
% 3.77/0.99  fof(f5,axiom,(
% 3.77/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f66,plain,(
% 3.77/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f5])).
% 3.77/0.99  
% 3.77/0.99  fof(f7,axiom,(
% 3.77/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f23,plain,(
% 3.77/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f7])).
% 3.77/0.99  
% 3.77/0.99  fof(f24,plain,(
% 3.77/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.77/0.99    inference(flattening,[],[f23])).
% 3.77/0.99  
% 3.77/0.99  fof(f68,plain,(
% 3.77/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f24])).
% 3.77/0.99  
% 3.77/0.99  fof(f3,axiom,(
% 3.77/0.99    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f42,plain,(
% 3.77/0.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.77/0.99    inference(nnf_transformation,[],[f3])).
% 3.77/0.99  
% 3.77/0.99  fof(f43,plain,(
% 3.77/0.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.77/0.99    inference(rectify,[],[f42])).
% 3.77/0.99  
% 3.77/0.99  fof(f46,plain,(
% 3.77/0.99    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f45,plain,(
% 3.77/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f44,plain,(
% 3.77/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f47,plain,(
% 3.77/0.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.77/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f46,f45,f44])).
% 3.77/0.99  
% 3.77/0.99  fof(f61,plain,(
% 3.77/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 3.77/0.99    inference(cnf_transformation,[],[f47])).
% 3.77/0.99  
% 3.77/0.99  fof(f91,plain,(
% 3.77/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 3.77/0.99    inference(equality_resolution,[],[f61])).
% 3.77/0.99  
% 3.77/0.99  fof(f4,axiom,(
% 3.77/0.99    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f65,plain,(
% 3.77/0.99    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.77/0.99    inference(cnf_transformation,[],[f4])).
% 3.77/0.99  
% 3.77/0.99  fof(f6,axiom,(
% 3.77/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f22,plain,(
% 3.77/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f6])).
% 3.77/0.99  
% 3.77/0.99  fof(f67,plain,(
% 3.77/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f22])).
% 3.77/0.99  
% 3.77/0.99  fof(f18,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f35,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(ennf_transformation,[],[f18])).
% 3.77/0.99  
% 3.77/0.99  fof(f83,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f35])).
% 3.77/0.99  
% 3.77/0.99  fof(f88,plain,(
% 3.77/0.99    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK4,sK5,sK6)) | ~m1_subset_1(X3,sK5)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f54])).
% 3.77/0.99  
% 3.77/0.99  fof(f14,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f29,plain,(
% 3.77/0.99    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f14])).
% 3.77/0.99  
% 3.77/0.99  fof(f30,plain,(
% 3.77/0.99    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 3.77/0.99    inference(flattening,[],[f29])).
% 3.77/0.99  
% 3.77/0.99  fof(f78,plain,(
% 3.77/0.99    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f30])).
% 3.77/0.99  
% 3.77/0.99  fof(f17,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f34,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(ennf_transformation,[],[f17])).
% 3.77/0.99  
% 3.77/0.99  fof(f82,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f34])).
% 3.77/0.99  
% 3.77/0.99  fof(f87,plain,(
% 3.77/0.99    k1_xboole_0 != k1_relset_1(sK4,sK5,sK6)),
% 3.77/0.99    inference(cnf_transformation,[],[f54])).
% 3.77/0.99  
% 3.77/0.99  cnf(c_31,negated_conjecture,
% 3.77/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.77/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2138,plain,
% 3.77/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_15,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2149,plain,
% 3.77/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.77/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2670,plain,
% 3.77/0.99      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2138,c_2149]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_16,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.77/0.99      | ~ v1_relat_1(X1)
% 3.77/0.99      | v1_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_14,plain,
% 3.77/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_262,plain,
% 3.77/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.77/0.99      inference(prop_impl,[status(thm)],[c_14]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_263,plain,
% 3.77/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.77/0.99      inference(renaming,[status(thm)],[c_262]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_320,plain,
% 3.77/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.77/0.99      inference(bin_hyper_res,[status(thm)],[c_16,c_263]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2137,plain,
% 3.77/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.77/0.99      | v1_relat_1(X1) != iProver_top
% 3.77/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_17880,plain,
% 3.77/0.99      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.77/0.99      | v1_relat_1(sK6) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2670,c_2137]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2440,plain,
% 3.77/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.77/0.99      | v1_relat_1(X0)
% 3.77/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_320]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3068,plain,
% 3.77/0.99      ( ~ r1_tarski(sK6,k2_zfmisc_1(sK4,sK5))
% 3.77/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
% 3.77/0.99      | v1_relat_1(sK6) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_2440]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3070,plain,
% 3.77/0.99      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.77/0.99      | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.77/0.99      | v1_relat_1(sK6) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_3068]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_21,plain,
% 3.77/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3104,plain,
% 3.77/0.99      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3105,plain,
% 3.77/0.99      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_3104]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_17976,plain,
% 3.77/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_17880,c_2670,c_3070,c_3105]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3,plain,
% 3.77/0.99      ( r1_tarski(X0,X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2158,plain,
% 3.77/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_17,plain,
% 3.77/0.99      ( v4_relat_1(X0,X1)
% 3.77/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.77/0.99      | ~ v1_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2148,plain,
% 3.77/0.99      ( v4_relat_1(X0,X1) = iProver_top
% 3.77/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4194,plain,
% 3.77/0.99      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2158,c_2148]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_24,plain,
% 3.77/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.77/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2143,plain,
% 3.77/0.99      ( k7_relat_1(X0,X1) = X0
% 3.77/0.99      | v4_relat_1(X0,X1) != iProver_top
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4512,plain,
% 3.77/0.99      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_4194,c_2143]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_17981,plain,
% 3.77/0.99      ( k7_relat_1(sK6,k1_relat_1(sK6)) = sK6 ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_17976,c_4512]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_22,plain,
% 3.77/0.99      ( ~ v1_relat_1(X0)
% 3.77/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2145,plain,
% 3.77/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_17982,plain,
% 3.77/0.99      ( k2_relat_1(k7_relat_1(sK6,X0)) = k9_relat_1(sK6,X0) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_17976,c_2145]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_18074,plain,
% 3.77/0.99      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_17981,c_17982]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_0,plain,
% 3.77/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.77/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2160,plain,
% 3.77/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_25,plain,
% 3.77/0.99      ( v5_relat_1(X0,X1)
% 3.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.77/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_20,plain,
% 3.77/0.99      ( ~ v5_relat_1(X0,X1)
% 3.77/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 3.77/0.99      | ~ v1_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_473,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.77/0.99      | ~ v1_relat_1(X0) ),
% 3.77/0.99      inference(resolution,[status(thm)],[c_25,c_20]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2134,plain,
% 3.77/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.77/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3201,plain,
% 3.77/0.99      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
% 3.77/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2138,c_2134]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3678,plain,
% 3.77/0.99      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_3201,c_2670,c_3070,c_3105]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_11,plain,
% 3.77/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_13,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_428,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 3.77/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_429,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.77/0.99      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.77/0.99      inference(unflattening,[status(thm)],[c_428]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_998,plain,
% 3.77/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.77/0.99      inference(prop_impl,[status(thm)],[c_14]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_999,plain,
% 3.77/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.77/0.99      inference(renaming,[status(thm)],[c_998]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1050,plain,
% 3.77/0.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.77/0.99      inference(bin_hyper_res,[status(thm)],[c_429,c_999]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2133,plain,
% 3.77/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.77/0.99      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1050]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_7,plain,
% 3.77/0.99      ( ~ r2_hidden(X0,X1)
% 3.77/0.99      | ~ r2_hidden(X2,X0)
% 3.77/0.99      | r2_hidden(X2,k3_tarski(X1)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2154,plain,
% 3.77/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.77/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.77/0.99      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4733,plain,
% 3.77/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.77/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.77/0.99      | r2_hidden(X2,k3_tarski(k1_zfmisc_1(X1))) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2133,c_2154]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_10,plain,
% 3.77/0.99      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.77/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4737,plain,
% 3.77/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.77/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.77/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_4733,c_10]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4876,plain,
% 3.77/0.99      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.77/0.99      | r2_hidden(X0,sK5) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_3678,c_4737]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5230,plain,
% 3.77/0.99      ( k2_relat_1(sK6) = k1_xboole_0
% 3.77/0.99      | r2_hidden(sK0(k2_relat_1(sK6)),sK5) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2160,c_4876]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_12,plain,
% 3.77/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2151,plain,
% 3.77/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.77/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6137,plain,
% 3.77/0.99      ( k2_relat_1(sK6) = k1_xboole_0
% 3.77/0.99      | m1_subset_1(sK0(k2_relat_1(sK6)),sK5) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_5230,c_2151]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_28,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2140,plain,
% 3.77/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3403,plain,
% 3.77/0.99      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2138,c_2140]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_29,negated_conjecture,
% 3.77/0.99      ( ~ m1_subset_1(X0,sK5)
% 3.77/0.99      | ~ r2_hidden(X0,k2_relset_1(sK4,sK5,sK6)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2139,plain,
% 3.77/0.99      ( m1_subset_1(X0,sK5) != iProver_top
% 3.77/0.99      | r2_hidden(X0,k2_relset_1(sK4,sK5,sK6)) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2503,plain,
% 3.77/0.99      ( k2_relset_1(sK4,sK5,sK6) = k1_xboole_0
% 3.77/0.99      | m1_subset_1(sK0(k2_relset_1(sK4,sK5,sK6)),sK5) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2160,c_2139]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3531,plain,
% 3.77/0.99      ( k2_relat_1(sK6) = k1_xboole_0
% 3.77/0.99      | m1_subset_1(sK0(k2_relat_1(sK6)),sK5) != iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_3403,c_2503]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6306,plain,
% 3.77/0.99      ( k2_relat_1(sK6) = k1_xboole_0 ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_6137,c_3531]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_18076,plain,
% 3.77/0.99      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k1_xboole_0 ),
% 3.77/0.99      inference(light_normalisation,[status(thm)],[c_18074,c_6306]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_23,plain,
% 3.77/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.77/0.99      | ~ v1_relat_1(X1)
% 3.77/0.99      | k9_relat_1(X1,X0) != k1_xboole_0
% 3.77/0.99      | k1_xboole_0 = X0 ),
% 3.77/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2637,plain,
% 3.77/0.99      ( ~ r1_tarski(k1_relat_1(sK6),k1_relat_1(X0))
% 3.77/0.99      | ~ v1_relat_1(X0)
% 3.77/0.99      | k9_relat_1(X0,k1_relat_1(sK6)) != k1_xboole_0
% 3.77/0.99      | k1_xboole_0 = k1_relat_1(sK6) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4451,plain,
% 3.77/0.99      ( ~ r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6))
% 3.77/0.99      | ~ v1_relat_1(sK6)
% 3.77/0.99      | k9_relat_1(sK6,k1_relat_1(sK6)) != k1_xboole_0
% 3.77/0.99      | k1_xboole_0 = k1_relat_1(sK6) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_2637]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3080,plain,
% 3.77/0.99      ( r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2671,plain,
% 3.77/0.99      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) ),
% 3.77/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2670]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1489,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2415,plain,
% 3.77/0.99      ( k1_relset_1(sK4,sK5,sK6) != X0
% 3.77/0.99      | k1_xboole_0 != X0
% 3.77/0.99      | k1_xboole_0 = k1_relset_1(sK4,sK5,sK6) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_1489]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2491,plain,
% 3.77/0.99      ( k1_relset_1(sK4,sK5,sK6) != k1_relat_1(sK6)
% 3.77/0.99      | k1_xboole_0 = k1_relset_1(sK4,sK5,sK6)
% 3.77/0.99      | k1_xboole_0 != k1_relat_1(sK6) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_2415]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_27,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2418,plain,
% 3.77/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.77/0.99      | k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_27]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_30,negated_conjecture,
% 3.77/0.99      ( k1_xboole_0 != k1_relset_1(sK4,sK5,sK6) ),
% 3.77/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(contradiction,plain,
% 3.77/0.99      ( $false ),
% 3.77/0.99      inference(minisat,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_18076,c_4451,c_3104,c_3080,c_3068,c_2671,c_2491,
% 3.77/0.99                 c_2418,c_30,c_31]) ).
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  ------                               Statistics
% 3.77/0.99  
% 3.77/0.99  ------ General
% 3.77/0.99  
% 3.77/0.99  abstr_ref_over_cycles:                  0
% 3.77/0.99  abstr_ref_under_cycles:                 0
% 3.77/0.99  gc_basic_clause_elim:                   0
% 3.77/0.99  forced_gc_time:                         0
% 3.77/0.99  parsing_time:                           0.009
% 3.77/0.99  unif_index_cands_time:                  0.
% 3.77/0.99  unif_index_add_time:                    0.
% 3.77/0.99  orderings_time:                         0.
% 3.77/0.99  out_proof_time:                         0.01
% 3.77/0.99  total_time:                             0.428
% 3.77/0.99  num_of_symbols:                         55
% 3.77/0.99  num_of_terms:                           19350
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing
% 3.77/0.99  
% 3.77/0.99  num_of_splits:                          0
% 3.77/0.99  num_of_split_atoms:                     0
% 3.77/0.99  num_of_reused_defs:                     0
% 3.77/0.99  num_eq_ax_congr_red:                    44
% 3.77/0.99  num_of_sem_filtered_clauses:            1
% 3.77/0.99  num_of_subtypes:                        0
% 3.77/0.99  monotx_restored_types:                  0
% 3.77/0.99  sat_num_of_epr_types:                   0
% 3.77/0.99  sat_num_of_non_cyclic_types:            0
% 3.77/0.99  sat_guarded_non_collapsed_types:        0
% 3.77/0.99  num_pure_diseq_elim:                    0
% 3.77/0.99  simp_replaced_by:                       0
% 3.77/0.99  res_preprocessed:                       148
% 3.77/0.99  prep_upred:                             0
% 3.77/0.99  prep_unflattend:                        68
% 3.77/0.99  smt_new_axioms:                         0
% 3.77/0.99  pred_elim_cands:                        5
% 3.77/0.99  pred_elim:                              2
% 3.77/0.99  pred_elim_cl:                           3
% 3.77/0.99  pred_elim_cycles:                       6
% 3.77/0.99  merged_defs:                            8
% 3.77/0.99  merged_defs_ncl:                        0
% 3.77/0.99  bin_hyper_res:                          10
% 3.77/0.99  prep_cycles:                            4
% 3.77/0.99  pred_elim_time:                         0.008
% 3.77/0.99  splitting_time:                         0.
% 3.77/0.99  sem_filter_time:                        0.
% 3.77/0.99  monotx_time:                            0.
% 3.77/0.99  subtype_inf_time:                       0.
% 3.77/0.99  
% 3.77/0.99  ------ Problem properties
% 3.77/0.99  
% 3.77/0.99  clauses:                                30
% 3.77/0.99  conjectures:                            3
% 3.77/0.99  epr:                                    6
% 3.77/0.99  horn:                                   27
% 3.77/0.99  ground:                                 2
% 3.77/0.99  unary:                                  5
% 3.77/0.99  binary:                                 14
% 3.77/0.99  lits:                                   68
% 3.77/0.99  lits_eq:                                13
% 3.77/0.99  fd_pure:                                0
% 3.77/0.99  fd_pseudo:                              0
% 3.77/0.99  fd_cond:                                2
% 3.77/0.99  fd_pseudo_cond:                         4
% 3.77/0.99  ac_symbols:                             0
% 3.77/0.99  
% 3.77/0.99  ------ Propositional Solver
% 3.77/0.99  
% 3.77/0.99  prop_solver_calls:                      31
% 3.77/0.99  prop_fast_solver_calls:                 1257
% 3.77/0.99  smt_solver_calls:                       0
% 3.77/0.99  smt_fast_solver_calls:                  0
% 3.77/0.99  prop_num_of_clauses:                    7067
% 3.77/0.99  prop_preprocess_simplified:             13845
% 3.77/0.99  prop_fo_subsumed:                       12
% 3.77/0.99  prop_solver_time:                       0.
% 3.77/0.99  smt_solver_time:                        0.
% 3.77/0.99  smt_fast_solver_time:                   0.
% 3.77/0.99  prop_fast_solver_time:                  0.
% 3.77/0.99  prop_unsat_core_time:                   0.
% 3.77/0.99  
% 3.77/0.99  ------ QBF
% 3.77/0.99  
% 3.77/0.99  qbf_q_res:                              0
% 3.77/0.99  qbf_num_tautologies:                    0
% 3.77/0.99  qbf_prep_cycles:                        0
% 3.77/0.99  
% 3.77/0.99  ------ BMC1
% 3.77/0.99  
% 3.77/0.99  bmc1_current_bound:                     -1
% 3.77/0.99  bmc1_last_solved_bound:                 -1
% 3.77/0.99  bmc1_unsat_core_size:                   -1
% 3.77/0.99  bmc1_unsat_core_parents_size:           -1
% 3.77/0.99  bmc1_merge_next_fun:                    0
% 3.77/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.77/0.99  
% 3.77/0.99  ------ Instantiation
% 3.77/0.99  
% 3.77/0.99  inst_num_of_clauses:                    1708
% 3.77/0.99  inst_num_in_passive:                    800
% 3.77/0.99  inst_num_in_active:                     667
% 3.77/0.99  inst_num_in_unprocessed:                251
% 3.77/0.99  inst_num_of_loops:                      820
% 3.77/0.99  inst_num_of_learning_restarts:          0
% 3.77/0.99  inst_num_moves_active_passive:          149
% 3.77/0.99  inst_lit_activity:                      0
% 3.77/0.99  inst_lit_activity_moves:                0
% 3.77/0.99  inst_num_tautologies:                   0
% 3.77/0.99  inst_num_prop_implied:                  0
% 3.77/0.99  inst_num_existing_simplified:           0
% 3.77/0.99  inst_num_eq_res_simplified:             0
% 3.77/0.99  inst_num_child_elim:                    0
% 3.77/0.99  inst_num_of_dismatching_blockings:      835
% 3.77/0.99  inst_num_of_non_proper_insts:           1736
% 3.77/0.99  inst_num_of_duplicates:                 0
% 3.77/0.99  inst_inst_num_from_inst_to_res:         0
% 3.77/0.99  inst_dismatching_checking_time:         0.
% 3.77/0.99  
% 3.77/0.99  ------ Resolution
% 3.77/0.99  
% 3.77/0.99  res_num_of_clauses:                     0
% 3.77/0.99  res_num_in_passive:                     0
% 3.77/0.99  res_num_in_active:                      0
% 3.77/0.99  res_num_of_loops:                       152
% 3.77/0.99  res_forward_subset_subsumed:            174
% 3.77/0.99  res_backward_subset_subsumed:           22
% 3.77/0.99  res_forward_subsumed:                   0
% 3.77/0.99  res_backward_subsumed:                  0
% 3.77/0.99  res_forward_subsumption_resolution:     0
% 3.77/0.99  res_backward_subsumption_resolution:    0
% 3.77/0.99  res_clause_to_clause_subsumption:       2026
% 3.77/0.99  res_orphan_elimination:                 0
% 3.77/0.99  res_tautology_del:                      104
% 3.77/0.99  res_num_eq_res_simplified:              0
% 3.77/0.99  res_num_sel_changes:                    0
% 3.77/0.99  res_moves_from_active_to_pass:          0
% 3.77/0.99  
% 3.77/0.99  ------ Superposition
% 3.77/0.99  
% 3.77/0.99  sup_time_total:                         0.
% 3.77/0.99  sup_time_generating:                    0.
% 3.77/0.99  sup_time_sim_full:                      0.
% 3.77/0.99  sup_time_sim_immed:                     0.
% 3.77/0.99  
% 3.77/0.99  sup_num_of_clauses:                     428
% 3.77/0.99  sup_num_in_active:                      146
% 3.77/0.99  sup_num_in_passive:                     282
% 3.77/0.99  sup_num_of_loops:                       163
% 3.77/0.99  sup_fw_superposition:                   248
% 3.77/0.99  sup_bw_superposition:                   308
% 3.77/0.99  sup_immediate_simplified:               124
% 3.77/0.99  sup_given_eliminated:                   1
% 3.77/0.99  comparisons_done:                       0
% 3.77/0.99  comparisons_avoided:                    6
% 3.77/0.99  
% 3.77/0.99  ------ Simplifications
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  sim_fw_subset_subsumed:                 22
% 3.77/0.99  sim_bw_subset_subsumed:                 21
% 3.77/0.99  sim_fw_subsumed:                        46
% 3.77/0.99  sim_bw_subsumed:                        28
% 3.77/0.99  sim_fw_subsumption_res:                 0
% 3.77/0.99  sim_bw_subsumption_res:                 0
% 3.77/0.99  sim_tautology_del:                      5
% 3.77/0.99  sim_eq_tautology_del:                   3
% 3.77/0.99  sim_eq_res_simp:                        0
% 3.77/0.99  sim_fw_demodulated:                     11
% 3.77/0.99  sim_bw_demodulated:                     18
% 3.77/0.99  sim_light_normalised:                   11
% 3.77/0.99  sim_joinable_taut:                      0
% 3.77/0.99  sim_joinable_simp:                      0
% 3.77/0.99  sim_ac_normalised:                      0
% 3.77/0.99  sim_smt_subsumption:                    0
% 3.77/0.99  
%------------------------------------------------------------------------------
