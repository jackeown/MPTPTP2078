%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:50 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 404 expanded)
%              Number of clauses        :   98 ( 162 expanded)
%              Number of leaves         :   30 (  90 expanded)
%              Depth                    :   17
%              Number of atoms          :  470 (1317 expanded)
%              Number of equality atoms :  169 ( 333 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f53])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f26])).

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
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f23,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
              | ~ m1_subset_1(X3,X1) )
          & k1_xboole_0 != k2_relset_1(X1,X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(X1,X0,sK4))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k2_relset_1(X1,X0,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k1_relset_1(sK3,X0,X2))
                | ~ m1_subset_1(X3,sK3) )
            & k1_xboole_0 != k2_relset_1(sK3,X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) )
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k2_relset_1(X1,X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,sK2,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,sK2,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK3,sK2,sK4))
        | ~ m1_subset_1(X3,sK3) )
    & k1_xboole_0 != k2_relset_1(sK3,sK2,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f47,f61,f60,f59])).

fof(f95,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f62])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK3,sK2,sK4))
      | ~ m1_subset_1(X3,sK3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f89,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f100,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f75])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f96,plain,(
    k1_xboole_0 != k2_relset_1(sK3,sK2,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2005,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2010,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4735,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_2010])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1998,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10426,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(sK1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4735,c_1998])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1984,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1987,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3743,plain,
    ( k1_relset_1(sK3,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1984,c_1987])).

cnf(c_30,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | ~ r2_hidden(X0,k1_relset_1(sK3,sK2,sK4)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1985,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_relset_1(sK3,sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2587,plain,
    ( k1_relset_1(sK3,sK2,sK4) = k1_xboole_0
    | m1_subset_1(sK1(k1_relset_1(sK3,sK2,sK4)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_1985])).

cnf(c_4088,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(sK1(k1_relat_1(sK4)),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3743,c_2587])).

cnf(c_23028,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10426,c_4088])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_27,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2274,plain,
    ( v4_relat_1(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2275,plain,
    ( v4_relat_1(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2274])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1996,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3281,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK3,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1984,c_1996])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_273,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_274,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_273])).

cnf(c_329,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_19,c_274])).

cnf(c_1980,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_8372,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3281,c_1980])).

cnf(c_23,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1992,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8539,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8372,c_1992])).

cnf(c_21,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4855,plain,
    ( ~ v4_relat_1(X0,sK3)
    | r1_tarski(k1_relat_1(X0),sK3)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_9000,plain,
    ( ~ v4_relat_1(sK4,sK3)
    | r1_tarski(k1_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4855])).

cnf(c_9001,plain,
    ( v4_relat_1(sK4,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9000])).

cnf(c_23270,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23028,c_37,c_2275,c_8539,c_9001])).

cnf(c_26,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1989,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8544,plain,
    ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_8539,c_1989])).

cnf(c_23280,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = sK4 ),
    inference(demodulation,[status(thm)],[c_23270,c_8544])).

cnf(c_1988,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3904,plain,
    ( v4_relat_1(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1984,c_1988])).

cnf(c_25,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1990,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4085,plain,
    ( k7_relat_1(sK4,sK3) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3904,c_1990])).

cnf(c_8545,plain,
    ( k7_relat_1(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_8539,c_4085])).

cnf(c_13,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2000,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1999,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4687,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2000,c_1999])).

cnf(c_84,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_86,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_87,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_94,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_96,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_4832,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4687,c_86,c_87,c_96])).

cnf(c_11,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2002,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_328,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_18,c_274])).

cnf(c_1981,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_2586,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_1981])).

cnf(c_5447,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2002,c_2586])).

cnf(c_5604,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4832,c_5447])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2009,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5814,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5604,c_2009])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2006,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5823,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5814,c_2006])).

cnf(c_24,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1991,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
    | r1_xboole_0(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5880,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5823,c_1991])).

cnf(c_8541,plain,
    ( k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8539,c_5880])).

cnf(c_9200,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8545,c_8541])).

cnf(c_23291,plain,
    ( sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_23280,c_9200])).

cnf(c_1222,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4620,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_4622,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4620])).

cnf(c_22,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3114,plain,
    ( v1_xboole_0(k2_relat_1(sK4))
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2535,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK4))
    | k1_xboole_0 = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1218,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2295,plain,
    ( k2_relset_1(sK3,sK2,sK4) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relset_1(sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_2440,plain,
    ( k2_relset_1(sK3,sK2,sK4) != k2_relat_1(sK4)
    | k1_xboole_0 = k2_relset_1(sK3,sK2,sK4)
    | k1_xboole_0 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2295])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2302,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | k2_relset_1(sK3,sK2,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_95,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_85,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != k2_relset_1(sK3,sK2,sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23291,c_4622,c_3114,c_2535,c_2440,c_2302,c_95,c_13,c_85,c_31,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:40:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.41/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/1.52  
% 6.41/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.41/1.52  
% 6.41/1.52  ------  iProver source info
% 6.41/1.52  
% 6.41/1.52  git: date: 2020-06-30 10:37:57 +0100
% 6.41/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.41/1.52  git: non_committed_changes: false
% 6.41/1.52  git: last_make_outside_of_git: false
% 6.41/1.52  
% 6.41/1.52  ------ 
% 6.41/1.52  
% 6.41/1.52  ------ Input Options
% 6.41/1.52  
% 6.41/1.52  --out_options                           all
% 6.41/1.52  --tptp_safe_out                         true
% 6.41/1.52  --problem_path                          ""
% 6.41/1.52  --include_path                          ""
% 6.41/1.52  --clausifier                            res/vclausify_rel
% 6.41/1.52  --clausifier_options                    --mode clausify
% 6.41/1.52  --stdin                                 false
% 6.41/1.52  --stats_out                             all
% 6.41/1.52  
% 6.41/1.52  ------ General Options
% 6.41/1.52  
% 6.41/1.52  --fof                                   false
% 6.41/1.52  --time_out_real                         305.
% 6.41/1.52  --time_out_virtual                      -1.
% 6.41/1.52  --symbol_type_check                     false
% 6.41/1.52  --clausify_out                          false
% 6.41/1.52  --sig_cnt_out                           false
% 6.41/1.52  --trig_cnt_out                          false
% 6.41/1.52  --trig_cnt_out_tolerance                1.
% 6.41/1.52  --trig_cnt_out_sk_spl                   false
% 6.41/1.52  --abstr_cl_out                          false
% 6.41/1.52  
% 6.41/1.52  ------ Global Options
% 6.41/1.52  
% 6.41/1.52  --schedule                              default
% 6.41/1.52  --add_important_lit                     false
% 6.41/1.52  --prop_solver_per_cl                    1000
% 6.41/1.52  --min_unsat_core                        false
% 6.41/1.52  --soft_assumptions                      false
% 6.41/1.52  --soft_lemma_size                       3
% 6.41/1.52  --prop_impl_unit_size                   0
% 6.41/1.52  --prop_impl_unit                        []
% 6.41/1.52  --share_sel_clauses                     true
% 6.41/1.52  --reset_solvers                         false
% 6.41/1.52  --bc_imp_inh                            [conj_cone]
% 6.41/1.52  --conj_cone_tolerance                   3.
% 6.41/1.52  --extra_neg_conj                        none
% 6.41/1.52  --large_theory_mode                     true
% 6.41/1.52  --prolific_symb_bound                   200
% 6.41/1.52  --lt_threshold                          2000
% 6.41/1.52  --clause_weak_htbl                      true
% 6.41/1.52  --gc_record_bc_elim                     false
% 6.41/1.52  
% 6.41/1.52  ------ Preprocessing Options
% 6.41/1.52  
% 6.41/1.52  --preprocessing_flag                    true
% 6.41/1.52  --time_out_prep_mult                    0.1
% 6.41/1.52  --splitting_mode                        input
% 6.41/1.52  --splitting_grd                         true
% 6.41/1.52  --splitting_cvd                         false
% 6.41/1.52  --splitting_cvd_svl                     false
% 6.41/1.52  --splitting_nvd                         32
% 6.41/1.52  --sub_typing                            true
% 6.41/1.52  --prep_gs_sim                           true
% 6.41/1.52  --prep_unflatten                        true
% 6.41/1.52  --prep_res_sim                          true
% 6.41/1.52  --prep_upred                            true
% 6.41/1.52  --prep_sem_filter                       exhaustive
% 6.41/1.52  --prep_sem_filter_out                   false
% 6.41/1.52  --pred_elim                             true
% 6.41/1.52  --res_sim_input                         true
% 6.41/1.52  --eq_ax_congr_red                       true
% 6.41/1.52  --pure_diseq_elim                       true
% 6.41/1.52  --brand_transform                       false
% 6.41/1.52  --non_eq_to_eq                          false
% 6.41/1.52  --prep_def_merge                        true
% 6.41/1.52  --prep_def_merge_prop_impl              false
% 6.41/1.52  --prep_def_merge_mbd                    true
% 6.41/1.52  --prep_def_merge_tr_red                 false
% 6.41/1.52  --prep_def_merge_tr_cl                  false
% 6.41/1.52  --smt_preprocessing                     true
% 6.41/1.52  --smt_ac_axioms                         fast
% 6.41/1.52  --preprocessed_out                      false
% 6.41/1.52  --preprocessed_stats                    false
% 6.41/1.52  
% 6.41/1.52  ------ Abstraction refinement Options
% 6.41/1.52  
% 6.41/1.52  --abstr_ref                             []
% 6.41/1.52  --abstr_ref_prep                        false
% 6.41/1.52  --abstr_ref_until_sat                   false
% 6.41/1.52  --abstr_ref_sig_restrict                funpre
% 6.41/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 6.41/1.52  --abstr_ref_under                       []
% 6.41/1.52  
% 6.41/1.52  ------ SAT Options
% 6.41/1.52  
% 6.41/1.52  --sat_mode                              false
% 6.41/1.52  --sat_fm_restart_options                ""
% 6.41/1.52  --sat_gr_def                            false
% 6.41/1.52  --sat_epr_types                         true
% 6.41/1.52  --sat_non_cyclic_types                  false
% 6.41/1.52  --sat_finite_models                     false
% 6.41/1.52  --sat_fm_lemmas                         false
% 6.41/1.52  --sat_fm_prep                           false
% 6.41/1.52  --sat_fm_uc_incr                        true
% 6.41/1.52  --sat_out_model                         small
% 6.41/1.52  --sat_out_clauses                       false
% 6.41/1.52  
% 6.41/1.52  ------ QBF Options
% 6.41/1.52  
% 6.41/1.52  --qbf_mode                              false
% 6.41/1.52  --qbf_elim_univ                         false
% 6.41/1.52  --qbf_dom_inst                          none
% 6.41/1.52  --qbf_dom_pre_inst                      false
% 6.41/1.52  --qbf_sk_in                             false
% 6.41/1.52  --qbf_pred_elim                         true
% 6.41/1.52  --qbf_split                             512
% 6.41/1.52  
% 6.41/1.52  ------ BMC1 Options
% 6.41/1.52  
% 6.41/1.52  --bmc1_incremental                      false
% 6.41/1.52  --bmc1_axioms                           reachable_all
% 6.41/1.52  --bmc1_min_bound                        0
% 6.41/1.52  --bmc1_max_bound                        -1
% 6.41/1.52  --bmc1_max_bound_default                -1
% 6.41/1.52  --bmc1_symbol_reachability              true
% 6.41/1.52  --bmc1_property_lemmas                  false
% 6.41/1.52  --bmc1_k_induction                      false
% 6.41/1.52  --bmc1_non_equiv_states                 false
% 6.41/1.52  --bmc1_deadlock                         false
% 6.41/1.52  --bmc1_ucm                              false
% 6.41/1.52  --bmc1_add_unsat_core                   none
% 6.41/1.52  --bmc1_unsat_core_children              false
% 6.41/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 6.41/1.52  --bmc1_out_stat                         full
% 6.41/1.52  --bmc1_ground_init                      false
% 6.41/1.52  --bmc1_pre_inst_next_state              false
% 6.41/1.52  --bmc1_pre_inst_state                   false
% 6.41/1.52  --bmc1_pre_inst_reach_state             false
% 6.41/1.52  --bmc1_out_unsat_core                   false
% 6.41/1.52  --bmc1_aig_witness_out                  false
% 6.41/1.52  --bmc1_verbose                          false
% 6.41/1.52  --bmc1_dump_clauses_tptp                false
% 6.41/1.52  --bmc1_dump_unsat_core_tptp             false
% 6.41/1.52  --bmc1_dump_file                        -
% 6.41/1.52  --bmc1_ucm_expand_uc_limit              128
% 6.41/1.52  --bmc1_ucm_n_expand_iterations          6
% 6.41/1.52  --bmc1_ucm_extend_mode                  1
% 6.41/1.52  --bmc1_ucm_init_mode                    2
% 6.41/1.52  --bmc1_ucm_cone_mode                    none
% 6.41/1.52  --bmc1_ucm_reduced_relation_type        0
% 6.41/1.52  --bmc1_ucm_relax_model                  4
% 6.41/1.52  --bmc1_ucm_full_tr_after_sat            true
% 6.41/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 6.41/1.52  --bmc1_ucm_layered_model                none
% 6.41/1.52  --bmc1_ucm_max_lemma_size               10
% 6.41/1.52  
% 6.41/1.52  ------ AIG Options
% 6.41/1.52  
% 6.41/1.52  --aig_mode                              false
% 6.41/1.52  
% 6.41/1.52  ------ Instantiation Options
% 6.41/1.52  
% 6.41/1.52  --instantiation_flag                    true
% 6.41/1.52  --inst_sos_flag                         false
% 6.41/1.52  --inst_sos_phase                        true
% 6.41/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.41/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.41/1.52  --inst_lit_sel_side                     num_symb
% 6.41/1.52  --inst_solver_per_active                1400
% 6.41/1.52  --inst_solver_calls_frac                1.
% 6.41/1.52  --inst_passive_queue_type               priority_queues
% 6.41/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.41/1.52  --inst_passive_queues_freq              [25;2]
% 6.41/1.52  --inst_dismatching                      true
% 6.41/1.52  --inst_eager_unprocessed_to_passive     true
% 6.41/1.52  --inst_prop_sim_given                   true
% 6.41/1.52  --inst_prop_sim_new                     false
% 6.41/1.52  --inst_subs_new                         false
% 6.41/1.52  --inst_eq_res_simp                      false
% 6.41/1.52  --inst_subs_given                       false
% 6.41/1.52  --inst_orphan_elimination               true
% 6.41/1.52  --inst_learning_loop_flag               true
% 6.41/1.52  --inst_learning_start                   3000
% 6.41/1.52  --inst_learning_factor                  2
% 6.41/1.52  --inst_start_prop_sim_after_learn       3
% 6.41/1.52  --inst_sel_renew                        solver
% 6.41/1.52  --inst_lit_activity_flag                true
% 6.41/1.52  --inst_restr_to_given                   false
% 6.41/1.52  --inst_activity_threshold               500
% 6.41/1.52  --inst_out_proof                        true
% 6.41/1.52  
% 6.41/1.52  ------ Resolution Options
% 6.41/1.52  
% 6.41/1.52  --resolution_flag                       true
% 6.41/1.52  --res_lit_sel                           adaptive
% 6.41/1.52  --res_lit_sel_side                      none
% 6.41/1.52  --res_ordering                          kbo
% 6.41/1.52  --res_to_prop_solver                    active
% 6.41/1.52  --res_prop_simpl_new                    false
% 6.41/1.52  --res_prop_simpl_given                  true
% 6.41/1.52  --res_passive_queue_type                priority_queues
% 6.41/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.41/1.52  --res_passive_queues_freq               [15;5]
% 6.41/1.52  --res_forward_subs                      full
% 6.41/1.52  --res_backward_subs                     full
% 6.41/1.52  --res_forward_subs_resolution           true
% 6.41/1.52  --res_backward_subs_resolution          true
% 6.41/1.52  --res_orphan_elimination                true
% 6.41/1.52  --res_time_limit                        2.
% 6.41/1.52  --res_out_proof                         true
% 6.41/1.52  
% 6.41/1.52  ------ Superposition Options
% 6.41/1.52  
% 6.41/1.52  --superposition_flag                    true
% 6.41/1.52  --sup_passive_queue_type                priority_queues
% 6.41/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.41/1.52  --sup_passive_queues_freq               [8;1;4]
% 6.41/1.52  --demod_completeness_check              fast
% 6.41/1.52  --demod_use_ground                      true
% 6.41/1.52  --sup_to_prop_solver                    passive
% 6.41/1.52  --sup_prop_simpl_new                    true
% 6.41/1.52  --sup_prop_simpl_given                  true
% 6.41/1.52  --sup_fun_splitting                     false
% 6.41/1.52  --sup_smt_interval                      50000
% 6.41/1.52  
% 6.41/1.52  ------ Superposition Simplification Setup
% 6.41/1.52  
% 6.41/1.52  --sup_indices_passive                   []
% 6.41/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 6.41/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.52  --sup_full_bw                           [BwDemod]
% 6.41/1.52  --sup_immed_triv                        [TrivRules]
% 6.41/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.41/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.52  --sup_immed_bw_main                     []
% 6.41/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 6.41/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.52  
% 6.41/1.52  ------ Combination Options
% 6.41/1.52  
% 6.41/1.52  --comb_res_mult                         3
% 6.41/1.52  --comb_sup_mult                         2
% 6.41/1.52  --comb_inst_mult                        10
% 6.41/1.52  
% 6.41/1.52  ------ Debug Options
% 6.41/1.52  
% 6.41/1.52  --dbg_backtrace                         false
% 6.41/1.52  --dbg_dump_prop_clauses                 false
% 6.41/1.52  --dbg_dump_prop_clauses_file            -
% 6.41/1.52  --dbg_out_stat                          false
% 6.41/1.52  ------ Parsing...
% 6.41/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.41/1.52  
% 6.41/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.41/1.52  
% 6.41/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.41/1.52  
% 6.41/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.41/1.52  ------ Proving...
% 6.41/1.52  ------ Problem Properties 
% 6.41/1.52  
% 6.41/1.52  
% 6.41/1.52  clauses                                 34
% 6.41/1.52  conjectures                             5
% 6.41/1.52  EPR                                     13
% 6.41/1.52  Horn                                    32
% 6.41/1.52  unary                                   8
% 6.41/1.52  binary                                  17
% 6.41/1.52  lits                                    69
% 6.41/1.52  lits eq                                 12
% 6.41/1.52  fd_pure                                 0
% 6.41/1.52  fd_pseudo                               0
% 6.41/1.52  fd_cond                                 3
% 6.41/1.52  fd_pseudo_cond                          1
% 6.41/1.52  AC symbols                              0
% 6.41/1.52  
% 6.41/1.52  ------ Schedule dynamic 5 is on 
% 6.41/1.52  
% 6.41/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.41/1.52  
% 6.41/1.52  
% 6.41/1.52  ------ 
% 6.41/1.52  Current options:
% 6.41/1.52  ------ 
% 6.41/1.52  
% 6.41/1.52  ------ Input Options
% 6.41/1.52  
% 6.41/1.52  --out_options                           all
% 6.41/1.52  --tptp_safe_out                         true
% 6.41/1.52  --problem_path                          ""
% 6.41/1.52  --include_path                          ""
% 6.41/1.52  --clausifier                            res/vclausify_rel
% 6.41/1.52  --clausifier_options                    --mode clausify
% 6.41/1.52  --stdin                                 false
% 6.41/1.52  --stats_out                             all
% 6.41/1.52  
% 6.41/1.52  ------ General Options
% 6.41/1.52  
% 6.41/1.52  --fof                                   false
% 6.41/1.52  --time_out_real                         305.
% 6.41/1.52  --time_out_virtual                      -1.
% 6.41/1.52  --symbol_type_check                     false
% 6.41/1.52  --clausify_out                          false
% 6.41/1.52  --sig_cnt_out                           false
% 6.41/1.52  --trig_cnt_out                          false
% 6.41/1.52  --trig_cnt_out_tolerance                1.
% 6.41/1.52  --trig_cnt_out_sk_spl                   false
% 6.41/1.52  --abstr_cl_out                          false
% 6.41/1.52  
% 6.41/1.52  ------ Global Options
% 6.41/1.52  
% 6.41/1.52  --schedule                              default
% 6.41/1.52  --add_important_lit                     false
% 6.41/1.52  --prop_solver_per_cl                    1000
% 6.41/1.52  --min_unsat_core                        false
% 6.41/1.52  --soft_assumptions                      false
% 6.41/1.52  --soft_lemma_size                       3
% 6.41/1.52  --prop_impl_unit_size                   0
% 6.41/1.52  --prop_impl_unit                        []
% 6.41/1.52  --share_sel_clauses                     true
% 6.41/1.52  --reset_solvers                         false
% 6.41/1.52  --bc_imp_inh                            [conj_cone]
% 6.41/1.52  --conj_cone_tolerance                   3.
% 6.41/1.52  --extra_neg_conj                        none
% 6.41/1.52  --large_theory_mode                     true
% 6.41/1.52  --prolific_symb_bound                   200
% 6.41/1.52  --lt_threshold                          2000
% 6.41/1.52  --clause_weak_htbl                      true
% 6.41/1.52  --gc_record_bc_elim                     false
% 6.41/1.52  
% 6.41/1.52  ------ Preprocessing Options
% 6.41/1.52  
% 6.41/1.52  --preprocessing_flag                    true
% 6.41/1.52  --time_out_prep_mult                    0.1
% 6.41/1.52  --splitting_mode                        input
% 6.41/1.52  --splitting_grd                         true
% 6.41/1.52  --splitting_cvd                         false
% 6.41/1.52  --splitting_cvd_svl                     false
% 6.41/1.52  --splitting_nvd                         32
% 6.41/1.52  --sub_typing                            true
% 6.41/1.52  --prep_gs_sim                           true
% 6.41/1.52  --prep_unflatten                        true
% 6.41/1.52  --prep_res_sim                          true
% 6.41/1.52  --prep_upred                            true
% 6.41/1.52  --prep_sem_filter                       exhaustive
% 6.41/1.52  --prep_sem_filter_out                   false
% 6.41/1.52  --pred_elim                             true
% 6.41/1.52  --res_sim_input                         true
% 6.41/1.52  --eq_ax_congr_red                       true
% 6.41/1.52  --pure_diseq_elim                       true
% 6.41/1.52  --brand_transform                       false
% 6.41/1.52  --non_eq_to_eq                          false
% 6.41/1.52  --prep_def_merge                        true
% 6.41/1.52  --prep_def_merge_prop_impl              false
% 6.41/1.52  --prep_def_merge_mbd                    true
% 6.41/1.52  --prep_def_merge_tr_red                 false
% 6.41/1.52  --prep_def_merge_tr_cl                  false
% 6.41/1.52  --smt_preprocessing                     true
% 6.41/1.52  --smt_ac_axioms                         fast
% 6.41/1.52  --preprocessed_out                      false
% 6.41/1.52  --preprocessed_stats                    false
% 6.41/1.52  
% 6.41/1.52  ------ Abstraction refinement Options
% 6.41/1.52  
% 6.41/1.52  --abstr_ref                             []
% 6.41/1.52  --abstr_ref_prep                        false
% 6.41/1.52  --abstr_ref_until_sat                   false
% 6.41/1.52  --abstr_ref_sig_restrict                funpre
% 6.41/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 6.41/1.52  --abstr_ref_under                       []
% 6.41/1.52  
% 6.41/1.52  ------ SAT Options
% 6.41/1.52  
% 6.41/1.52  --sat_mode                              false
% 6.41/1.52  --sat_fm_restart_options                ""
% 6.41/1.52  --sat_gr_def                            false
% 6.41/1.52  --sat_epr_types                         true
% 6.41/1.52  --sat_non_cyclic_types                  false
% 6.41/1.52  --sat_finite_models                     false
% 6.41/1.52  --sat_fm_lemmas                         false
% 6.41/1.52  --sat_fm_prep                           false
% 6.41/1.52  --sat_fm_uc_incr                        true
% 6.41/1.52  --sat_out_model                         small
% 6.41/1.52  --sat_out_clauses                       false
% 6.41/1.52  
% 6.41/1.52  ------ QBF Options
% 6.41/1.52  
% 6.41/1.52  --qbf_mode                              false
% 6.41/1.52  --qbf_elim_univ                         false
% 6.41/1.52  --qbf_dom_inst                          none
% 6.41/1.52  --qbf_dom_pre_inst                      false
% 6.41/1.52  --qbf_sk_in                             false
% 6.41/1.52  --qbf_pred_elim                         true
% 6.41/1.52  --qbf_split                             512
% 6.41/1.52  
% 6.41/1.52  ------ BMC1 Options
% 6.41/1.52  
% 6.41/1.52  --bmc1_incremental                      false
% 6.41/1.52  --bmc1_axioms                           reachable_all
% 6.41/1.52  --bmc1_min_bound                        0
% 6.41/1.52  --bmc1_max_bound                        -1
% 6.41/1.52  --bmc1_max_bound_default                -1
% 6.41/1.52  --bmc1_symbol_reachability              true
% 6.41/1.52  --bmc1_property_lemmas                  false
% 6.41/1.52  --bmc1_k_induction                      false
% 6.41/1.52  --bmc1_non_equiv_states                 false
% 6.41/1.52  --bmc1_deadlock                         false
% 6.41/1.52  --bmc1_ucm                              false
% 6.41/1.52  --bmc1_add_unsat_core                   none
% 6.41/1.52  --bmc1_unsat_core_children              false
% 6.41/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 6.41/1.52  --bmc1_out_stat                         full
% 6.41/1.52  --bmc1_ground_init                      false
% 6.41/1.52  --bmc1_pre_inst_next_state              false
% 6.41/1.52  --bmc1_pre_inst_state                   false
% 6.41/1.52  --bmc1_pre_inst_reach_state             false
% 6.41/1.52  --bmc1_out_unsat_core                   false
% 6.41/1.52  --bmc1_aig_witness_out                  false
% 6.41/1.52  --bmc1_verbose                          false
% 6.41/1.52  --bmc1_dump_clauses_tptp                false
% 6.41/1.52  --bmc1_dump_unsat_core_tptp             false
% 6.41/1.52  --bmc1_dump_file                        -
% 6.41/1.52  --bmc1_ucm_expand_uc_limit              128
% 6.41/1.52  --bmc1_ucm_n_expand_iterations          6
% 6.41/1.52  --bmc1_ucm_extend_mode                  1
% 6.41/1.52  --bmc1_ucm_init_mode                    2
% 6.41/1.52  --bmc1_ucm_cone_mode                    none
% 6.41/1.52  --bmc1_ucm_reduced_relation_type        0
% 6.41/1.52  --bmc1_ucm_relax_model                  4
% 6.41/1.52  --bmc1_ucm_full_tr_after_sat            true
% 6.41/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 6.41/1.52  --bmc1_ucm_layered_model                none
% 6.41/1.52  --bmc1_ucm_max_lemma_size               10
% 6.41/1.52  
% 6.41/1.52  ------ AIG Options
% 6.41/1.52  
% 6.41/1.52  --aig_mode                              false
% 6.41/1.52  
% 6.41/1.52  ------ Instantiation Options
% 6.41/1.52  
% 6.41/1.52  --instantiation_flag                    true
% 6.41/1.52  --inst_sos_flag                         false
% 6.41/1.52  --inst_sos_phase                        true
% 6.41/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.41/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.41/1.52  --inst_lit_sel_side                     none
% 6.41/1.52  --inst_solver_per_active                1400
% 6.41/1.52  --inst_solver_calls_frac                1.
% 6.41/1.52  --inst_passive_queue_type               priority_queues
% 6.41/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.41/1.52  --inst_passive_queues_freq              [25;2]
% 6.41/1.52  --inst_dismatching                      true
% 6.41/1.52  --inst_eager_unprocessed_to_passive     true
% 6.41/1.52  --inst_prop_sim_given                   true
% 6.41/1.52  --inst_prop_sim_new                     false
% 6.41/1.52  --inst_subs_new                         false
% 6.41/1.52  --inst_eq_res_simp                      false
% 6.41/1.52  --inst_subs_given                       false
% 6.41/1.52  --inst_orphan_elimination               true
% 6.41/1.52  --inst_learning_loop_flag               true
% 6.41/1.52  --inst_learning_start                   3000
% 6.41/1.52  --inst_learning_factor                  2
% 6.41/1.52  --inst_start_prop_sim_after_learn       3
% 6.41/1.52  --inst_sel_renew                        solver
% 6.41/1.52  --inst_lit_activity_flag                true
% 6.41/1.52  --inst_restr_to_given                   false
% 6.41/1.52  --inst_activity_threshold               500
% 6.41/1.52  --inst_out_proof                        true
% 6.41/1.52  
% 6.41/1.52  ------ Resolution Options
% 6.41/1.52  
% 6.41/1.52  --resolution_flag                       false
% 6.41/1.52  --res_lit_sel                           adaptive
% 6.41/1.52  --res_lit_sel_side                      none
% 6.41/1.52  --res_ordering                          kbo
% 6.41/1.52  --res_to_prop_solver                    active
% 6.41/1.52  --res_prop_simpl_new                    false
% 6.41/1.52  --res_prop_simpl_given                  true
% 6.41/1.52  --res_passive_queue_type                priority_queues
% 6.41/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.41/1.52  --res_passive_queues_freq               [15;5]
% 6.41/1.52  --res_forward_subs                      full
% 6.41/1.52  --res_backward_subs                     full
% 6.41/1.52  --res_forward_subs_resolution           true
% 6.41/1.52  --res_backward_subs_resolution          true
% 6.41/1.52  --res_orphan_elimination                true
% 6.41/1.52  --res_time_limit                        2.
% 6.41/1.52  --res_out_proof                         true
% 6.41/1.52  
% 6.41/1.52  ------ Superposition Options
% 6.41/1.52  
% 6.41/1.52  --superposition_flag                    true
% 6.41/1.52  --sup_passive_queue_type                priority_queues
% 6.41/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.41/1.52  --sup_passive_queues_freq               [8;1;4]
% 6.41/1.52  --demod_completeness_check              fast
% 6.41/1.52  --demod_use_ground                      true
% 6.41/1.52  --sup_to_prop_solver                    passive
% 6.41/1.52  --sup_prop_simpl_new                    true
% 6.41/1.52  --sup_prop_simpl_given                  true
% 6.41/1.52  --sup_fun_splitting                     false
% 6.41/1.52  --sup_smt_interval                      50000
% 6.41/1.52  
% 6.41/1.52  ------ Superposition Simplification Setup
% 6.41/1.52  
% 6.41/1.52  --sup_indices_passive                   []
% 6.41/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 6.41/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.52  --sup_full_bw                           [BwDemod]
% 6.41/1.52  --sup_immed_triv                        [TrivRules]
% 6.41/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.41/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.52  --sup_immed_bw_main                     []
% 6.41/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 6.41/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.52  
% 6.41/1.52  ------ Combination Options
% 6.41/1.52  
% 6.41/1.52  --comb_res_mult                         3
% 6.41/1.52  --comb_sup_mult                         2
% 6.41/1.52  --comb_inst_mult                        10
% 6.41/1.52  
% 6.41/1.52  ------ Debug Options
% 6.41/1.52  
% 6.41/1.52  --dbg_backtrace                         false
% 6.41/1.52  --dbg_dump_prop_clauses                 false
% 6.41/1.52  --dbg_dump_prop_clauses_file            -
% 6.41/1.52  --dbg_out_stat                          false
% 6.41/1.52  
% 6.41/1.52  
% 6.41/1.52  
% 6.41/1.52  
% 6.41/1.52  ------ Proving...
% 6.41/1.52  
% 6.41/1.52  
% 6.41/1.52  % SZS status Theorem for theBenchmark.p
% 6.41/1.52  
% 6.41/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 6.41/1.52  
% 6.41/1.52  fof(f5,axiom,(
% 6.41/1.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f29,plain,(
% 6.41/1.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 6.41/1.52    inference(ennf_transformation,[],[f5])).
% 6.41/1.52  
% 6.41/1.52  fof(f53,plain,(
% 6.41/1.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 6.41/1.52    introduced(choice_axiom,[])).
% 6.41/1.52  
% 6.41/1.52  fof(f54,plain,(
% 6.41/1.52    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 6.41/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f53])).
% 6.41/1.52  
% 6.41/1.52  fof(f70,plain,(
% 6.41/1.52    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 6.41/1.52    inference(cnf_transformation,[],[f54])).
% 6.41/1.52  
% 6.41/1.52  fof(f1,axiom,(
% 6.41/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f26,plain,(
% 6.41/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.41/1.52    inference(ennf_transformation,[],[f1])).
% 6.41/1.52  
% 6.41/1.52  fof(f48,plain,(
% 6.41/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.41/1.52    inference(nnf_transformation,[],[f26])).
% 6.41/1.52  
% 6.41/1.52  fof(f49,plain,(
% 6.41/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.41/1.52    inference(rectify,[],[f48])).
% 6.41/1.52  
% 6.41/1.52  fof(f50,plain,(
% 6.41/1.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 6.41/1.52    introduced(choice_axiom,[])).
% 6.41/1.52  
% 6.41/1.52  fof(f51,plain,(
% 6.41/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.41/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).
% 6.41/1.52  
% 6.41/1.52  fof(f63,plain,(
% 6.41/1.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f51])).
% 6.41/1.52  
% 6.41/1.52  fof(f10,axiom,(
% 6.41/1.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f33,plain,(
% 6.41/1.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 6.41/1.52    inference(ennf_transformation,[],[f10])).
% 6.41/1.52  
% 6.41/1.52  fof(f78,plain,(
% 6.41/1.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f33])).
% 6.41/1.52  
% 6.41/1.52  fof(f23,conjecture,(
% 6.41/1.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f24,negated_conjecture,(
% 6.41/1.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 6.41/1.52    inference(negated_conjecture,[],[f23])).
% 6.41/1.52  
% 6.41/1.52  fof(f46,plain,(
% 6.41/1.52    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.41/1.52    inference(ennf_transformation,[],[f24])).
% 6.41/1.52  
% 6.41/1.52  fof(f47,plain,(
% 6.41/1.52    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.41/1.52    inference(flattening,[],[f46])).
% 6.41/1.52  
% 6.41/1.52  fof(f61,plain,(
% 6.41/1.52    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,sK4)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))) )),
% 6.41/1.52    introduced(choice_axiom,[])).
% 6.41/1.52  
% 6.41/1.52  fof(f60,plain,(
% 6.41/1.52    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK3,X0,X2)) | ~m1_subset_1(X3,sK3)) & k1_xboole_0 != k2_relset_1(sK3,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))) & ~v1_xboole_0(sK3))) )),
% 6.41/1.52    introduced(choice_axiom,[])).
% 6.41/1.52  
% 6.41/1.52  fof(f59,plain,(
% 6.41/1.52    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK2,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK2,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 6.41/1.52    introduced(choice_axiom,[])).
% 6.41/1.52  
% 6.41/1.52  fof(f62,plain,(
% 6.41/1.52    ((! [X3] : (~r2_hidden(X3,k1_relset_1(sK3,sK2,sK4)) | ~m1_subset_1(X3,sK3)) & k1_xboole_0 != k2_relset_1(sK3,sK2,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 6.41/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f47,f61,f60,f59])).
% 6.41/1.52  
% 6.41/1.52  fof(f95,plain,(
% 6.41/1.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 6.41/1.52    inference(cnf_transformation,[],[f62])).
% 6.41/1.52  
% 6.41/1.52  fof(f21,axiom,(
% 6.41/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f44,plain,(
% 6.41/1.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.52    inference(ennf_transformation,[],[f21])).
% 6.41/1.52  
% 6.41/1.52  fof(f91,plain,(
% 6.41/1.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.41/1.52    inference(cnf_transformation,[],[f44])).
% 6.41/1.52  
% 6.41/1.52  fof(f97,plain,(
% 6.41/1.52    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK3,sK2,sK4)) | ~m1_subset_1(X3,sK3)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f62])).
% 6.41/1.52  
% 6.41/1.52  fof(f20,axiom,(
% 6.41/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f25,plain,(
% 6.41/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 6.41/1.52    inference(pure_predicate_removal,[],[f20])).
% 6.41/1.52  
% 6.41/1.52  fof(f43,plain,(
% 6.41/1.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.52    inference(ennf_transformation,[],[f25])).
% 6.41/1.52  
% 6.41/1.52  fof(f90,plain,(
% 6.41/1.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.41/1.52    inference(cnf_transformation,[],[f43])).
% 6.41/1.52  
% 6.41/1.52  fof(f11,axiom,(
% 6.41/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f57,plain,(
% 6.41/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.41/1.52    inference(nnf_transformation,[],[f11])).
% 6.41/1.52  
% 6.41/1.52  fof(f79,plain,(
% 6.41/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.41/1.52    inference(cnf_transformation,[],[f57])).
% 6.41/1.52  
% 6.41/1.52  fof(f13,axiom,(
% 6.41/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f35,plain,(
% 6.41/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 6.41/1.52    inference(ennf_transformation,[],[f13])).
% 6.41/1.52  
% 6.41/1.52  fof(f82,plain,(
% 6.41/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f35])).
% 6.41/1.52  
% 6.41/1.52  fof(f80,plain,(
% 6.41/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f57])).
% 6.41/1.52  
% 6.41/1.52  fof(f16,axiom,(
% 6.41/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f86,plain,(
% 6.41/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 6.41/1.52    inference(cnf_transformation,[],[f16])).
% 6.41/1.52  
% 6.41/1.52  fof(f14,axiom,(
% 6.41/1.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f36,plain,(
% 6.41/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.41/1.52    inference(ennf_transformation,[],[f14])).
% 6.41/1.52  
% 6.41/1.52  fof(f58,plain,(
% 6.41/1.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.41/1.52    inference(nnf_transformation,[],[f36])).
% 6.41/1.52  
% 6.41/1.52  fof(f83,plain,(
% 6.41/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f58])).
% 6.41/1.52  
% 6.41/1.52  fof(f19,axiom,(
% 6.41/1.52    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f42,plain,(
% 6.41/1.52    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 6.41/1.52    inference(ennf_transformation,[],[f19])).
% 6.41/1.52  
% 6.41/1.52  fof(f89,plain,(
% 6.41/1.52    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f42])).
% 6.41/1.52  
% 6.41/1.52  fof(f18,axiom,(
% 6.41/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f40,plain,(
% 6.41/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.41/1.52    inference(ennf_transformation,[],[f18])).
% 6.41/1.52  
% 6.41/1.52  fof(f41,plain,(
% 6.41/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.41/1.52    inference(flattening,[],[f40])).
% 6.41/1.52  
% 6.41/1.52  fof(f88,plain,(
% 6.41/1.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f41])).
% 6.41/1.52  
% 6.41/1.52  fof(f8,axiom,(
% 6.41/1.52    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f30,plain,(
% 6.41/1.52    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 6.41/1.52    inference(ennf_transformation,[],[f8])).
% 6.41/1.52  
% 6.41/1.52  fof(f75,plain,(
% 6.41/1.52    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f30])).
% 6.41/1.52  
% 6.41/1.52  fof(f100,plain,(
% 6.41/1.52    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 6.41/1.52    inference(equality_resolution,[],[f75])).
% 6.41/1.52  
% 6.41/1.52  fof(f9,axiom,(
% 6.41/1.52    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f31,plain,(
% 6.41/1.52    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 6.41/1.52    inference(ennf_transformation,[],[f9])).
% 6.41/1.52  
% 6.41/1.52  fof(f32,plain,(
% 6.41/1.52    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 6.41/1.52    inference(flattening,[],[f31])).
% 6.41/1.52  
% 6.41/1.52  fof(f77,plain,(
% 6.41/1.52    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f32])).
% 6.41/1.52  
% 6.41/1.52  fof(f6,axiom,(
% 6.41/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f55,plain,(
% 6.41/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.41/1.52    inference(nnf_transformation,[],[f6])).
% 6.41/1.52  
% 6.41/1.52  fof(f56,plain,(
% 6.41/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.41/1.52    inference(flattening,[],[f55])).
% 6.41/1.52  
% 6.41/1.52  fof(f71,plain,(
% 6.41/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.41/1.52    inference(cnf_transformation,[],[f56])).
% 6.41/1.52  
% 6.41/1.52  fof(f99,plain,(
% 6.41/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.41/1.52    inference(equality_resolution,[],[f71])).
% 6.41/1.52  
% 6.41/1.52  fof(f7,axiom,(
% 6.41/1.52    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f74,plain,(
% 6.41/1.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f7])).
% 6.41/1.52  
% 6.41/1.52  fof(f12,axiom,(
% 6.41/1.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f34,plain,(
% 6.41/1.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 6.41/1.52    inference(ennf_transformation,[],[f12])).
% 6.41/1.52  
% 6.41/1.52  fof(f81,plain,(
% 6.41/1.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f34])).
% 6.41/1.52  
% 6.41/1.52  fof(f2,axiom,(
% 6.41/1.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f52,plain,(
% 6.41/1.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 6.41/1.52    inference(nnf_transformation,[],[f2])).
% 6.41/1.52  
% 6.41/1.52  fof(f67,plain,(
% 6.41/1.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 6.41/1.52    inference(cnf_transformation,[],[f52])).
% 6.41/1.52  
% 6.41/1.52  fof(f4,axiom,(
% 6.41/1.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f28,plain,(
% 6.41/1.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 6.41/1.52    inference(ennf_transformation,[],[f4])).
% 6.41/1.52  
% 6.41/1.52  fof(f69,plain,(
% 6.41/1.52    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f28])).
% 6.41/1.52  
% 6.41/1.52  fof(f17,axiom,(
% 6.41/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f38,plain,(
% 6.41/1.52    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 6.41/1.52    inference(ennf_transformation,[],[f17])).
% 6.41/1.52  
% 6.41/1.52  fof(f39,plain,(
% 6.41/1.52    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 6.41/1.52    inference(flattening,[],[f38])).
% 6.41/1.52  
% 6.41/1.52  fof(f87,plain,(
% 6.41/1.52    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f39])).
% 6.41/1.52  
% 6.41/1.52  fof(f15,axiom,(
% 6.41/1.52    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 6.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.52  
% 6.41/1.52  fof(f37,plain,(
% 6.41/1.52    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 6.41/1.52    inference(ennf_transformation,[],[f15])).
% 6.41/1.52  
% 6.41/1.52  fof(f85,plain,(
% 6.41/1.52    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 6.41/1.52    inference(cnf_transformation,[],[f37])).
% 6.41/1.52  
% 6.41/1.52  fof(f3,axiom,(
% 6.41/1.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 6.41/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.53  
% 6.41/1.53  fof(f27,plain,(
% 6.41/1.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 6.41/1.53    inference(ennf_transformation,[],[f3])).
% 6.41/1.53  
% 6.41/1.53  fof(f68,plain,(
% 6.41/1.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 6.41/1.53    inference(cnf_transformation,[],[f27])).
% 6.41/1.53  
% 6.41/1.53  fof(f22,axiom,(
% 6.41/1.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 6.41/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.53  
% 6.41/1.53  fof(f45,plain,(
% 6.41/1.53    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.41/1.53    inference(ennf_transformation,[],[f22])).
% 6.41/1.53  
% 6.41/1.53  fof(f92,plain,(
% 6.41/1.53    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.41/1.53    inference(cnf_transformation,[],[f45])).
% 6.41/1.53  
% 6.41/1.53  fof(f96,plain,(
% 6.41/1.53    k1_xboole_0 != k2_relset_1(sK3,sK2,sK4)),
% 6.41/1.53    inference(cnf_transformation,[],[f62])).
% 6.41/1.53  
% 6.41/1.53  cnf(c_7,plain,
% 6.41/1.53      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 6.41/1.53      inference(cnf_transformation,[],[f70]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2005,plain,
% 6.41/1.53      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2,plain,
% 6.41/1.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 6.41/1.53      inference(cnf_transformation,[],[f63]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2010,plain,
% 6.41/1.53      ( r2_hidden(X0,X1) != iProver_top
% 6.41/1.53      | r2_hidden(X0,X2) = iProver_top
% 6.41/1.53      | r1_tarski(X1,X2) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_4735,plain,
% 6.41/1.53      ( k1_xboole_0 = X0
% 6.41/1.53      | r2_hidden(sK1(X0),X1) = iProver_top
% 6.41/1.53      | r1_tarski(X0,X1) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_2005,c_2010]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_15,plain,
% 6.41/1.53      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 6.41/1.53      inference(cnf_transformation,[],[f78]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1998,plain,
% 6.41/1.53      ( m1_subset_1(X0,X1) = iProver_top
% 6.41/1.53      | r2_hidden(X0,X1) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_10426,plain,
% 6.41/1.53      ( k1_xboole_0 = X0
% 6.41/1.53      | m1_subset_1(sK1(X0),X1) = iProver_top
% 6.41/1.53      | r1_tarski(X0,X1) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_4735,c_1998]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_32,negated_conjecture,
% 6.41/1.53      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 6.41/1.53      inference(cnf_transformation,[],[f95]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1984,plain,
% 6.41/1.53      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_28,plain,
% 6.41/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f91]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1987,plain,
% 6.41/1.53      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.41/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3743,plain,
% 6.41/1.53      ( k1_relset_1(sK3,sK2,sK4) = k1_relat_1(sK4) ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_1984,c_1987]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_30,negated_conjecture,
% 6.41/1.53      ( ~ m1_subset_1(X0,sK3)
% 6.41/1.53      | ~ r2_hidden(X0,k1_relset_1(sK3,sK2,sK4)) ),
% 6.41/1.53      inference(cnf_transformation,[],[f97]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1985,plain,
% 6.41/1.53      ( m1_subset_1(X0,sK3) != iProver_top
% 6.41/1.53      | r2_hidden(X0,k1_relset_1(sK3,sK2,sK4)) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2587,plain,
% 6.41/1.53      ( k1_relset_1(sK3,sK2,sK4) = k1_xboole_0
% 6.41/1.53      | m1_subset_1(sK1(k1_relset_1(sK3,sK2,sK4)),sK3) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_2005,c_1985]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_4088,plain,
% 6.41/1.53      ( k1_relat_1(sK4) = k1_xboole_0
% 6.41/1.53      | m1_subset_1(sK1(k1_relat_1(sK4)),sK3) != iProver_top ),
% 6.41/1.53      inference(demodulation,[status(thm)],[c_3743,c_2587]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_23028,plain,
% 6.41/1.53      ( k1_relat_1(sK4) = k1_xboole_0
% 6.41/1.53      | r1_tarski(k1_relat_1(sK4),sK3) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_10426,c_4088]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_37,plain,
% 6.41/1.53      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_27,plain,
% 6.41/1.53      ( v4_relat_1(X0,X1)
% 6.41/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.41/1.53      inference(cnf_transformation,[],[f90]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2274,plain,
% 6.41/1.53      ( v4_relat_1(sK4,sK3)
% 6.41/1.53      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_27]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2275,plain,
% 6.41/1.53      ( v4_relat_1(sK4,sK3) = iProver_top
% 6.41/1.53      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_2274]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_17,plain,
% 6.41/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.41/1.53      inference(cnf_transformation,[],[f79]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1996,plain,
% 6.41/1.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.41/1.53      | r1_tarski(X0,X1) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3281,plain,
% 6.41/1.53      ( r1_tarski(sK4,k2_zfmisc_1(sK3,sK2)) = iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_1984,c_1996]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_19,plain,
% 6.41/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.41/1.53      | ~ v1_relat_1(X1)
% 6.41/1.53      | v1_relat_1(X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f82]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_16,plain,
% 6.41/1.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.41/1.53      inference(cnf_transformation,[],[f80]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_273,plain,
% 6.41/1.53      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 6.41/1.53      inference(prop_impl,[status(thm)],[c_16]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_274,plain,
% 6.41/1.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.41/1.53      inference(renaming,[status(thm)],[c_273]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_329,plain,
% 6.41/1.53      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 6.41/1.53      inference(bin_hyper_res,[status(thm)],[c_19,c_274]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1980,plain,
% 6.41/1.53      ( r1_tarski(X0,X1) != iProver_top
% 6.41/1.53      | v1_relat_1(X1) != iProver_top
% 6.41/1.53      | v1_relat_1(X0) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_8372,plain,
% 6.41/1.53      ( v1_relat_1(k2_zfmisc_1(sK3,sK2)) != iProver_top
% 6.41/1.53      | v1_relat_1(sK4) = iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_3281,c_1980]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_23,plain,
% 6.41/1.53      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 6.41/1.53      inference(cnf_transformation,[],[f86]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1992,plain,
% 6.41/1.53      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_8539,plain,
% 6.41/1.53      ( v1_relat_1(sK4) = iProver_top ),
% 6.41/1.53      inference(forward_subsumption_resolution,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_8372,c_1992]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_21,plain,
% 6.41/1.53      ( ~ v4_relat_1(X0,X1)
% 6.41/1.53      | r1_tarski(k1_relat_1(X0),X1)
% 6.41/1.53      | ~ v1_relat_1(X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f83]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_4855,plain,
% 6.41/1.53      ( ~ v4_relat_1(X0,sK3)
% 6.41/1.53      | r1_tarski(k1_relat_1(X0),sK3)
% 6.41/1.53      | ~ v1_relat_1(X0) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_21]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_9000,plain,
% 6.41/1.53      ( ~ v4_relat_1(sK4,sK3)
% 6.41/1.53      | r1_tarski(k1_relat_1(sK4),sK3)
% 6.41/1.53      | ~ v1_relat_1(sK4) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_4855]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_9001,plain,
% 6.41/1.53      ( v4_relat_1(sK4,sK3) != iProver_top
% 6.41/1.53      | r1_tarski(k1_relat_1(sK4),sK3) = iProver_top
% 6.41/1.53      | v1_relat_1(sK4) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_9000]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_23270,plain,
% 6.41/1.53      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 6.41/1.53      inference(global_propositional_subsumption,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_23028,c_37,c_2275,c_8539,c_9001]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_26,plain,
% 6.41/1.53      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 6.41/1.53      inference(cnf_transformation,[],[f89]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1989,plain,
% 6.41/1.53      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 6.41/1.53      | v1_relat_1(X0) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_8544,plain,
% 6.41/1.53      ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_8539,c_1989]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_23280,plain,
% 6.41/1.53      ( k7_relat_1(sK4,k1_xboole_0) = sK4 ),
% 6.41/1.53      inference(demodulation,[status(thm)],[c_23270,c_8544]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1988,plain,
% 6.41/1.53      ( v4_relat_1(X0,X1) = iProver_top
% 6.41/1.53      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3904,plain,
% 6.41/1.53      ( v4_relat_1(sK4,sK3) = iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_1984,c_1988]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_25,plain,
% 6.41/1.53      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 6.41/1.53      inference(cnf_transformation,[],[f88]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1990,plain,
% 6.41/1.53      ( k7_relat_1(X0,X1) = X0
% 6.41/1.53      | v4_relat_1(X0,X1) != iProver_top
% 6.41/1.53      | v1_relat_1(X0) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_4085,plain,
% 6.41/1.53      ( k7_relat_1(sK4,sK3) = sK4 | v1_relat_1(sK4) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_3904,c_1990]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_8545,plain,
% 6.41/1.53      ( k7_relat_1(sK4,sK3) = sK4 ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_8539,c_4085]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_13,plain,
% 6.41/1.53      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f100]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2000,plain,
% 6.41/1.53      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_14,plain,
% 6.41/1.53      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f77]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1999,plain,
% 6.41/1.53      ( r1_xboole_0(X0,X1) != iProver_top
% 6.41/1.53      | r1_tarski(X0,X1) != iProver_top
% 6.41/1.53      | v1_xboole_0(X0) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_4687,plain,
% 6.41/1.53      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 6.41/1.53      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_2000,c_1999]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_84,plain,
% 6.41/1.53      ( r1_xboole_0(X0,X1) != iProver_top
% 6.41/1.53      | r1_tarski(X0,X1) != iProver_top
% 6.41/1.53      | v1_xboole_0(X0) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_86,plain,
% 6.41/1.53      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 6.41/1.53      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 6.41/1.53      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_84]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_87,plain,
% 6.41/1.53      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_10,plain,
% 6.41/1.53      ( r1_tarski(X0,X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f99]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_94,plain,
% 6.41/1.53      ( r1_tarski(X0,X0) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_96,plain,
% 6.41/1.53      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_94]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_4832,plain,
% 6.41/1.53      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 6.41/1.53      inference(global_propositional_subsumption,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_4687,c_86,c_87,c_96]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_11,plain,
% 6.41/1.53      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f74]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2002,plain,
% 6.41/1.53      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_18,plain,
% 6.41/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.41/1.53      | ~ r2_hidden(X2,X0)
% 6.41/1.53      | ~ v1_xboole_0(X1) ),
% 6.41/1.53      inference(cnf_transformation,[],[f81]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_328,plain,
% 6.41/1.53      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 6.41/1.53      inference(bin_hyper_res,[status(thm)],[c_18,c_274]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1981,plain,
% 6.41/1.53      ( r2_hidden(X0,X1) != iProver_top
% 6.41/1.53      | r1_tarski(X1,X2) != iProver_top
% 6.41/1.53      | v1_xboole_0(X2) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2586,plain,
% 6.41/1.53      ( k1_xboole_0 = X0
% 6.41/1.53      | r1_tarski(X0,X1) != iProver_top
% 6.41/1.53      | v1_xboole_0(X1) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_2005,c_1981]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_5447,plain,
% 6.41/1.53      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 6.41/1.53      | v1_xboole_0(X0) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_2002,c_2586]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_5604,plain,
% 6.41/1.53      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_4832,c_5447]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3,plain,
% 6.41/1.53      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 6.41/1.53      inference(cnf_transformation,[],[f67]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2009,plain,
% 6.41/1.53      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 6.41/1.53      | r1_xboole_0(X0,X1) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_5814,plain,
% 6.41/1.53      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_5604,c_2009]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_6,plain,
% 6.41/1.53      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f69]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2006,plain,
% 6.41/1.53      ( r1_xboole_0(X0,X1) != iProver_top
% 6.41/1.53      | r1_xboole_0(X1,X0) = iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_5823,plain,
% 6.41/1.53      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_5814,c_2006]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_24,plain,
% 6.41/1.53      ( ~ r1_xboole_0(X0,X1)
% 6.41/1.53      | ~ v1_relat_1(X2)
% 6.41/1.53      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 6.41/1.53      inference(cnf_transformation,[],[f87]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1991,plain,
% 6.41/1.53      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
% 6.41/1.53      | r1_xboole_0(X1,X2) != iProver_top
% 6.41/1.53      | v1_relat_1(X0) != iProver_top ),
% 6.41/1.53      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_5880,plain,
% 6.41/1.53      ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
% 6.41/1.53      | v1_relat_1(X0) != iProver_top ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_5823,c_1991]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_8541,plain,
% 6.41/1.53      ( k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0) = k1_xboole_0 ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_8539,c_5880]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_9200,plain,
% 6.41/1.53      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 6.41/1.53      inference(superposition,[status(thm)],[c_8545,c_8541]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_23291,plain,
% 6.41/1.53      ( sK4 = k1_xboole_0 ),
% 6.41/1.53      inference(light_normalisation,[status(thm)],[c_23280,c_9200]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1222,plain,
% 6.41/1.53      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 6.41/1.53      theory(equality) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_4620,plain,
% 6.41/1.53      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_1222]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_4622,plain,
% 6.41/1.53      ( v1_xboole_0(sK4)
% 6.41/1.53      | ~ v1_xboole_0(k1_xboole_0)
% 6.41/1.53      | sK4 != k1_xboole_0 ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_4620]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_22,plain,
% 6.41/1.53      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0)) ),
% 6.41/1.53      inference(cnf_transformation,[],[f85]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_3114,plain,
% 6.41/1.53      ( v1_xboole_0(k2_relat_1(sK4)) | ~ v1_xboole_0(sK4) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_22]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_5,plain,
% 6.41/1.53      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 6.41/1.53      inference(cnf_transformation,[],[f68]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2535,plain,
% 6.41/1.53      ( ~ v1_xboole_0(k2_relat_1(sK4)) | k1_xboole_0 = k2_relat_1(sK4) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_5]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_1218,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2295,plain,
% 6.41/1.53      ( k2_relset_1(sK3,sK2,sK4) != X0
% 6.41/1.53      | k1_xboole_0 != X0
% 6.41/1.53      | k1_xboole_0 = k2_relset_1(sK3,sK2,sK4) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_1218]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2440,plain,
% 6.41/1.53      ( k2_relset_1(sK3,sK2,sK4) != k2_relat_1(sK4)
% 6.41/1.53      | k1_xboole_0 = k2_relset_1(sK3,sK2,sK4)
% 6.41/1.53      | k1_xboole_0 != k2_relat_1(sK4) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_2295]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_29,plain,
% 6.41/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.41/1.53      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 6.41/1.53      inference(cnf_transformation,[],[f92]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_2302,plain,
% 6.41/1.53      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 6.41/1.53      | k2_relset_1(sK3,sK2,sK4) = k2_relat_1(sK4) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_29]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_95,plain,
% 6.41/1.53      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_10]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_85,plain,
% 6.41/1.53      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 6.41/1.53      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 6.41/1.53      | v1_xboole_0(k1_xboole_0) ),
% 6.41/1.53      inference(instantiation,[status(thm)],[c_14]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(c_31,negated_conjecture,
% 6.41/1.53      ( k1_xboole_0 != k2_relset_1(sK3,sK2,sK4) ),
% 6.41/1.53      inference(cnf_transformation,[],[f96]) ).
% 6.41/1.53  
% 6.41/1.53  cnf(contradiction,plain,
% 6.41/1.53      ( $false ),
% 6.41/1.53      inference(minisat,
% 6.41/1.53                [status(thm)],
% 6.41/1.53                [c_23291,c_4622,c_3114,c_2535,c_2440,c_2302,c_95,c_13,
% 6.41/1.53                 c_85,c_31,c_32]) ).
% 6.41/1.53  
% 6.41/1.53  
% 6.41/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 6.41/1.53  
% 6.41/1.53  ------                               Statistics
% 6.41/1.53  
% 6.41/1.53  ------ General
% 6.41/1.53  
% 6.41/1.53  abstr_ref_over_cycles:                  0
% 6.41/1.53  abstr_ref_under_cycles:                 0
% 6.41/1.53  gc_basic_clause_elim:                   0
% 6.41/1.53  forced_gc_time:                         0
% 6.41/1.53  parsing_time:                           0.025
% 6.41/1.53  unif_index_cands_time:                  0.
% 6.41/1.53  unif_index_add_time:                    0.
% 6.41/1.53  orderings_time:                         0.
% 6.41/1.53  out_proof_time:                         0.01
% 6.41/1.53  total_time:                             0.58
% 6.41/1.53  num_of_symbols:                         52
% 6.41/1.53  num_of_terms:                           14433
% 6.41/1.53  
% 6.41/1.53  ------ Preprocessing
% 6.41/1.53  
% 6.41/1.53  num_of_splits:                          0
% 6.41/1.53  num_of_split_atoms:                     0
% 6.41/1.53  num_of_reused_defs:                     0
% 6.41/1.53  num_eq_ax_congr_red:                    30
% 6.41/1.53  num_of_sem_filtered_clauses:            1
% 6.41/1.53  num_of_subtypes:                        0
% 6.41/1.53  monotx_restored_types:                  0
% 6.41/1.53  sat_num_of_epr_types:                   0
% 6.41/1.53  sat_num_of_non_cyclic_types:            0
% 6.41/1.53  sat_guarded_non_collapsed_types:        0
% 6.41/1.53  num_pure_diseq_elim:                    0
% 6.41/1.53  simp_replaced_by:                       0
% 6.41/1.53  res_preprocessed:                       163
% 6.41/1.53  prep_upred:                             0
% 6.41/1.53  prep_unflattend:                        38
% 6.41/1.53  smt_new_axioms:                         0
% 6.41/1.53  pred_elim_cands:                        7
% 6.41/1.53  pred_elim:                              0
% 6.41/1.53  pred_elim_cl:                           0
% 6.41/1.53  pred_elim_cycles:                       4
% 6.41/1.53  merged_defs:                            16
% 6.41/1.53  merged_defs_ncl:                        0
% 6.41/1.53  bin_hyper_res:                          18
% 6.41/1.53  prep_cycles:                            4
% 6.41/1.53  pred_elim_time:                         0.008
% 6.41/1.53  splitting_time:                         0.
% 6.41/1.53  sem_filter_time:                        0.
% 6.41/1.53  monotx_time:                            0.
% 6.41/1.53  subtype_inf_time:                       0.
% 6.41/1.53  
% 6.41/1.53  ------ Problem properties
% 6.41/1.53  
% 6.41/1.53  clauses:                                34
% 6.41/1.53  conjectures:                            5
% 6.41/1.53  epr:                                    13
% 6.41/1.53  horn:                                   32
% 6.41/1.53  ground:                                 5
% 6.41/1.53  unary:                                  8
% 6.41/1.53  binary:                                 17
% 6.41/1.53  lits:                                   69
% 6.41/1.53  lits_eq:                                12
% 6.41/1.53  fd_pure:                                0
% 6.41/1.53  fd_pseudo:                              0
% 6.41/1.53  fd_cond:                                3
% 6.41/1.53  fd_pseudo_cond:                         1
% 6.41/1.53  ac_symbols:                             0
% 6.41/1.53  
% 6.41/1.53  ------ Propositional Solver
% 6.41/1.53  
% 6.41/1.53  prop_solver_calls:                      28
% 6.41/1.53  prop_fast_solver_calls:                 1353
% 6.41/1.53  smt_solver_calls:                       0
% 6.41/1.53  smt_fast_solver_calls:                  0
% 6.41/1.53  prop_num_of_clauses:                    8266
% 6.41/1.53  prop_preprocess_simplified:             18427
% 6.41/1.53  prop_fo_subsumed:                       15
% 6.41/1.53  prop_solver_time:                       0.
% 6.41/1.53  smt_solver_time:                        0.
% 6.41/1.53  smt_fast_solver_time:                   0.
% 6.41/1.53  prop_fast_solver_time:                  0.
% 6.41/1.53  prop_unsat_core_time:                   0.
% 6.41/1.53  
% 6.41/1.53  ------ QBF
% 6.41/1.53  
% 6.41/1.53  qbf_q_res:                              0
% 6.41/1.53  qbf_num_tautologies:                    0
% 6.41/1.53  qbf_prep_cycles:                        0
% 6.41/1.53  
% 6.41/1.53  ------ BMC1
% 6.41/1.53  
% 6.41/1.53  bmc1_current_bound:                     -1
% 6.41/1.53  bmc1_last_solved_bound:                 -1
% 6.41/1.53  bmc1_unsat_core_size:                   -1
% 6.41/1.53  bmc1_unsat_core_parents_size:           -1
% 6.41/1.53  bmc1_merge_next_fun:                    0
% 6.41/1.53  bmc1_unsat_core_clauses_time:           0.
% 6.41/1.53  
% 6.41/1.53  ------ Instantiation
% 6.41/1.53  
% 6.41/1.53  inst_num_of_clauses:                    2331
% 6.41/1.53  inst_num_in_passive:                    632
% 6.41/1.53  inst_num_in_active:                     1109
% 6.41/1.53  inst_num_in_unprocessed:                590
% 6.41/1.53  inst_num_of_loops:                      1350
% 6.41/1.53  inst_num_of_learning_restarts:          0
% 6.41/1.53  inst_num_moves_active_passive:          240
% 6.41/1.53  inst_lit_activity:                      0
% 6.41/1.53  inst_lit_activity_moves:                0
% 6.41/1.53  inst_num_tautologies:                   0
% 6.41/1.53  inst_num_prop_implied:                  0
% 6.41/1.53  inst_num_existing_simplified:           0
% 6.41/1.53  inst_num_eq_res_simplified:             0
% 6.41/1.53  inst_num_child_elim:                    0
% 6.41/1.53  inst_num_of_dismatching_blockings:      792
% 6.41/1.53  inst_num_of_non_proper_insts:           2713
% 6.41/1.53  inst_num_of_duplicates:                 0
% 6.41/1.53  inst_inst_num_from_inst_to_res:         0
% 6.41/1.53  inst_dismatching_checking_time:         0.
% 6.41/1.53  
% 6.41/1.53  ------ Resolution
% 6.41/1.53  
% 6.41/1.53  res_num_of_clauses:                     0
% 6.41/1.53  res_num_in_passive:                     0
% 6.41/1.53  res_num_in_active:                      0
% 6.41/1.53  res_num_of_loops:                       167
% 6.41/1.53  res_forward_subset_subsumed:            297
% 6.41/1.53  res_backward_subset_subsumed:           0
% 6.41/1.53  res_forward_subsumed:                   0
% 6.41/1.53  res_backward_subsumed:                  0
% 6.41/1.53  res_forward_subsumption_resolution:     0
% 6.41/1.53  res_backward_subsumption_resolution:    0
% 6.41/1.53  res_clause_to_clause_subsumption:       2825
% 6.41/1.53  res_orphan_elimination:                 0
% 6.41/1.53  res_tautology_del:                      227
% 6.41/1.53  res_num_eq_res_simplified:              0
% 6.41/1.53  res_num_sel_changes:                    0
% 6.41/1.53  res_moves_from_active_to_pass:          0
% 6.41/1.53  
% 6.41/1.53  ------ Superposition
% 6.41/1.53  
% 6.41/1.53  sup_time_total:                         0.
% 6.41/1.53  sup_time_generating:                    0.
% 6.41/1.53  sup_time_sim_full:                      0.
% 6.41/1.53  sup_time_sim_immed:                     0.
% 6.41/1.53  
% 6.41/1.53  sup_num_of_clauses:                     478
% 6.41/1.53  sup_num_in_active:                      244
% 6.41/1.53  sup_num_in_passive:                     234
% 6.41/1.53  sup_num_of_loops:                       269
% 6.41/1.53  sup_fw_superposition:                   567
% 6.41/1.53  sup_bw_superposition:                   196
% 6.41/1.53  sup_immediate_simplified:               199
% 6.41/1.53  sup_given_eliminated:                   1
% 6.41/1.53  comparisons_done:                       0
% 6.41/1.53  comparisons_avoided:                    6
% 6.41/1.53  
% 6.41/1.53  ------ Simplifications
% 6.41/1.53  
% 6.41/1.53  
% 6.41/1.53  sim_fw_subset_subsumed:                 26
% 6.41/1.53  sim_bw_subset_subsumed:                 4
% 6.41/1.53  sim_fw_subsumed:                        24
% 6.41/1.53  sim_bw_subsumed:                        5
% 6.41/1.53  sim_fw_subsumption_res:                 1
% 6.41/1.53  sim_bw_subsumption_res:                 0
% 6.41/1.53  sim_tautology_del:                      6
% 6.41/1.53  sim_eq_tautology_del:                   72
% 6.41/1.53  sim_eq_res_simp:                        0
% 6.41/1.53  sim_fw_demodulated:                     15
% 6.41/1.53  sim_bw_demodulated:                     23
% 6.41/1.53  sim_light_normalised:                   145
% 6.41/1.53  sim_joinable_taut:                      0
% 6.41/1.53  sim_joinable_simp:                      0
% 6.41/1.53  sim_ac_normalised:                      0
% 6.41/1.53  sim_smt_subsumption:                    0
% 6.41/1.53  
%------------------------------------------------------------------------------
