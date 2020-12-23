%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:49 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 319 expanded)
%              Number of clauses        :   76 ( 129 expanded)
%              Number of leaves         :   26 (  73 expanded)
%              Depth                    :   20
%              Number of atoms          :  440 (1137 expanded)
%              Number of equality atoms :  139 ( 250 expanded)
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
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
              | ~ m1_subset_1(X3,X1) )
          & k1_xboole_0 != k2_relset_1(X1,X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(X1,X0,sK6))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k2_relset_1(X1,X0,sK6)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
                ( ~ r2_hidden(X3,k1_relset_1(sK5,X0,X2))
                | ~ m1_subset_1(X3,sK5) )
            & k1_xboole_0 != k2_relset_1(sK5,X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) )
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
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
                  ( ~ r2_hidden(X3,k1_relset_1(X1,sK4,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,sK4,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK4))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK5,sK4,sK6))
        | ~ m1_subset_1(X3,sK5) )
    & k1_xboole_0 != k2_relset_1(sK5,sK4,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f35,f52,f51,f50])).

fof(f84,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f5])).

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

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f63])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK5,sK4,sK6))
      | ~ m1_subset_1(X3,sK5) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1778,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1785,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2585,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_1785])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_17,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_248,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_249,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_248])).

cnf(c_305,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_19,c_249])).

cnf(c_1775,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_15166,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2585,c_1775])).

cnf(c_2315,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_4323,plain,
    ( ~ r1_tarski(sK6,k2_zfmisc_1(sK5,sK4))
    | ~ v1_relat_1(k2_zfmisc_1(sK5,sK4))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2315])).

cnf(c_4324,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK5,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4323])).

cnf(c_22,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4398,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_4399,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4398])).

cnf(c_15195,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15166,c_2585,c_4324,c_4399])).

cnf(c_23,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1783,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_15199,plain,
    ( k10_relat_1(sK6,k2_relat_1(sK6)) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_15195,c_1783])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1801,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_25,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_21,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_25,c_21])).

cnf(c_1774,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_2195,plain,
    ( r1_tarski(k1_relat_1(sK6),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_1774])).

cnf(c_1786,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1787,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3304,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1786,c_1787])).

cnf(c_441,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X2,X3)
    | v1_xboole_0(X3)
    | X0 != X2
    | k1_zfmisc_1(X1) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_249])).

cnf(c_442,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_14,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_452,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_442,c_14])).

cnf(c_455,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_8887,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3304,c_455])).

cnf(c_8888,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8887])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1792,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8895,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(k1_zfmisc_1(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8888,c_1792])).

cnf(c_13,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8899,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8895,c_13])).

cnf(c_8983,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_8899])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1868,plain,
    ( m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1869,plain,
    ( m1_subset_1(X0,sK5) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1868])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1781,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2987,plain,
    ( k1_relset_1(sK5,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1778,c_1781])).

cnf(c_28,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,k1_relset_1(sK5,sK4,sK6)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1779,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,k1_relset_1(sK5,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3078,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2987,c_1779])).

cnf(c_9266,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8983,c_1869,c_2585,c_3078,c_4324,c_4399])).

cnf(c_9272,plain,
    ( v1_xboole_0(k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_9266])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1799,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1796,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2919,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1799,c_1796])).

cnf(c_9287,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9272,c_2919])).

cnf(c_15200,plain,
    ( k10_relat_1(sK6,k2_relat_1(sK6)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_15199,c_9287])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1782,plain,
    ( k10_relat_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_17406,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_15200,c_1782])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_6819,plain,
    ( r1_tarski(k2_relat_1(sK6),k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6820,plain,
    ( r1_tarski(k2_relat_1(sK6),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6819])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1780,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2770,plain,
    ( k2_relset_1(sK5,sK4,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1778,c_1780])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2991,plain,
    ( k2_relat_1(sK6) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2770,c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17406,c_6820,c_4399,c_4324,c_2991,c_2585])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.77/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
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
% 3.77/0.99  --clausifier_options                    ""
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
% 3.77/1.00  --trig_cnt_out                          false
% 3.77/1.00  --trig_cnt_out_tolerance                1.
% 3.77/1.00  --trig_cnt_out_sk_spl                   false
% 3.77/1.00  --abstr_cl_out                          false
% 3.77/1.00  
% 3.77/1.00  ------ Global Options
% 3.77/1.00  
% 3.77/1.00  --schedule                              default
% 3.77/1.00  --add_important_lit                     false
% 3.77/1.00  --prop_solver_per_cl                    1000
% 3.77/1.00  --min_unsat_core                        false
% 3.77/1.00  --soft_assumptions                      false
% 3.77/1.00  --soft_lemma_size                       3
% 3.77/1.00  --prop_impl_unit_size                   0
% 3.77/1.00  --prop_impl_unit                        []
% 3.77/1.00  --share_sel_clauses                     true
% 3.77/1.00  --reset_solvers                         false
% 3.77/1.00  --bc_imp_inh                            [conj_cone]
% 3.77/1.00  --conj_cone_tolerance                   3.
% 3.77/1.00  --extra_neg_conj                        none
% 3.77/1.00  --large_theory_mode                     true
% 3.77/1.00  --prolific_symb_bound                   200
% 3.77/1.00  --lt_threshold                          2000
% 3.77/1.00  --clause_weak_htbl                      true
% 3.77/1.00  --gc_record_bc_elim                     false
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing Options
% 3.77/1.00  
% 3.77/1.00  --preprocessing_flag                    true
% 3.77/1.00  --time_out_prep_mult                    0.1
% 3.77/1.00  --splitting_mode                        input
% 3.77/1.00  --splitting_grd                         true
% 3.77/1.00  --splitting_cvd                         false
% 3.77/1.00  --splitting_cvd_svl                     false
% 3.77/1.00  --splitting_nvd                         32
% 3.77/1.00  --sub_typing                            true
% 3.77/1.00  --prep_gs_sim                           true
% 3.77/1.00  --prep_unflatten                        true
% 3.77/1.00  --prep_res_sim                          true
% 3.77/1.00  --prep_upred                            true
% 3.77/1.00  --prep_sem_filter                       exhaustive
% 3.77/1.00  --prep_sem_filter_out                   false
% 3.77/1.00  --pred_elim                             true
% 3.77/1.00  --res_sim_input                         true
% 3.77/1.00  --eq_ax_congr_red                       true
% 3.77/1.00  --pure_diseq_elim                       true
% 3.77/1.00  --brand_transform                       false
% 3.77/1.00  --non_eq_to_eq                          false
% 3.77/1.00  --prep_def_merge                        true
% 3.77/1.00  --prep_def_merge_prop_impl              false
% 3.77/1.00  --prep_def_merge_mbd                    true
% 3.77/1.00  --prep_def_merge_tr_red                 false
% 3.77/1.00  --prep_def_merge_tr_cl                  false
% 3.77/1.00  --smt_preprocessing                     true
% 3.77/1.00  --smt_ac_axioms                         fast
% 3.77/1.00  --preprocessed_out                      false
% 3.77/1.00  --preprocessed_stats                    false
% 3.77/1.00  
% 3.77/1.00  ------ Abstraction refinement Options
% 3.77/1.00  
% 3.77/1.00  --abstr_ref                             []
% 3.77/1.00  --abstr_ref_prep                        false
% 3.77/1.00  --abstr_ref_until_sat                   false
% 3.77/1.00  --abstr_ref_sig_restrict                funpre
% 3.77/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/1.00  --abstr_ref_under                       []
% 3.77/1.00  
% 3.77/1.00  ------ SAT Options
% 3.77/1.00  
% 3.77/1.00  --sat_mode                              false
% 3.77/1.00  --sat_fm_restart_options                ""
% 3.77/1.00  --sat_gr_def                            false
% 3.77/1.00  --sat_epr_types                         true
% 3.77/1.00  --sat_non_cyclic_types                  false
% 3.77/1.00  --sat_finite_models                     false
% 3.77/1.00  --sat_fm_lemmas                         false
% 3.77/1.00  --sat_fm_prep                           false
% 3.77/1.00  --sat_fm_uc_incr                        true
% 3.77/1.00  --sat_out_model                         small
% 3.77/1.00  --sat_out_clauses                       false
% 3.77/1.00  
% 3.77/1.00  ------ QBF Options
% 3.77/1.00  
% 3.77/1.00  --qbf_mode                              false
% 3.77/1.00  --qbf_elim_univ                         false
% 3.77/1.00  --qbf_dom_inst                          none
% 3.77/1.00  --qbf_dom_pre_inst                      false
% 3.77/1.00  --qbf_sk_in                             false
% 3.77/1.00  --qbf_pred_elim                         true
% 3.77/1.00  --qbf_split                             512
% 3.77/1.00  
% 3.77/1.00  ------ BMC1 Options
% 3.77/1.00  
% 3.77/1.00  --bmc1_incremental                      false
% 3.77/1.00  --bmc1_axioms                           reachable_all
% 3.77/1.00  --bmc1_min_bound                        0
% 3.77/1.00  --bmc1_max_bound                        -1
% 3.77/1.00  --bmc1_max_bound_default                -1
% 3.77/1.00  --bmc1_symbol_reachability              true
% 3.77/1.00  --bmc1_property_lemmas                  false
% 3.77/1.00  --bmc1_k_induction                      false
% 3.77/1.00  --bmc1_non_equiv_states                 false
% 3.77/1.00  --bmc1_deadlock                         false
% 3.77/1.00  --bmc1_ucm                              false
% 3.77/1.00  --bmc1_add_unsat_core                   none
% 3.77/1.00  --bmc1_unsat_core_children              false
% 3.77/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/1.00  --bmc1_out_stat                         full
% 3.77/1.00  --bmc1_ground_init                      false
% 3.77/1.00  --bmc1_pre_inst_next_state              false
% 3.77/1.00  --bmc1_pre_inst_state                   false
% 3.77/1.00  --bmc1_pre_inst_reach_state             false
% 3.77/1.00  --bmc1_out_unsat_core                   false
% 3.77/1.00  --bmc1_aig_witness_out                  false
% 3.77/1.00  --bmc1_verbose                          false
% 3.77/1.00  --bmc1_dump_clauses_tptp                false
% 3.77/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.77/1.00  --bmc1_dump_file                        -
% 3.77/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.77/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.77/1.00  --bmc1_ucm_extend_mode                  1
% 3.77/1.00  --bmc1_ucm_init_mode                    2
% 3.77/1.00  --bmc1_ucm_cone_mode                    none
% 3.77/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.77/1.00  --bmc1_ucm_relax_model                  4
% 3.77/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.77/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/1.00  --bmc1_ucm_layered_model                none
% 3.77/1.00  --bmc1_ucm_max_lemma_size               10
% 3.77/1.00  
% 3.77/1.00  ------ AIG Options
% 3.77/1.00  
% 3.77/1.00  --aig_mode                              false
% 3.77/1.00  
% 3.77/1.00  ------ Instantiation Options
% 3.77/1.00  
% 3.77/1.00  --instantiation_flag                    true
% 3.77/1.00  --inst_sos_flag                         true
% 3.77/1.00  --inst_sos_phase                        true
% 3.77/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/1.00  --inst_lit_sel_side                     num_symb
% 3.77/1.00  --inst_solver_per_active                1400
% 3.77/1.00  --inst_solver_calls_frac                1.
% 3.77/1.00  --inst_passive_queue_type               priority_queues
% 3.77/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/1.00  --inst_passive_queues_freq              [25;2]
% 3.77/1.00  --inst_dismatching                      true
% 3.77/1.00  --inst_eager_unprocessed_to_passive     true
% 3.77/1.00  --inst_prop_sim_given                   true
% 3.77/1.00  --inst_prop_sim_new                     false
% 3.77/1.00  --inst_subs_new                         false
% 3.77/1.00  --inst_eq_res_simp                      false
% 3.77/1.00  --inst_subs_given                       false
% 3.77/1.00  --inst_orphan_elimination               true
% 3.77/1.00  --inst_learning_loop_flag               true
% 3.77/1.00  --inst_learning_start                   3000
% 3.77/1.00  --inst_learning_factor                  2
% 3.77/1.00  --inst_start_prop_sim_after_learn       3
% 3.77/1.00  --inst_sel_renew                        solver
% 3.77/1.00  --inst_lit_activity_flag                true
% 3.77/1.00  --inst_restr_to_given                   false
% 3.77/1.00  --inst_activity_threshold               500
% 3.77/1.00  --inst_out_proof                        true
% 3.77/1.00  
% 3.77/1.00  ------ Resolution Options
% 3.77/1.00  
% 3.77/1.00  --resolution_flag                       true
% 3.77/1.00  --res_lit_sel                           adaptive
% 3.77/1.00  --res_lit_sel_side                      none
% 3.77/1.00  --res_ordering                          kbo
% 3.77/1.00  --res_to_prop_solver                    active
% 3.77/1.00  --res_prop_simpl_new                    false
% 3.77/1.00  --res_prop_simpl_given                  true
% 3.77/1.00  --res_passive_queue_type                priority_queues
% 3.77/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/1.00  --res_passive_queues_freq               [15;5]
% 3.77/1.00  --res_forward_subs                      full
% 3.77/1.00  --res_backward_subs                     full
% 3.77/1.00  --res_forward_subs_resolution           true
% 3.77/1.00  --res_backward_subs_resolution          true
% 3.77/1.00  --res_orphan_elimination                true
% 3.77/1.00  --res_time_limit                        2.
% 3.77/1.00  --res_out_proof                         true
% 3.77/1.00  
% 3.77/1.00  ------ Superposition Options
% 3.77/1.00  
% 3.77/1.00  --superposition_flag                    true
% 3.77/1.00  --sup_passive_queue_type                priority_queues
% 3.77/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.77/1.00  --demod_completeness_check              fast
% 3.77/1.00  --demod_use_ground                      true
% 3.77/1.00  --sup_to_prop_solver                    passive
% 3.77/1.00  --sup_prop_simpl_new                    true
% 3.77/1.00  --sup_prop_simpl_given                  true
% 3.77/1.00  --sup_fun_splitting                     true
% 3.77/1.00  --sup_smt_interval                      50000
% 3.77/1.00  
% 3.77/1.00  ------ Superposition Simplification Setup
% 3.77/1.00  
% 3.77/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.77/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.77/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.77/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.77/1.00  --sup_immed_triv                        [TrivRules]
% 3.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/1.00  --sup_immed_bw_main                     []
% 3.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/1.00  --sup_input_bw                          []
% 3.77/1.00  
% 3.77/1.00  ------ Combination Options
% 3.77/1.00  
% 3.77/1.00  --comb_res_mult                         3
% 3.77/1.00  --comb_sup_mult                         2
% 3.77/1.00  --comb_inst_mult                        10
% 3.77/1.00  
% 3.77/1.00  ------ Debug Options
% 3.77/1.00  
% 3.77/1.00  --dbg_backtrace                         false
% 3.77/1.00  --dbg_dump_prop_clauses                 false
% 3.77/1.00  --dbg_dump_prop_clauses_file            -
% 3.77/1.00  --dbg_out_stat                          false
% 3.77/1.00  ------ Parsing...
% 3.77/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/1.00  ------ Proving...
% 3.77/1.00  ------ Problem Properties 
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  clauses                                 30
% 3.77/1.00  conjectures                             5
% 3.77/1.00  EPR                                     10
% 3.77/1.00  Horn                                    26
% 3.77/1.00  unary                                   9
% 3.77/1.00  binary                                  11
% 3.77/1.00  lits                                    63
% 3.77/1.00  lits eq                                 12
% 3.77/1.00  fd_pure                                 0
% 3.77/1.00  fd_pseudo                               0
% 3.77/1.00  fd_cond                                 1
% 3.77/1.00  fd_pseudo_cond                          5
% 3.77/1.00  AC symbols                              0
% 3.77/1.00  
% 3.77/1.00  ------ Schedule dynamic 5 is on 
% 3.77/1.00  
% 3.77/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  ------ 
% 3.77/1.00  Current options:
% 3.77/1.00  ------ 
% 3.77/1.00  
% 3.77/1.00  ------ Input Options
% 3.77/1.00  
% 3.77/1.00  --out_options                           all
% 3.77/1.00  --tptp_safe_out                         true
% 3.77/1.00  --problem_path                          ""
% 3.77/1.00  --include_path                          ""
% 3.77/1.00  --clausifier                            res/vclausify_rel
% 3.77/1.00  --clausifier_options                    ""
% 3.77/1.00  --stdin                                 false
% 3.77/1.00  --stats_out                             all
% 3.77/1.00  
% 3.77/1.00  ------ General Options
% 3.77/1.00  
% 3.77/1.00  --fof                                   false
% 3.77/1.00  --time_out_real                         305.
% 3.77/1.00  --time_out_virtual                      -1.
% 3.77/1.00  --symbol_type_check                     false
% 3.77/1.00  --clausify_out                          false
% 3.77/1.00  --sig_cnt_out                           false
% 3.77/1.00  --trig_cnt_out                          false
% 3.77/1.00  --trig_cnt_out_tolerance                1.
% 3.77/1.00  --trig_cnt_out_sk_spl                   false
% 3.77/1.00  --abstr_cl_out                          false
% 3.77/1.00  
% 3.77/1.00  ------ Global Options
% 3.77/1.00  
% 3.77/1.00  --schedule                              default
% 3.77/1.00  --add_important_lit                     false
% 3.77/1.00  --prop_solver_per_cl                    1000
% 3.77/1.00  --min_unsat_core                        false
% 3.77/1.00  --soft_assumptions                      false
% 3.77/1.00  --soft_lemma_size                       3
% 3.77/1.00  --prop_impl_unit_size                   0
% 3.77/1.00  --prop_impl_unit                        []
% 3.77/1.00  --share_sel_clauses                     true
% 3.77/1.00  --reset_solvers                         false
% 3.77/1.00  --bc_imp_inh                            [conj_cone]
% 3.77/1.00  --conj_cone_tolerance                   3.
% 3.77/1.00  --extra_neg_conj                        none
% 3.77/1.00  --large_theory_mode                     true
% 3.77/1.00  --prolific_symb_bound                   200
% 3.77/1.00  --lt_threshold                          2000
% 3.77/1.00  --clause_weak_htbl                      true
% 3.77/1.00  --gc_record_bc_elim                     false
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing Options
% 3.77/1.00  
% 3.77/1.00  --preprocessing_flag                    true
% 3.77/1.00  --time_out_prep_mult                    0.1
% 3.77/1.00  --splitting_mode                        input
% 3.77/1.00  --splitting_grd                         true
% 3.77/1.00  --splitting_cvd                         false
% 3.77/1.00  --splitting_cvd_svl                     false
% 3.77/1.00  --splitting_nvd                         32
% 3.77/1.00  --sub_typing                            true
% 3.77/1.00  --prep_gs_sim                           true
% 3.77/1.00  --prep_unflatten                        true
% 3.77/1.00  --prep_res_sim                          true
% 3.77/1.00  --prep_upred                            true
% 3.77/1.00  --prep_sem_filter                       exhaustive
% 3.77/1.00  --prep_sem_filter_out                   false
% 3.77/1.00  --pred_elim                             true
% 3.77/1.00  --res_sim_input                         true
% 3.77/1.00  --eq_ax_congr_red                       true
% 3.77/1.00  --pure_diseq_elim                       true
% 3.77/1.00  --brand_transform                       false
% 3.77/1.00  --non_eq_to_eq                          false
% 3.77/1.00  --prep_def_merge                        true
% 3.77/1.00  --prep_def_merge_prop_impl              false
% 3.77/1.00  --prep_def_merge_mbd                    true
% 3.77/1.00  --prep_def_merge_tr_red                 false
% 3.77/1.00  --prep_def_merge_tr_cl                  false
% 3.77/1.00  --smt_preprocessing                     true
% 3.77/1.00  --smt_ac_axioms                         fast
% 3.77/1.00  --preprocessed_out                      false
% 3.77/1.00  --preprocessed_stats                    false
% 3.77/1.00  
% 3.77/1.00  ------ Abstraction refinement Options
% 3.77/1.00  
% 3.77/1.00  --abstr_ref                             []
% 3.77/1.00  --abstr_ref_prep                        false
% 3.77/1.00  --abstr_ref_until_sat                   false
% 3.77/1.00  --abstr_ref_sig_restrict                funpre
% 3.77/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/1.00  --abstr_ref_under                       []
% 3.77/1.00  
% 3.77/1.00  ------ SAT Options
% 3.77/1.00  
% 3.77/1.00  --sat_mode                              false
% 3.77/1.00  --sat_fm_restart_options                ""
% 3.77/1.00  --sat_gr_def                            false
% 3.77/1.00  --sat_epr_types                         true
% 3.77/1.00  --sat_non_cyclic_types                  false
% 3.77/1.00  --sat_finite_models                     false
% 3.77/1.00  --sat_fm_lemmas                         false
% 3.77/1.00  --sat_fm_prep                           false
% 3.77/1.00  --sat_fm_uc_incr                        true
% 3.77/1.00  --sat_out_model                         small
% 3.77/1.00  --sat_out_clauses                       false
% 3.77/1.00  
% 3.77/1.00  ------ QBF Options
% 3.77/1.00  
% 3.77/1.00  --qbf_mode                              false
% 3.77/1.00  --qbf_elim_univ                         false
% 3.77/1.00  --qbf_dom_inst                          none
% 3.77/1.00  --qbf_dom_pre_inst                      false
% 3.77/1.00  --qbf_sk_in                             false
% 3.77/1.00  --qbf_pred_elim                         true
% 3.77/1.00  --qbf_split                             512
% 3.77/1.00  
% 3.77/1.00  ------ BMC1 Options
% 3.77/1.00  
% 3.77/1.00  --bmc1_incremental                      false
% 3.77/1.00  --bmc1_axioms                           reachable_all
% 3.77/1.00  --bmc1_min_bound                        0
% 3.77/1.00  --bmc1_max_bound                        -1
% 3.77/1.00  --bmc1_max_bound_default                -1
% 3.77/1.00  --bmc1_symbol_reachability              true
% 3.77/1.00  --bmc1_property_lemmas                  false
% 3.77/1.00  --bmc1_k_induction                      false
% 3.77/1.00  --bmc1_non_equiv_states                 false
% 3.77/1.00  --bmc1_deadlock                         false
% 3.77/1.00  --bmc1_ucm                              false
% 3.77/1.00  --bmc1_add_unsat_core                   none
% 3.77/1.00  --bmc1_unsat_core_children              false
% 3.77/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/1.00  --bmc1_out_stat                         full
% 3.77/1.00  --bmc1_ground_init                      false
% 3.77/1.00  --bmc1_pre_inst_next_state              false
% 3.77/1.00  --bmc1_pre_inst_state                   false
% 3.77/1.00  --bmc1_pre_inst_reach_state             false
% 3.77/1.00  --bmc1_out_unsat_core                   false
% 3.77/1.00  --bmc1_aig_witness_out                  false
% 3.77/1.00  --bmc1_verbose                          false
% 3.77/1.00  --bmc1_dump_clauses_tptp                false
% 3.77/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.77/1.00  --bmc1_dump_file                        -
% 3.77/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.77/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.77/1.00  --bmc1_ucm_extend_mode                  1
% 3.77/1.00  --bmc1_ucm_init_mode                    2
% 3.77/1.00  --bmc1_ucm_cone_mode                    none
% 3.77/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.77/1.00  --bmc1_ucm_relax_model                  4
% 3.77/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.77/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/1.00  --bmc1_ucm_layered_model                none
% 3.77/1.00  --bmc1_ucm_max_lemma_size               10
% 3.77/1.00  
% 3.77/1.00  ------ AIG Options
% 3.77/1.00  
% 3.77/1.00  --aig_mode                              false
% 3.77/1.00  
% 3.77/1.00  ------ Instantiation Options
% 3.77/1.00  
% 3.77/1.00  --instantiation_flag                    true
% 3.77/1.00  --inst_sos_flag                         true
% 3.77/1.00  --inst_sos_phase                        true
% 3.77/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/1.00  --inst_lit_sel_side                     none
% 3.77/1.00  --inst_solver_per_active                1400
% 3.77/1.00  --inst_solver_calls_frac                1.
% 3.77/1.00  --inst_passive_queue_type               priority_queues
% 3.77/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/1.00  --inst_passive_queues_freq              [25;2]
% 3.77/1.00  --inst_dismatching                      true
% 3.77/1.00  --inst_eager_unprocessed_to_passive     true
% 3.77/1.00  --inst_prop_sim_given                   true
% 3.77/1.00  --inst_prop_sim_new                     false
% 3.77/1.00  --inst_subs_new                         false
% 3.77/1.00  --inst_eq_res_simp                      false
% 3.77/1.00  --inst_subs_given                       false
% 3.77/1.00  --inst_orphan_elimination               true
% 3.77/1.00  --inst_learning_loop_flag               true
% 3.77/1.00  --inst_learning_start                   3000
% 3.77/1.00  --inst_learning_factor                  2
% 3.77/1.00  --inst_start_prop_sim_after_learn       3
% 3.77/1.00  --inst_sel_renew                        solver
% 3.77/1.00  --inst_lit_activity_flag                true
% 3.77/1.00  --inst_restr_to_given                   false
% 3.77/1.00  --inst_activity_threshold               500
% 3.77/1.00  --inst_out_proof                        true
% 3.77/1.00  
% 3.77/1.00  ------ Resolution Options
% 3.77/1.00  
% 3.77/1.00  --resolution_flag                       false
% 3.77/1.00  --res_lit_sel                           adaptive
% 3.77/1.00  --res_lit_sel_side                      none
% 3.77/1.00  --res_ordering                          kbo
% 3.77/1.00  --res_to_prop_solver                    active
% 3.77/1.00  --res_prop_simpl_new                    false
% 3.77/1.00  --res_prop_simpl_given                  true
% 3.77/1.00  --res_passive_queue_type                priority_queues
% 3.77/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/1.00  --res_passive_queues_freq               [15;5]
% 3.77/1.00  --res_forward_subs                      full
% 3.77/1.00  --res_backward_subs                     full
% 3.77/1.00  --res_forward_subs_resolution           true
% 3.77/1.00  --res_backward_subs_resolution          true
% 3.77/1.00  --res_orphan_elimination                true
% 3.77/1.00  --res_time_limit                        2.
% 3.77/1.00  --res_out_proof                         true
% 3.77/1.00  
% 3.77/1.00  ------ Superposition Options
% 3.77/1.00  
% 3.77/1.00  --superposition_flag                    true
% 3.77/1.00  --sup_passive_queue_type                priority_queues
% 3.77/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.77/1.00  --demod_completeness_check              fast
% 3.77/1.00  --demod_use_ground                      true
% 3.77/1.00  --sup_to_prop_solver                    passive
% 3.77/1.00  --sup_prop_simpl_new                    true
% 3.77/1.00  --sup_prop_simpl_given                  true
% 3.77/1.00  --sup_fun_splitting                     true
% 3.77/1.00  --sup_smt_interval                      50000
% 3.77/1.00  
% 3.77/1.00  ------ Superposition Simplification Setup
% 3.77/1.00  
% 3.77/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.77/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.77/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.77/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.77/1.00  --sup_immed_triv                        [TrivRules]
% 3.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/1.00  --sup_immed_bw_main                     []
% 3.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/1.00  --sup_input_bw                          []
% 3.77/1.00  
% 3.77/1.00  ------ Combination Options
% 3.77/1.00  
% 3.77/1.00  --comb_res_mult                         3
% 3.77/1.00  --comb_sup_mult                         2
% 3.77/1.00  --comb_inst_mult                        10
% 3.77/1.00  
% 3.77/1.00  ------ Debug Options
% 3.77/1.00  
% 3.77/1.00  --dbg_backtrace                         false
% 3.77/1.00  --dbg_dump_prop_clauses                 false
% 3.77/1.00  --dbg_dump_prop_clauses_file            -
% 3.77/1.00  --dbg_out_stat                          false
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  ------ Proving...
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  % SZS status Theorem for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  fof(f19,conjecture,(
% 3.77/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f20,negated_conjecture,(
% 3.77/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 3.77/1.00    inference(negated_conjecture,[],[f19])).
% 3.77/1.00  
% 3.77/1.00  fof(f34,plain,(
% 3.77/1.00    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f20])).
% 3.77/1.00  
% 3.77/1.00  fof(f35,plain,(
% 3.77/1.00    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.77/1.00    inference(flattening,[],[f34])).
% 3.77/1.00  
% 3.77/1.00  fof(f52,plain,(
% 3.77/1.00    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,sK6)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))) )),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f51,plain,(
% 3.77/1.00    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK5,X0,X2)) | ~m1_subset_1(X3,sK5)) & k1_xboole_0 != k2_relset_1(sK5,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))) & ~v1_xboole_0(sK5))) )),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f50,plain,(
% 3.77/1.00    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK4,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK4,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK4))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f53,plain,(
% 3.77/1.00    ((! [X3] : (~r2_hidden(X3,k1_relset_1(sK5,sK4,sK6)) | ~m1_subset_1(X3,sK5)) & k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)),
% 3.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f35,f52,f51,f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f84,plain,(
% 3.77/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 3.77/1.00    inference(cnf_transformation,[],[f53])).
% 3.77/1.00  
% 3.77/1.00  fof(f10,axiom,(
% 3.77/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f48,plain,(
% 3.77/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.77/1.00    inference(nnf_transformation,[],[f10])).
% 3.77/1.00  
% 3.77/1.00  fof(f71,plain,(
% 3.77/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f48])).
% 3.77/1.00  
% 3.77/1.00  fof(f11,axiom,(
% 3.77/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f26,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f11])).
% 3.77/1.00  
% 3.77/1.00  fof(f73,plain,(
% 3.77/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f26])).
% 3.77/1.00  
% 3.77/1.00  fof(f72,plain,(
% 3.77/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f48])).
% 3.77/1.00  
% 3.77/1.00  fof(f13,axiom,(
% 3.77/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f76,plain,(
% 3.77/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f13])).
% 3.77/1.00  
% 3.77/1.00  fof(f14,axiom,(
% 3.77/1.00    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f28,plain,(
% 3.77/1.00    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f14])).
% 3.77/1.00  
% 3.77/1.00  fof(f77,plain,(
% 3.77/1.00    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f28])).
% 3.77/1.00  
% 3.77/1.00  fof(f1,axiom,(
% 3.77/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f36,plain,(
% 3.77/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.77/1.00    inference(nnf_transformation,[],[f1])).
% 3.77/1.00  
% 3.77/1.00  fof(f37,plain,(
% 3.77/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.77/1.00    inference(rectify,[],[f36])).
% 3.77/1.00  
% 3.77/1.00  fof(f38,plain,(
% 3.77/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f39,plain,(
% 3.77/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.77/1.00  
% 3.77/1.00  fof(f55,plain,(
% 3.77/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f39])).
% 3.77/1.00  
% 3.77/1.00  fof(f16,axiom,(
% 3.77/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f21,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.77/1.00    inference(pure_predicate_removal,[],[f16])).
% 3.77/1.00  
% 3.77/1.00  fof(f31,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.00    inference(ennf_transformation,[],[f21])).
% 3.77/1.00  
% 3.77/1.00  fof(f79,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f31])).
% 3.77/1.00  
% 3.77/1.00  fof(f12,axiom,(
% 3.77/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f27,plain,(
% 3.77/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.77/1.00    inference(ennf_transformation,[],[f12])).
% 3.77/1.00  
% 3.77/1.00  fof(f49,plain,(
% 3.77/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.77/1.00    inference(nnf_transformation,[],[f27])).
% 3.77/1.00  
% 3.77/1.00  fof(f74,plain,(
% 3.77/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f49])).
% 3.77/1.00  
% 3.77/1.00  fof(f9,axiom,(
% 3.77/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f24,plain,(
% 3.77/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.77/1.00    inference(ennf_transformation,[],[f9])).
% 3.77/1.00  
% 3.77/1.00  fof(f25,plain,(
% 3.77/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.77/1.00    inference(flattening,[],[f24])).
% 3.77/1.00  
% 3.77/1.00  fof(f70,plain,(
% 3.77/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f25])).
% 3.77/1.00  
% 3.77/1.00  fof(f7,axiom,(
% 3.77/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f68,plain,(
% 3.77/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f7])).
% 3.77/1.00  
% 3.77/1.00  fof(f5,axiom,(
% 3.77/1.00    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f42,plain,(
% 3.77/1.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.77/1.00    inference(nnf_transformation,[],[f5])).
% 3.77/1.00  
% 3.77/1.00  fof(f43,plain,(
% 3.77/1.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.77/1.00    inference(rectify,[],[f42])).
% 3.77/1.00  
% 3.77/1.00  fof(f46,plain,(
% 3.77/1.00    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f45,plain,(
% 3.77/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f44,plain,(
% 3.77/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f47,plain,(
% 3.77/1.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f46,f45,f44])).
% 3.77/1.00  
% 3.77/1.00  fof(f63,plain,(
% 3.77/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 3.77/1.00    inference(cnf_transformation,[],[f47])).
% 3.77/1.00  
% 3.77/1.00  fof(f89,plain,(
% 3.77/1.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 3.77/1.00    inference(equality_resolution,[],[f63])).
% 3.77/1.00  
% 3.77/1.00  fof(f6,axiom,(
% 3.77/1.00    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f67,plain,(
% 3.77/1.00    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.77/1.00    inference(cnf_transformation,[],[f6])).
% 3.77/1.00  
% 3.77/1.00  fof(f8,axiom,(
% 3.77/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f23,plain,(
% 3.77/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.77/1.00    inference(ennf_transformation,[],[f8])).
% 3.77/1.00  
% 3.77/1.00  fof(f69,plain,(
% 3.77/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f23])).
% 3.77/1.00  
% 3.77/1.00  fof(f17,axiom,(
% 3.77/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f32,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.00    inference(ennf_transformation,[],[f17])).
% 3.77/1.00  
% 3.77/1.00  fof(f80,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f32])).
% 3.77/1.00  
% 3.77/1.00  fof(f86,plain,(
% 3.77/1.00    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK5,sK4,sK6)) | ~m1_subset_1(X3,sK5)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f53])).
% 3.77/1.00  
% 3.77/1.00  fof(f2,axiom,(
% 3.77/1.00    v1_xboole_0(k1_xboole_0)),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f56,plain,(
% 3.77/1.00    v1_xboole_0(k1_xboole_0)),
% 3.77/1.00    inference(cnf_transformation,[],[f2])).
% 3.77/1.00  
% 3.77/1.00  fof(f4,axiom,(
% 3.77/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f22,plain,(
% 3.77/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f4])).
% 3.77/1.00  
% 3.77/1.00  fof(f60,plain,(
% 3.77/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f22])).
% 3.77/1.00  
% 3.77/1.00  fof(f15,axiom,(
% 3.77/1.00    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f29,plain,(
% 3.77/1.00    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 3.77/1.00    inference(ennf_transformation,[],[f15])).
% 3.77/1.00  
% 3.77/1.00  fof(f30,plain,(
% 3.77/1.00    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 3.77/1.00    inference(flattening,[],[f29])).
% 3.77/1.00  
% 3.77/1.00  fof(f78,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f30])).
% 3.77/1.00  
% 3.77/1.00  fof(f3,axiom,(
% 3.77/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f40,plain,(
% 3.77/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/1.00    inference(nnf_transformation,[],[f3])).
% 3.77/1.00  
% 3.77/1.00  fof(f41,plain,(
% 3.77/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/1.00    inference(flattening,[],[f40])).
% 3.77/1.00  
% 3.77/1.00  fof(f57,plain,(
% 3.77/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.77/1.00    inference(cnf_transformation,[],[f41])).
% 3.77/1.00  
% 3.77/1.00  fof(f88,plain,(
% 3.77/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.77/1.00    inference(equality_resolution,[],[f57])).
% 3.77/1.00  
% 3.77/1.00  fof(f18,axiom,(
% 3.77/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f33,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.00    inference(ennf_transformation,[],[f18])).
% 3.77/1.00  
% 3.77/1.00  fof(f81,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f33])).
% 3.77/1.00  
% 3.77/1.00  fof(f85,plain,(
% 3.77/1.00    k1_xboole_0 != k2_relset_1(sK5,sK4,sK6)),
% 3.77/1.00    inference(cnf_transformation,[],[f53])).
% 3.77/1.00  
% 3.77/1.00  cnf(c_30,negated_conjecture,
% 3.77/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
% 3.77/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1778,plain,
% 3.77/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_18,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1785,plain,
% 3.77/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.77/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2585,plain,
% 3.77/1.00      ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1778,c_1785]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_19,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.77/1.00      | ~ v1_relat_1(X1)
% 3.77/1.00      | v1_relat_1(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_17,plain,
% 3.77/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_248,plain,
% 3.77/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.77/1.00      inference(prop_impl,[status(thm)],[c_17]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_249,plain,
% 3.77/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_248]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_305,plain,
% 3.77/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.77/1.00      inference(bin_hyper_res,[status(thm)],[c_19,c_249]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1775,plain,
% 3.77/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.77/1.00      | v1_relat_1(X1) != iProver_top
% 3.77/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_15166,plain,
% 3.77/1.00      ( v1_relat_1(k2_zfmisc_1(sK5,sK4)) != iProver_top
% 3.77/1.00      | v1_relat_1(sK6) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2585,c_1775]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2315,plain,
% 3.77/1.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.77/1.00      | v1_relat_1(X0)
% 3.77/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_305]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4323,plain,
% 3.77/1.00      ( ~ r1_tarski(sK6,k2_zfmisc_1(sK5,sK4))
% 3.77/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK5,sK4))
% 3.77/1.00      | v1_relat_1(sK6) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_2315]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4324,plain,
% 3.77/1.00      ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) != iProver_top
% 3.77/1.00      | v1_relat_1(k2_zfmisc_1(sK5,sK4)) != iProver_top
% 3.77/1.00      | v1_relat_1(sK6) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_4323]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_22,plain,
% 3.77/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4398,plain,
% 3.77/1.00      ( v1_relat_1(k2_zfmisc_1(sK5,sK4)) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4399,plain,
% 3.77/1.00      ( v1_relat_1(k2_zfmisc_1(sK5,sK4)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_4398]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_15195,plain,
% 3.77/1.00      ( v1_relat_1(sK6) = iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_15166,c_2585,c_4324,c_4399]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_23,plain,
% 3.77/1.00      ( ~ v1_relat_1(X0)
% 3.77/1.00      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1783,plain,
% 3.77/1.00      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_15199,plain,
% 3.77/1.00      ( k10_relat_1(sK6,k2_relat_1(sK6)) = k1_relat_1(sK6) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_15195,c_1783]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_0,plain,
% 3.77/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1801,plain,
% 3.77/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.77/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_25,plain,
% 3.77/1.00      ( v4_relat_1(X0,X1)
% 3.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.77/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_21,plain,
% 3.77/1.00      ( ~ v4_relat_1(X0,X1)
% 3.77/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.77/1.00      | ~ v1_relat_1(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_410,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.77/1.00      | ~ v1_relat_1(X0) ),
% 3.77/1.00      inference(resolution,[status(thm)],[c_25,c_21]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1774,plain,
% 3.77/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.77/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2195,plain,
% 3.77/1.00      ( r1_tarski(k1_relat_1(sK6),sK5) = iProver_top
% 3.77/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1778,c_1774]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1786,plain,
% 3.77/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.77/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_16,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1787,plain,
% 3.77/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.77/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.77/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3304,plain,
% 3.77/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.77/1.00      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.77/1.00      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1786,c_1787]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_441,plain,
% 3.77/1.00      ( ~ r1_tarski(X0,X1)
% 3.77/1.00      | r2_hidden(X2,X3)
% 3.77/1.00      | v1_xboole_0(X3)
% 3.77/1.00      | X0 != X2
% 3.77/1.00      | k1_zfmisc_1(X1) != X3 ),
% 3.77/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_249]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_442,plain,
% 3.77/1.00      ( ~ r1_tarski(X0,X1)
% 3.77/1.00      | r2_hidden(X0,k1_zfmisc_1(X1))
% 3.77/1.00      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 3.77/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_14,plain,
% 3.77/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_452,plain,
% 3.77/1.00      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.77/1.00      inference(forward_subsumption_resolution,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_442,c_14]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_455,plain,
% 3.77/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.77/1.00      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8887,plain,
% 3.77/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.77/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_3304,c_455]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8888,plain,
% 3.77/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.77/1.00      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_8887]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_10,plain,
% 3.77/1.00      ( ~ r2_hidden(X0,X1)
% 3.77/1.00      | ~ r2_hidden(X2,X0)
% 3.77/1.00      | r2_hidden(X2,k3_tarski(X1)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1792,plain,
% 3.77/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.77/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.77/1.00      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8895,plain,
% 3.77/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.77/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.77/1.00      | r2_hidden(X2,k3_tarski(k1_zfmisc_1(X1))) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_8888,c_1792]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_13,plain,
% 3.77/1.00      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.77/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8899,plain,
% 3.77/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.77/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.77/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_8895,c_13]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8983,plain,
% 3.77/1.00      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.77/1.00      | r2_hidden(X0,sK5) = iProver_top
% 3.77/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2195,c_8899]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_15,plain,
% 3.77/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1868,plain,
% 3.77/1.00      ( m1_subset_1(X0,sK5) | ~ r2_hidden(X0,sK5) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1869,plain,
% 3.77/1.00      ( m1_subset_1(X0,sK5) = iProver_top
% 3.77/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1868]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_26,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1781,plain,
% 3.77/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.77/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2987,plain,
% 3.77/1.00      ( k1_relset_1(sK5,sK4,sK6) = k1_relat_1(sK6) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1778,c_1781]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_28,negated_conjecture,
% 3.77/1.00      ( ~ m1_subset_1(X0,sK5)
% 3.77/1.00      | ~ r2_hidden(X0,k1_relset_1(sK5,sK4,sK6)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1779,plain,
% 3.77/1.00      ( m1_subset_1(X0,sK5) != iProver_top
% 3.77/1.00      | r2_hidden(X0,k1_relset_1(sK5,sK4,sK6)) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3078,plain,
% 3.77/1.00      ( m1_subset_1(X0,sK5) != iProver_top
% 3.77/1.00      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_2987,c_1779]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_9266,plain,
% 3.77/1.00      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_8983,c_1869,c_2585,c_3078,c_4324,c_4399]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_9272,plain,
% 3.77/1.00      ( v1_xboole_0(k1_relat_1(sK6)) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1801,c_9266]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2,plain,
% 3.77/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1799,plain,
% 3.77/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6,plain,
% 3.77/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.77/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1796,plain,
% 3.77/1.00      ( X0 = X1
% 3.77/1.00      | v1_xboole_0(X0) != iProver_top
% 3.77/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2919,plain,
% 3.77/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1799,c_1796]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_9287,plain,
% 3.77/1.00      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_9272,c_2919]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_15200,plain,
% 3.77/1.00      ( k10_relat_1(sK6,k2_relat_1(sK6)) = k1_xboole_0 ),
% 3.77/1.00      inference(light_normalisation,[status(thm)],[c_15199,c_9287]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_24,plain,
% 3.77/1.00      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.77/1.00      | ~ v1_relat_1(X1)
% 3.77/1.00      | k10_relat_1(X1,X0) != k1_xboole_0
% 3.77/1.00      | k1_xboole_0 = X0 ),
% 3.77/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1782,plain,
% 3.77/1.00      ( k10_relat_1(X0,X1) != k1_xboole_0
% 3.77/1.00      | k1_xboole_0 = X1
% 3.77/1.00      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 3.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_17406,plain,
% 3.77/1.00      ( k2_relat_1(sK6) = k1_xboole_0
% 3.77/1.00      | r1_tarski(k2_relat_1(sK6),k2_relat_1(sK6)) != iProver_top
% 3.77/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_15200,c_1782]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5,plain,
% 3.77/1.00      ( r1_tarski(X0,X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6819,plain,
% 3.77/1.00      ( r1_tarski(k2_relat_1(sK6),k2_relat_1(sK6)) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6820,plain,
% 3.77/1.00      ( r1_tarski(k2_relat_1(sK6),k2_relat_1(sK6)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_6819]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_27,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1780,plain,
% 3.77/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.77/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2770,plain,
% 3.77/1.00      ( k2_relset_1(sK5,sK4,sK6) = k2_relat_1(sK6) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1778,c_1780]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_29,negated_conjecture,
% 3.77/1.00      ( k1_xboole_0 != k2_relset_1(sK5,sK4,sK6) ),
% 3.77/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2991,plain,
% 3.77/1.00      ( k2_relat_1(sK6) != k1_xboole_0 ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_2770,c_29]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(contradiction,plain,
% 3.77/1.00      ( $false ),
% 3.77/1.00      inference(minisat,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_17406,c_6820,c_4399,c_4324,c_2991,c_2585]) ).
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  ------                               Statistics
% 3.77/1.00  
% 3.77/1.00  ------ General
% 3.77/1.00  
% 3.77/1.00  abstr_ref_over_cycles:                  0
% 3.77/1.00  abstr_ref_under_cycles:                 0
% 3.77/1.00  gc_basic_clause_elim:                   0
% 3.77/1.00  forced_gc_time:                         0
% 3.77/1.00  parsing_time:                           0.009
% 3.77/1.00  unif_index_cands_time:                  0.
% 3.77/1.00  unif_index_add_time:                    0.
% 3.77/1.00  orderings_time:                         0.
% 3.77/1.00  out_proof_time:                         0.01
% 3.77/1.00  total_time:                             0.5
% 3.77/1.00  num_of_symbols:                         53
% 3.77/1.00  num_of_terms:                           19336
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing
% 3.77/1.00  
% 3.77/1.00  num_of_splits:                          0
% 3.77/1.00  num_of_split_atoms:                     0
% 3.77/1.00  num_of_reused_defs:                     0
% 3.77/1.00  num_eq_ax_congr_red:                    32
% 3.77/1.00  num_of_sem_filtered_clauses:            1
% 3.77/1.00  num_of_subtypes:                        0
% 3.77/1.00  monotx_restored_types:                  0
% 3.77/1.00  sat_num_of_epr_types:                   0
% 3.77/1.00  sat_num_of_non_cyclic_types:            0
% 3.77/1.00  sat_guarded_non_collapsed_types:        0
% 3.77/1.00  num_pure_diseq_elim:                    0
% 3.77/1.00  simp_replaced_by:                       0
% 3.77/1.00  res_preprocessed:                       149
% 3.77/1.00  prep_upred:                             0
% 3.77/1.00  prep_unflattend:                        46
% 3.77/1.00  smt_new_axioms:                         0
% 3.77/1.00  pred_elim_cands:                        5
% 3.77/1.00  pred_elim:                              1
% 3.77/1.00  pred_elim_cl:                           2
% 3.77/1.00  pred_elim_cycles:                       3
% 3.77/1.00  merged_defs:                            8
% 3.77/1.00  merged_defs_ncl:                        0
% 3.77/1.00  bin_hyper_res:                          9
% 3.77/1.00  prep_cycles:                            4
% 3.77/1.00  pred_elim_time:                         0.009
% 3.77/1.00  splitting_time:                         0.
% 3.77/1.00  sem_filter_time:                        0.
% 3.77/1.00  monotx_time:                            0.001
% 3.77/1.00  subtype_inf_time:                       0.
% 3.77/1.00  
% 3.77/1.00  ------ Problem properties
% 3.77/1.00  
% 3.77/1.00  clauses:                                30
% 3.77/1.00  conjectures:                            5
% 3.77/1.00  epr:                                    10
% 3.77/1.00  horn:                                   26
% 3.77/1.00  ground:                                 5
% 3.77/1.00  unary:                                  9
% 3.77/1.00  binary:                                 11
% 3.77/1.00  lits:                                   63
% 3.77/1.00  lits_eq:                                12
% 3.77/1.00  fd_pure:                                0
% 3.77/1.00  fd_pseudo:                              0
% 3.77/1.00  fd_cond:                                1
% 3.77/1.00  fd_pseudo_cond:                         5
% 3.77/1.00  ac_symbols:                             0
% 3.77/1.00  
% 3.77/1.00  ------ Propositional Solver
% 3.77/1.00  
% 3.77/1.00  prop_solver_calls:                      32
% 3.77/1.00  prop_fast_solver_calls:                 1315
% 3.77/1.00  smt_solver_calls:                       0
% 3.77/1.00  smt_fast_solver_calls:                  0
% 3.77/1.00  prop_num_of_clauses:                    7644
% 3.77/1.00  prop_preprocess_simplified:             18133
% 3.77/1.00  prop_fo_subsumed:                       11
% 3.77/1.00  prop_solver_time:                       0.
% 3.77/1.00  smt_solver_time:                        0.
% 3.77/1.00  smt_fast_solver_time:                   0.
% 3.77/1.00  prop_fast_solver_time:                  0.
% 3.77/1.00  prop_unsat_core_time:                   0.
% 3.77/1.00  
% 3.77/1.00  ------ QBF
% 3.77/1.00  
% 3.77/1.00  qbf_q_res:                              0
% 3.77/1.00  qbf_num_tautologies:                    0
% 3.77/1.00  qbf_prep_cycles:                        0
% 3.77/1.00  
% 3.77/1.00  ------ BMC1
% 3.77/1.00  
% 3.77/1.00  bmc1_current_bound:                     -1
% 3.77/1.00  bmc1_last_solved_bound:                 -1
% 3.77/1.00  bmc1_unsat_core_size:                   -1
% 3.77/1.00  bmc1_unsat_core_parents_size:           -1
% 3.77/1.00  bmc1_merge_next_fun:                    0
% 3.77/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.77/1.00  
% 3.77/1.00  ------ Instantiation
% 3.77/1.00  
% 3.77/1.00  inst_num_of_clauses:                    2014
% 3.77/1.00  inst_num_in_passive:                    1094
% 3.77/1.00  inst_num_in_active:                     876
% 3.77/1.00  inst_num_in_unprocessed:                49
% 3.77/1.00  inst_num_of_loops:                      1010
% 3.77/1.00  inst_num_of_learning_restarts:          0
% 3.77/1.00  inst_num_moves_active_passive:          130
% 3.77/1.00  inst_lit_activity:                      0
% 3.77/1.00  inst_lit_activity_moves:                0
% 3.77/1.00  inst_num_tautologies:                   0
% 3.77/1.00  inst_num_prop_implied:                  0
% 3.77/1.00  inst_num_existing_simplified:           0
% 3.77/1.00  inst_num_eq_res_simplified:             0
% 3.77/1.00  inst_num_child_elim:                    0
% 3.77/1.00  inst_num_of_dismatching_blockings:      1657
% 3.77/1.00  inst_num_of_non_proper_insts:           2897
% 3.77/1.00  inst_num_of_duplicates:                 0
% 3.77/1.00  inst_inst_num_from_inst_to_res:         0
% 3.77/1.00  inst_dismatching_checking_time:         0.
% 3.77/1.00  
% 3.77/1.00  ------ Resolution
% 3.77/1.00  
% 3.77/1.00  res_num_of_clauses:                     0
% 3.77/1.00  res_num_in_passive:                     0
% 3.77/1.00  res_num_in_active:                      0
% 3.77/1.00  res_num_of_loops:                       153
% 3.77/1.00  res_forward_subset_subsumed:            325
% 3.77/1.00  res_backward_subset_subsumed:           16
% 3.77/1.00  res_forward_subsumed:                   0
% 3.77/1.00  res_backward_subsumed:                  0
% 3.77/1.00  res_forward_subsumption_resolution:     2
% 3.77/1.00  res_backward_subsumption_resolution:    0
% 3.77/1.00  res_clause_to_clause_subsumption:       2688
% 3.77/1.00  res_orphan_elimination:                 0
% 3.77/1.00  res_tautology_del:                      168
% 3.77/1.00  res_num_eq_res_simplified:              0
% 3.77/1.00  res_num_sel_changes:                    0
% 3.77/1.00  res_moves_from_active_to_pass:          0
% 3.77/1.00  
% 3.77/1.00  ------ Superposition
% 3.77/1.00  
% 3.77/1.00  sup_time_total:                         0.
% 3.77/1.00  sup_time_generating:                    0.
% 3.77/1.00  sup_time_sim_full:                      0.
% 3.77/1.00  sup_time_sim_immed:                     0.
% 3.77/1.00  
% 3.77/1.00  sup_num_of_clauses:                     561
% 3.77/1.00  sup_num_in_active:                      179
% 3.77/1.00  sup_num_in_passive:                     382
% 3.77/1.00  sup_num_of_loops:                       200
% 3.77/1.00  sup_fw_superposition:                   401
% 3.77/1.00  sup_bw_superposition:                   557
% 3.77/1.00  sup_immediate_simplified:               269
% 3.77/1.00  sup_given_eliminated:                   3
% 3.77/1.00  comparisons_done:                       0
% 3.77/1.00  comparisons_avoided:                    6
% 3.77/1.00  
% 3.77/1.00  ------ Simplifications
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  sim_fw_subset_subsumed:                 103
% 3.77/1.00  sim_bw_subset_subsumed:                 60
% 3.77/1.00  sim_fw_subsumed:                        51
% 3.77/1.00  sim_bw_subsumed:                        29
% 3.77/1.00  sim_fw_subsumption_res:                 0
% 3.77/1.00  sim_bw_subsumption_res:                 0
% 3.77/1.00  sim_tautology_del:                      8
% 3.77/1.00  sim_eq_tautology_del:                   7
% 3.77/1.00  sim_eq_res_simp:                        0
% 3.77/1.00  sim_fw_demodulated:                     20
% 3.77/1.00  sim_bw_demodulated:                     23
% 3.77/1.00  sim_light_normalised:                   28
% 3.77/1.00  sim_joinable_taut:                      0
% 3.77/1.00  sim_joinable_simp:                      0
% 3.77/1.00  sim_ac_normalised:                      0
% 3.77/1.00  sim_smt_subsumption:                    0
% 3.77/1.00  
%------------------------------------------------------------------------------
