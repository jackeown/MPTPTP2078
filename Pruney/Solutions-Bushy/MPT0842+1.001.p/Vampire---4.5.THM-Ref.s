%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0842+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:45 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 958 expanded)
%              Number of leaves         :   20 ( 391 expanded)
%              Depth                    :   33
%              Number of atoms          :  551 (10081 expanded)
%              Number of equality atoms :   14 ( 114 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(resolution,[],[f331,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f3,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f331,plain,(
    ! [X0] : ~ m1_subset_1(X0,sK2) ),
    inference(resolution,[],[f330,f46])).

fof(f46,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK1)
          | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
          | ~ m1_subset_1(X5,sK2) )
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
    & ( ( r2_hidden(sK5,sK1)
        & r2_hidden(k4_tarski(sK4,sK5),sK3)
        & m1_subset_1(sK5,sK2) )
      | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f30,f29,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X4,X5),X3)
                              | ~ m1_subset_1(X5,X2) )
                          | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                        & ( ? [X6] :
                              ( r2_hidden(X6,X1)
                              & r2_hidden(k4_tarski(X4,X6),X3)
                              & m1_subset_1(X6,X2) )
                          | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                        & m1_subset_1(X4,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X4,X5),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k8_relset_1(sK0,X2,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X4,X6),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k8_relset_1(sK0,X2,X3,X1)) )
                      & m1_subset_1(X4,sK0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ! [X5] :
                          ( ~ r2_hidden(X5,X1)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ m1_subset_1(X5,X2) )
                      | ~ r2_hidden(X4,k8_relset_1(sK0,X2,X3,X1)) )
                    & ( ? [X6] :
                          ( r2_hidden(X6,X1)
                          & r2_hidden(k4_tarski(X4,X6),X3)
                          & m1_subset_1(X6,X2) )
                      | r2_hidden(X4,k8_relset_1(sK0,X2,X3,X1)) )
                    & m1_subset_1(X4,sK0) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ! [X5] :
                        ( ~ r2_hidden(X5,sK1)
                        | ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ m1_subset_1(X5,X2) )
                    | ~ r2_hidden(X4,k8_relset_1(sK0,X2,X3,sK1)) )
                  & ( ? [X6] :
                        ( r2_hidden(X6,sK1)
                        & r2_hidden(k4_tarski(X4,X6),X3)
                        & m1_subset_1(X6,X2) )
                    | r2_hidden(X4,k8_relset_1(sK0,X2,X3,sK1)) )
                  & m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ! [X5] :
                      ( ~ r2_hidden(X5,sK1)
                      | ~ r2_hidden(k4_tarski(X4,X5),X3)
                      | ~ m1_subset_1(X5,X2) )
                  | ~ r2_hidden(X4,k8_relset_1(sK0,X2,X3,sK1)) )
                & ( ? [X6] :
                      ( r2_hidden(X6,sK1)
                      & r2_hidden(k4_tarski(X4,X6),X3)
                      & m1_subset_1(X6,X2) )
                  | r2_hidden(X4,k8_relset_1(sK0,X2,X3,sK1)) )
                & m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ! [X5] :
                    ( ~ r2_hidden(X5,sK1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X3)
                    | ~ m1_subset_1(X5,sK2) )
                | ~ r2_hidden(X4,k8_relset_1(sK0,sK2,X3,sK1)) )
              & ( ? [X6] :
                    ( r2_hidden(X6,sK1)
                    & r2_hidden(k4_tarski(X4,X6),X3)
                    & m1_subset_1(X6,sK2) )
                | r2_hidden(X4,k8_relset_1(sK0,sK2,X3,sK1)) )
              & m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,sK1)
                  | ~ r2_hidden(k4_tarski(X4,X5),X3)
                  | ~ m1_subset_1(X5,sK2) )
              | ~ r2_hidden(X4,k8_relset_1(sK0,sK2,X3,sK1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,sK1)
                  & r2_hidden(k4_tarski(X4,X6),X3)
                  & m1_subset_1(X6,sK2) )
              | r2_hidden(X4,k8_relset_1(sK0,sK2,X3,sK1)) )
            & m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) )
   => ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,sK1)
                | ~ r2_hidden(k4_tarski(X4,X5),sK3)
                | ~ m1_subset_1(X5,sK2) )
            | ~ r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK1)
                & r2_hidden(k4_tarski(X4,X6),sK3)
                & m1_subset_1(X6,sK2) )
            | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X4] :
        ( ( ! [X5] :
              ( ~ r2_hidden(X5,sK1)
              | ~ r2_hidden(k4_tarski(X4,X5),sK3)
              | ~ m1_subset_1(X5,sK2) )
          | ~ r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,sK1)
              & r2_hidden(k4_tarski(X4,X6),sK3)
              & m1_subset_1(X6,sK2) )
          | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
        & m1_subset_1(X4,sK0) )
   => ( ( ! [X5] :
            ( ~ r2_hidden(X5,sK1)
            | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
            | ~ m1_subset_1(X5,sK2) )
        | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
      & ( ? [X6] :
            ( r2_hidden(X6,sK1)
            & r2_hidden(k4_tarski(sK4,X6),sK3)
            & m1_subset_1(X6,sK2) )
        | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X6] :
        ( r2_hidden(X6,sK1)
        & r2_hidden(k4_tarski(sK4,X6),sK3)
        & m1_subset_1(X6,sK2) )
   => ( r2_hidden(sK5,sK1)
      & r2_hidden(k4_tarski(sK4,sK5),sK3)
      & m1_subset_1(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X4,X5),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X4,X6),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X4,X5),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) )
                        | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X4,X5),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) )
                        | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).

fof(f330,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f324,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f324,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X1,sK0) ) ),
    inference(resolution,[],[f323,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f323,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ m1_subset_1(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f318,f44])).

fof(f44,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f318,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X1,sK2) ) ),
    inference(resolution,[],[f317,f59])).

fof(f317,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f316,f107])).

fof(f107,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X15,X13))
      | ~ r2_hidden(X14,X15)
      | ~ r2_hidden(X12,X13) ) ),
    inference(resolution,[],[f66,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f316,plain,(
    v1_xboole_0(k2_zfmisc_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f315,f222])).

fof(f222,plain,(
    m1_subset_1(sK4,k10_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f221,f156])).

fof(f156,plain,
    ( m1_subset_1(sK4,k10_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f145,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f145,plain,
    ( m1_subset_1(sK4,k10_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(superposition,[],[f80,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f80,plain,
    ( m1_subset_1(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(resolution,[],[f58,f49])).

fof(f49,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f221,plain,
    ( ~ r2_hidden(sK5,sK1)
    | m1_subset_1(sK4,k10_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f217,f157])).

fof(f157,plain,
    ( m1_subset_1(sK4,k10_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f146,f45])).

fof(f146,plain,
    ( m1_subset_1(sK4,k10_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(superposition,[],[f81,f63])).

fof(f81,plain,
    ( m1_subset_1(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(resolution,[],[f58,f47])).

fof(f47,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f217,plain,
    ( ~ m1_subset_1(sK5,sK2)
    | ~ r2_hidden(sK5,sK1)
    | m1_subset_1(sK4,k10_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f216,f155])).

fof(f155,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | m1_subset_1(sK4,k10_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f144,f45])).

fof(f144,plain,
    ( m1_subset_1(sK4,k10_relat_1(sK3,sK1))
    | r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(superposition,[],[f79,f63])).

fof(f79,plain,
    ( m1_subset_1(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    inference(resolution,[],[f58,f48])).

fof(f48,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f216,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK4,X0),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f215,f94])).

fof(f94,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f61,f45])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f215,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK4,X0),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ v1_relat_1(sK3) ) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK4,X0),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ v1_relat_1(sK3) ) ),
    inference(condensation,[],[f212])).

fof(f212,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(k4_tarski(sK4,X3),sK3)
      | ~ m1_subset_1(X3,sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(k4_tarski(sK4,X4),sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f151,f67])).

fof(f67,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK7(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK8(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f33,f36,f35,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f151,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
      | ~ r2_hidden(k4_tarski(sK4,X0),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f140,f45])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
      | ~ r2_hidden(k4_tarski(sK4,X0),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    inference(superposition,[],[f50,f63])).

fof(f50,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f315,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK2))
    | ~ m1_subset_1(sK4,k10_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f313,f224])).

fof(f224,plain,(
    ~ v1_xboole_0(k10_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f223,f153])).

fof(f153,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f142,f45])).

fof(f142,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(superposition,[],[f71,f63])).

fof(f71,plain,
    ( ~ v1_xboole_0(k8_relset_1(sK0,sK2,sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(resolution,[],[f60,f49])).

fof(f223,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ v1_xboole_0(k10_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f218,f154])).

fof(f154,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f143,f45])).

fof(f143,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(superposition,[],[f72,f63])).

fof(f72,plain,
    ( ~ v1_xboole_0(k8_relset_1(sK0,sK2,sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(resolution,[],[f60,f47])).

fof(f218,plain,
    ( ~ m1_subset_1(sK5,sK2)
    | ~ r2_hidden(sK5,sK1)
    | ~ v1_xboole_0(k10_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f216,f152])).

fof(f152,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ v1_xboole_0(k10_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f141,f45])).

fof(f141,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK3,sK1))
    | r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(superposition,[],[f70,f63])).

fof(f70,plain,
    ( ~ v1_xboole_0(k8_relset_1(sK0,sK2,sK3,sK1))
    | r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    inference(resolution,[],[f60,f48])).

fof(f313,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK2))
    | v1_xboole_0(k10_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK4,k10_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f308,f59])).

fof(f308,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f307])).

fof(f307,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK2))
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f305,f286])).

fof(f286,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(sK3,X1,X0),sK2)
      | v1_xboole_0(k2_zfmisc_1(sK0,sK2))
      | ~ r2_hidden(X0,k10_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f267,f58])).

fof(f267,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK8(sK3,X7,X6),sK2)
      | ~ r2_hidden(X6,k10_relat_1(sK3,X7))
      | v1_xboole_0(k2_zfmisc_1(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f253,f94])).

fof(f253,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k10_relat_1(sK3,X7))
      | ~ v1_relat_1(sK3)
      | r2_hidden(sK8(sK3,X7,X6),sK2)
      | v1_xboole_0(k2_zfmisc_1(sK0,sK2)) ) ),
    inference(resolution,[],[f69,f132])).

fof(f132,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X4),sK3)
      | r2_hidden(X4,sK2)
      | v1_xboole_0(k2_zfmisc_1(sK0,sK2)) ) ),
    inference(resolution,[],[f103,f99])).

fof(f99,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k2_zfmisc_1(sK0,sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f62,f45])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(X3,X0),k2_zfmisc_1(X2,X1))
      | v1_xboole_0(k2_zfmisc_1(X2,X1))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f65,f59])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f305,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f304,f94])).

fof(f304,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f266,f68])).

fof(f68,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f266,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(sK3,X0,sK4),sK1)
      | ~ m1_subset_1(sK8(sK3,X0,sK4),sK2)
      | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f265,f222])).

fof(f265,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k10_relat_1(sK3,X0))
      | ~ m1_subset_1(sK4,k10_relat_1(sK3,sK1))
      | ~ m1_subset_1(sK8(sK3,X0,sK4),sK2)
      | ~ r2_hidden(sK8(sK3,X0,sK4),sK1) ) ),
    inference(subsumption_resolution,[],[f264,f224])).

fof(f264,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k10_relat_1(sK3,X0))
      | v1_xboole_0(k10_relat_1(sK3,sK1))
      | ~ m1_subset_1(sK4,k10_relat_1(sK3,sK1))
      | ~ m1_subset_1(sK8(sK3,X0,sK4),sK2)
      | ~ r2_hidden(sK8(sK3,X0,sK4),sK1) ) ),
    inference(subsumption_resolution,[],[f247,f94])).

fof(f247,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k10_relat_1(sK3,X0))
      | ~ v1_relat_1(sK3)
      | v1_xboole_0(k10_relat_1(sK3,sK1))
      | ~ m1_subset_1(sK4,k10_relat_1(sK3,sK1))
      | ~ m1_subset_1(sK8(sK3,X0,sK4),sK2)
      | ~ r2_hidden(sK8(sK3,X0,sK4),sK1) ) ),
    inference(resolution,[],[f69,f158])).

fof(f158,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(sK4,X1),sK3)
      | v1_xboole_0(k10_relat_1(sK3,sK1))
      | ~ m1_subset_1(sK4,k10_relat_1(sK3,sK1))
      | ~ m1_subset_1(X1,sK2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f147,f45])).

fof(f147,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK4,k10_relat_1(sK3,sK1))
      | v1_xboole_0(k10_relat_1(sK3,sK1))
      | ~ r2_hidden(k4_tarski(sK4,X1),sK3)
      | ~ m1_subset_1(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    inference(superposition,[],[f85,f63])).

fof(f85,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
      | v1_xboole_0(k8_relset_1(sK0,sK2,sK3,sK1))
      | ~ r2_hidden(k4_tarski(sK4,X4),sK3)
      | ~ m1_subset_1(X4,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(resolution,[],[f59,f50])).

%------------------------------------------------------------------------------
