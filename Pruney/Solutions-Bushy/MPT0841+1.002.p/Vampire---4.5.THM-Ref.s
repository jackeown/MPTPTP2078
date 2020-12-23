%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0841+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 948 expanded)
%              Number of leaves         :   20 ( 386 expanded)
%              Depth                    :   33
%              Number of atoms          :  550 (9890 expanded)
%              Number of equality atoms :   14 ( 114 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f343,plain,(
    $false ),
    inference(resolution,[],[f338,f57])).

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

fof(f338,plain,(
    ! [X6] : ~ m1_subset_1(X6,sK0) ),
    inference(resolution,[],[f335,f57])).

fof(f335,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK2)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f330,f44])).

fof(f44,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK1)
          | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
          | ~ m1_subset_1(X5,sK2) )
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
    & ( ( r2_hidden(sK5,sK1)
        & r2_hidden(k4_tarski(sK5,sK4),sK3)
        & m1_subset_1(sK5,sK2) )
      | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
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
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                        & ( ? [X6] :
                              ( r2_hidden(X6,X1)
                              & r2_hidden(k4_tarski(X6,X4),X3)
                              & m1_subset_1(X6,X2) )
                          | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                        & m1_subset_1(X4,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X6,X4),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1)) )
                      & m1_subset_1(X4,sK0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) )
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
                          | ~ r2_hidden(k4_tarski(X5,X4),X3)
                          | ~ m1_subset_1(X5,X2) )
                      | ~ r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1)) )
                    & ( ? [X6] :
                          ( r2_hidden(X6,X1)
                          & r2_hidden(k4_tarski(X6,X4),X3)
                          & m1_subset_1(X6,X2) )
                      | r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1)) )
                    & m1_subset_1(X4,sK0) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ! [X5] :
                        ( ~ r2_hidden(X5,sK1)
                        | ~ r2_hidden(k4_tarski(X5,X4),X3)
                        | ~ m1_subset_1(X5,X2) )
                    | ~ r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1)) )
                  & ( ? [X6] :
                        ( r2_hidden(X6,sK1)
                        & r2_hidden(k4_tarski(X6,X4),X3)
                        & m1_subset_1(X6,X2) )
                    | r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1)) )
                  & m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ! [X5] :
                      ( ~ r2_hidden(X5,sK1)
                      | ~ r2_hidden(k4_tarski(X5,X4),X3)
                      | ~ m1_subset_1(X5,X2) )
                  | ~ r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1)) )
                & ( ? [X6] :
                      ( r2_hidden(X6,sK1)
                      & r2_hidden(k4_tarski(X6,X4),X3)
                      & m1_subset_1(X6,X2) )
                  | r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1)) )
                & m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ! [X5] :
                    ( ~ r2_hidden(X5,sK1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X3)
                    | ~ m1_subset_1(X5,sK2) )
                | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1)) )
              & ( ? [X6] :
                    ( r2_hidden(X6,sK1)
                    & r2_hidden(k4_tarski(X6,X4),X3)
                    & m1_subset_1(X6,sK2) )
                | r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1)) )
              & m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,sK1)
                  | ~ r2_hidden(k4_tarski(X5,X4),X3)
                  | ~ m1_subset_1(X5,sK2) )
              | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,sK1)
                  & r2_hidden(k4_tarski(X6,X4),X3)
                  & m1_subset_1(X6,sK2) )
              | r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1)) )
            & m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) )
   => ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,sK1)
                | ~ r2_hidden(k4_tarski(X5,X4),sK3)
                | ~ m1_subset_1(X5,sK2) )
            | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK1)
                & r2_hidden(k4_tarski(X6,X4),sK3)
                & m1_subset_1(X6,sK2) )
            | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X4] :
        ( ( ! [X5] :
              ( ~ r2_hidden(X5,sK1)
              | ~ r2_hidden(k4_tarski(X5,X4),sK3)
              | ~ m1_subset_1(X5,sK2) )
          | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,sK1)
              & r2_hidden(k4_tarski(X6,X4),sK3)
              & m1_subset_1(X6,sK2) )
          | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
        & m1_subset_1(X4,sK0) )
   => ( ( ! [X5] :
            ( ~ r2_hidden(X5,sK1)
            | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
            | ~ m1_subset_1(X5,sK2) )
        | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
      & ( ? [X6] :
            ( r2_hidden(X6,sK1)
            & r2_hidden(k4_tarski(X6,sK4),sK3)
            & m1_subset_1(X6,sK2) )
        | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X6] :
        ( r2_hidden(X6,sK1)
        & r2_hidden(k4_tarski(X6,sK4),sK3)
        & m1_subset_1(X6,sK2) )
   => ( r2_hidden(sK5,sK1)
      & r2_hidden(k4_tarski(sK5,sK4),sK3)
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
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X6,X4),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
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
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
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
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
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
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
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
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
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
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(f330,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X1,sK2) ) ),
    inference(resolution,[],[f329,f59])).

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

fof(f329,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f322,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f322,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X1,sK0) ) ),
    inference(resolution,[],[f321,f59])).

fof(f321,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f320,f107])).

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

fof(f320,plain,(
    v1_xboole_0(k2_zfmisc_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f319,f233])).

fof(f233,plain,(
    m1_subset_1(sK4,k9_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f232,f156])).

fof(f156,plain,
    ( m1_subset_1(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f145,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f145,plain,
    ( m1_subset_1(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f80,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f80,plain,
    ( m1_subset_1(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(resolution,[],[f58,f49])).

fof(f49,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
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

fof(f232,plain,
    ( ~ r2_hidden(sK5,sK1)
    | m1_subset_1(sK4,k9_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f228,f157])).

fof(f157,plain,
    ( m1_subset_1(sK4,k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f146,f45])).

fof(f146,plain,
    ( m1_subset_1(sK4,k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f81,f63])).

fof(f81,plain,
    ( m1_subset_1(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(resolution,[],[f58,f47])).

fof(f47,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f228,plain,
    ( ~ m1_subset_1(sK5,sK2)
    | ~ r2_hidden(sK5,sK1)
    | m1_subset_1(sK4,k9_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f227,f155])).

fof(f155,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | m1_subset_1(sK4,k9_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f144,f45])).

fof(f144,plain,
    ( m1_subset_1(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f79,f63])).

fof(f79,plain,
    ( m1_subset_1(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    inference(resolution,[],[f58,f48])).

fof(f48,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f227,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f226,f94])).

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

fof(f226,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ v1_relat_1(sK3) ) ),
    inference(duplicate_literal_removal,[],[f225])).

fof(f225,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK1)
      | ~ v1_relat_1(sK3) ) ),
    inference(condensation,[],[f223])).

fof(f223,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(k4_tarski(X3,sK4),sK3)
      | ~ m1_subset_1(X3,sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(k4_tarski(X4,sK4),sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f151,f67])).

fof(f67,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK7(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK8(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f33,f36,f35,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f151,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
      | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f140,f45])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
      | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    inference(superposition,[],[f50,f63])).

fof(f50,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f319,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK2,sK0))
    | ~ m1_subset_1(sK4,k9_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f317,f235])).

fof(f235,plain,(
    ~ v1_xboole_0(k9_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f234,f153])).

fof(f153,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f142,f45])).

fof(f142,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f71,f63])).

fof(f71,plain,
    ( ~ v1_xboole_0(k7_relset_1(sK2,sK0,sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(resolution,[],[f60,f49])).

fof(f234,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ v1_xboole_0(k9_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f229,f154])).

fof(f154,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f143,f45])).

fof(f143,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f72,f63])).

fof(f72,plain,
    ( ~ v1_xboole_0(k7_relset_1(sK2,sK0,sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(resolution,[],[f60,f47])).

fof(f229,plain,
    ( ~ m1_subset_1(sK5,sK2)
    | ~ r2_hidden(sK5,sK1)
    | ~ v1_xboole_0(k9_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f227,f152])).

fof(f152,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ v1_xboole_0(k9_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f141,f45])).

fof(f141,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f70,f63])).

fof(f70,plain,
    ( ~ v1_xboole_0(k7_relset_1(sK2,sK0,sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    inference(resolution,[],[f60,f48])).

fof(f317,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK2,sK0))
    | v1_xboole_0(k9_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK4,k9_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f312,f59])).

fof(f312,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | v1_xboole_0(k2_zfmisc_1(sK2,sK0)) ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | v1_xboole_0(k2_zfmisc_1(sK2,sK0))
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f309,f290])).

fof(f290,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(sK3,X1,X0),sK2)
      | v1_xboole_0(k2_zfmisc_1(sK2,sK0))
      | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f272,f58])).

fof(f272,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK8(sK3,X9,X8),sK2)
      | ~ r2_hidden(X8,k9_relat_1(sK3,X9))
      | v1_xboole_0(k2_zfmisc_1(sK2,sK0)) ) ),
    inference(subsumption_resolution,[],[f258,f94])).

fof(f258,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,k9_relat_1(sK3,X9))
      | ~ v1_relat_1(sK3)
      | r2_hidden(sK8(sK3,X9,X8),sK2)
      | v1_xboole_0(k2_zfmisc_1(sK2,sK0)) ) ),
    inference(resolution,[],[f69,f126])).

fof(f126,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK3)
      | r2_hidden(X4,sK2)
      | v1_xboole_0(k2_zfmisc_1(sK2,sK0)) ) ),
    inference(resolution,[],[f102,f99])).

fof(f99,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k2_zfmisc_1(sK2,sK0))
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

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(X0,X3),k2_zfmisc_1(X1,X2))
      | v1_xboole_0(k2_zfmisc_1(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f64,f59])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f309,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f308,f94])).

fof(f308,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f270,f68])).

fof(f68,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f270,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(sK3,X0,sK4),sK1)
      | ~ m1_subset_1(sK8(sK3,X0,sK4),sK2)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f269,f233])).

fof(f269,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
      | ~ m1_subset_1(sK4,k9_relat_1(sK3,sK1))
      | ~ m1_subset_1(sK8(sK3,X0,sK4),sK2)
      | ~ r2_hidden(sK8(sK3,X0,sK4),sK1) ) ),
    inference(subsumption_resolution,[],[f268,f235])).

fof(f268,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
      | v1_xboole_0(k9_relat_1(sK3,sK1))
      | ~ m1_subset_1(sK4,k9_relat_1(sK3,sK1))
      | ~ m1_subset_1(sK8(sK3,X0,sK4),sK2)
      | ~ r2_hidden(sK8(sK3,X0,sK4),sK1) ) ),
    inference(subsumption_resolution,[],[f251,f94])).

fof(f251,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
      | ~ v1_relat_1(sK3)
      | v1_xboole_0(k9_relat_1(sK3,sK1))
      | ~ m1_subset_1(sK4,k9_relat_1(sK3,sK1))
      | ~ m1_subset_1(sK8(sK3,X0,sK4),sK2)
      | ~ r2_hidden(sK8(sK3,X0,sK4),sK1) ) ),
    inference(resolution,[],[f69,f158])).

fof(f158,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK4),sK3)
      | v1_xboole_0(k9_relat_1(sK3,sK1))
      | ~ m1_subset_1(sK4,k9_relat_1(sK3,sK1))
      | ~ m1_subset_1(X1,sK2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f147,f45])).

fof(f147,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK4,k9_relat_1(sK3,sK1))
      | v1_xboole_0(k9_relat_1(sK3,sK1))
      | ~ r2_hidden(k4_tarski(X1,sK4),sK3)
      | ~ m1_subset_1(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    inference(superposition,[],[f85,f63])).

fof(f85,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
      | v1_xboole_0(k7_relset_1(sK2,sK0,sK3,sK1))
      | ~ r2_hidden(k4_tarski(X4,sK4),sK3)
      | ~ m1_subset_1(X4,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(resolution,[],[f59,f50])).

%------------------------------------------------------------------------------
