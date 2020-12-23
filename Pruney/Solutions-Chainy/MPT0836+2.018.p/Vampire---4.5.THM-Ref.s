%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 233 expanded)
%              Number of leaves         :   24 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  363 (1505 expanded)
%              Number of equality atoms :   12 (  44 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f92,f104,f160,f173,f176,f260,f279])).

fof(f279,plain,
    ( ~ spl8_1
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_7 ),
    inference(resolution,[],[f262,f174])).

fof(f174,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f107,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
          | ~ m1_subset_1(X4,sK1) )
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
    & ( ( r2_hidden(k4_tarski(sK3,sK4),sK2)
        & m1_subset_1(sK4,sK1) )
      | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f25,f24,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                          | ~ m1_subset_1(X4,X1) )
                      | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                    & ( ? [X5] :
                          ( r2_hidden(k4_tarski(X3,X5),X2)
                          & m1_subset_1(X5,X1) )
                      | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(sK0,X1,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X3,X5),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k1_relset_1(sK0,X1,X2)) )
                  & m1_subset_1(X3,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

% (28396)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                      | ~ m1_subset_1(X4,X1) )
                  | ~ r2_hidden(X3,k1_relset_1(sK0,X1,X2)) )
                & ( ? [X5] :
                      ( r2_hidden(k4_tarski(X3,X5),X2)
                      & m1_subset_1(X5,X1) )
                  | r2_hidden(X3,k1_relset_1(sK0,X1,X2)) )
                & m1_subset_1(X3,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ m1_subset_1(X4,sK1) )
                | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,X2)) )
              & ( ? [X5] :
                    ( r2_hidden(k4_tarski(X3,X5),X2)
                    & m1_subset_1(X5,sK1) )
                | r2_hidden(X3,k1_relset_1(sK0,sK1,X2)) )
              & m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                  | ~ m1_subset_1(X4,sK1) )
              | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X3,X5),X2)
                  & m1_subset_1(X5,sK1) )
              | r2_hidden(X3,k1_relset_1(sK0,sK1,X2)) )
            & m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),sK2)
                | ~ m1_subset_1(X4,sK1) )
            | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X3,X5),sK2)
                & m1_subset_1(X5,sK1) )
            | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
          & m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X3,X4),sK2)
              | ~ m1_subset_1(X4,sK1) )
          | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X3,X5),sK2)
              & m1_subset_1(X5,sK1) )
          | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
        & m1_subset_1(X3,sK0) )
   => ( ( ! [X4] :
            ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
            | ~ m1_subset_1(X4,sK1) )
        | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(sK3,X5),sK2)
            & m1_subset_1(X5,sK1) )
        | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(sK3,X5),sK2)
        & m1_subset_1(X5,sK1) )
   => ( r2_hidden(k4_tarski(sK3,sK4),sK2)
      & m1_subset_1(sK4,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X3,X5),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <~> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                    <=> ? [X4] :
                          ( r2_hidden(k4_tarski(X3,X4),X2)
                          & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).

fof(f107,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_1 ),
    inference(superposition,[],[f63,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f63,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl8_1
  <=> r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f262,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_relat_1(sK2))
    | ~ spl8_7 ),
    inference(resolution,[],[f88,f55])).

fof(f55,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f88,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl8_7
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f260,plain,
    ( ~ spl8_1
    | ~ spl8_9
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_9
    | spl8_11 ),
    inference(subsumption_resolution,[],[f257,f174])).

fof(f257,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl8_9
    | spl8_11 ),
    inference(resolution,[],[f238,f172])).

fof(f172,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3),sK1)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl8_11
  <=> m1_subset_1(sK7(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f238,plain,
    ( ! [X0] :
        ( m1_subset_1(sK7(sK2,X0),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl8_9 ),
    inference(resolution,[],[f206,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f206,plain,
    ( ! [X1] :
        ( r2_hidden(sK7(sK2,X1),sK1)
        | ~ r2_hidden(X1,k1_relat_1(sK2)) )
    | ~ spl8_9 ),
    inference(resolution,[],[f189,f55])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(X1,sK1) )
    | ~ spl8_9 ),
    inference(resolution,[],[f159,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f159,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl8_9
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f176,plain,
    ( ~ spl8_1
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl8_1
    | spl8_10 ),
    inference(subsumption_resolution,[],[f169,f174])).

fof(f169,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl8_10
  <=> r2_hidden(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f173,plain,
    ( ~ spl8_10
    | ~ spl8_11
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f109,f60,f171,f168])).

fof(f60,plain,
    ( spl8_2
  <=> ! [X4] :
        ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        | ~ m1_subset_1(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f109,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3),sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl8_2 ),
    inference(resolution,[],[f61,f55])).

fof(f61,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f160,plain,
    ( spl8_8
    | spl8_9 ),
    inference(avatar_split_clause,[],[f130,f158,f90])).

fof(f90,plain,
    ( spl8_8
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f95,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f49,f37])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f104,plain,
    ( spl8_1
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f102,f37])).

fof(f102,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f101,f94])).

fof(f94,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl8_3 ),
    inference(resolution,[],[f54,f66])).

fof(f66,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl8_3
  <=> r2_hidden(k4_tarski(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f54,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl8_1 ),
    inference(superposition,[],[f58,f48])).

fof(f58,plain,
    ( ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f92,plain,
    ( spl8_7
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f85,f90,f87])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f50,f37])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f67,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f40,f65,f57])).

fof(f40,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f41,f60,f57])).

fof(f41,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      | ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:34:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (28393)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (28389)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (28382)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (28385)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (28394)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (28386)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (28387)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (28395)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (28382)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f62,f67,f92,f104,f160,f173,f176,f260,f279])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    ~spl8_1 | ~spl8_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f273])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    $false | (~spl8_1 | ~spl8_7)),
% 0.22/0.50    inference(resolution,[],[f262,f174])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    r2_hidden(sK3,k1_relat_1(sK2)) | ~spl8_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f107,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ((((! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) & ((r2_hidden(k4_tarski(sK3,sK4),sK2) & m1_subset_1(sK4,sK1)) | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) & m1_subset_1(sK3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f25,f24,f23,f22,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(sK0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(sK0,X1,X2))) & m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  % (28396)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(sK0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(sK0,X1,X2))) & m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k1_relset_1(sK0,sK1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k1_relset_1(sK0,sK1,X2))) & m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k1_relset_1(sK0,sK1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k1_relset_1(sK0,sK1,X2))) & m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k1_relset_1(sK0,sK1,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2))) & m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k1_relset_1(sK0,sK1,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2))) & m1_subset_1(X3,sK0)) => ((! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) & (? [X5] : (r2_hidden(k4_tarski(sK3,X5),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) & m1_subset_1(sK3,sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ? [X5] : (r2_hidden(k4_tarski(sK3,X5),sK2) & m1_subset_1(X5,sK1)) => (r2_hidden(k4_tarski(sK3,sK4),sK2) & m1_subset_1(sK4,sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(rectify,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2)))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_hidden(X3,k1_relset_1(X0,X1,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    r2_hidden(sK3,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_1),
% 0.22/0.50    inference(superposition,[],[f63,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) | ~spl8_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    spl8_1 <=> r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.50  fof(f262,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2))) ) | ~spl8_7),
% 0.22/0.50    inference(resolution,[],[f88,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.22/0.50    inference(equality_resolution,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f31,f30,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.50    inference(rectify,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl8_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f87])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    spl8_7 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    ~spl8_1 | ~spl8_9 | spl8_11),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f259])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    $false | (~spl8_1 | ~spl8_9 | spl8_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f257,f174])).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    ~r2_hidden(sK3,k1_relat_1(sK2)) | (~spl8_9 | spl8_11)),
% 0.22/0.50    inference(resolution,[],[f238,f172])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    ~m1_subset_1(sK7(sK2,sK3),sK1) | spl8_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f171])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    spl8_11 <=> m1_subset_1(sK7(sK2,sK3),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(sK7(sK2,X0),sK1) | ~r2_hidden(X0,k1_relat_1(sK2))) ) | ~spl8_9),
% 0.22/0.50    inference(resolution,[],[f206,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    ( ! [X1] : (r2_hidden(sK7(sK2,X1),sK1) | ~r2_hidden(X1,k1_relat_1(sK2))) ) | ~spl8_9),
% 0.22/0.50    inference(resolution,[],[f189,f55])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X1,sK1)) ) | ~spl8_9),
% 0.22/0.50    inference(resolution,[],[f159,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.50    inference(flattening,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) ) | ~spl8_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f158])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    spl8_9 <=> ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    ~spl8_1 | spl8_10),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f175])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    $false | (~spl8_1 | spl8_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f169,f174])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ~r2_hidden(sK3,k1_relat_1(sK2)) | spl8_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f168])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    spl8_10 <=> r2_hidden(sK3,k1_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ~spl8_10 | ~spl8_11 | ~spl8_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f109,f60,f171,f168])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl8_2 <=> ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ~m1_subset_1(sK7(sK2,sK3),sK1) | ~r2_hidden(sK3,k1_relat_1(sK2)) | ~spl8_2),
% 0.22/0.50    inference(resolution,[],[f61,f55])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1)) ) | ~spl8_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f60])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    spl8_8 | spl8_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f130,f158,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl8_8 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK2) | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) )),
% 0.22/0.50    inference(resolution,[],[f95,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.22/0.50    inference(resolution,[],[f49,f37])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl8_1 | ~spl8_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    $false | (spl8_1 | ~spl8_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f102,f37])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl8_1 | ~spl8_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f101,f94])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    r2_hidden(sK3,k1_relat_1(sK2)) | ~spl8_3),
% 0.22/0.50    inference(resolution,[],[f54,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK3,sK4),sK2) | ~spl8_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl8_3 <=> r2_hidden(k4_tarski(sK3,sK4),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.22/0.50    inference(equality_resolution,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl8_1),
% 0.22/0.50    inference(superposition,[],[f58,f48])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) | spl8_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f57])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl8_7 | ~spl8_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f85,f90,f87])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.22/0.50    inference(resolution,[],[f50,f37])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl8_1 | spl8_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f65,f57])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK3,sK4),sK2) | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ~spl8_1 | spl8_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f60,f57])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1) | ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (28382)------------------------------
% 0.22/0.50  % (28382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28382)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (28382)Memory used [KB]: 10874
% 0.22/0.51  % (28382)Time elapsed: 0.069 s
% 0.22/0.51  % (28382)------------------------------
% 0.22/0.51  % (28382)------------------------------
% 0.22/0.51  % (28370)Success in time 0.145 s
%------------------------------------------------------------------------------
