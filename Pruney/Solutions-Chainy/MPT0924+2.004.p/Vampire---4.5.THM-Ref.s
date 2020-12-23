%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 429 expanded)
%              Number of leaves         :   16 ( 158 expanded)
%              Depth                    :   15
%              Number of atoms          :  348 (2654 expanded)
%              Number of equality atoms :   52 ( 746 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f72,f73,f74,f75,f83,f96,f129,f134,f140])).

fof(f140,plain,
    ( ~ spl13_1
    | spl13_3 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl13_1
    | spl13_3 ),
    inference(resolution,[],[f136,f126])).

fof(f126,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ spl13_1 ),
    inference(resolution,[],[f123,f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f119,f25])).

fof(f25,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f119,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(k1_mcart_1(X5),X3)
      | ~ r2_hidden(X5,k2_zfmisc_1(X3,X4)) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(k1_mcart_1(X5),X3)
      | ~ r2_hidden(X5,k2_zfmisc_1(X3,X4))
      | ~ r2_hidden(X5,k2_zfmisc_1(X3,X4)) ) ),
    inference(superposition,[],[f50,f86])).

fof(f86,plain,(
    ! [X10,X8,X9] :
      ( sK11(X8,X9,X10) = k1_mcart_1(X10)
      | ~ r2_hidden(X10,k2_zfmisc_1(X8,X9)) ) ),
    inference(superposition,[],[f25,f48])).

% (21144)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f48,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK11(X0,X1,X8),sK12(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK11(X0,X1,X8),sK12(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK8(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( sK8(X0,X1,X2) = k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2))
              & r2_hidden(sK10(X0,X1,X2),X1)
              & r2_hidden(sK9(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK11(X0,X1,X8),sK12(X0,X1,X8)) = X8
                & r2_hidden(sK12(X0,X1,X8),X1)
                & r2_hidden(sK11(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11,sK12])],[f15,f18,f17,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK8(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK8(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK8(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK8(X0,X1,X2) = k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2))
        & r2_hidden(sK10(X0,X1,X2),X1)
        & r2_hidden(sK9(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK11(X0,X1,X8),sK12(X0,X1,X8)) = X8
        & r2_hidden(sK12(X0,X1,X8),X1)
        & r2_hidden(sK11(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f50,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK11(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK11(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f123,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl13_1 ),
    inference(resolution,[],[f121,f53])).

fof(f53,plain,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl13_1
  <=> r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f136,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK1),k2_zfmisc_1(X1,sK5))
    | spl13_3 ),
    inference(resolution,[],[f62,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X3,X2)) ) ),
    inference(superposition,[],[f89,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6])).

fof(f89,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(k2_mcart_1(X5),X4)
      | ~ r2_hidden(X5,k2_zfmisc_1(X3,X4)) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(k2_mcart_1(X5),X4)
      | ~ r2_hidden(X5,k2_zfmisc_1(X3,X4))
      | ~ r2_hidden(X5,k2_zfmisc_1(X3,X4)) ) ),
    inference(superposition,[],[f49,f85])).

fof(f85,plain,(
    ! [X6,X7,X5] :
      ( sK12(X5,X6,X7) = k2_mcart_1(X7)
      | ~ r2_hidden(X7,k2_zfmisc_1(X5,X6)) ) ),
    inference(superposition,[],[f26,f48])).

fof(f49,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK12(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK12(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,
    ( ~ r2_hidden(sK1,sK5)
    | spl13_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl13_3
  <=> r2_hidden(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f134,plain,
    ( ~ spl13_1
    | spl13_4 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl13_1
    | spl13_4 ),
    inference(resolution,[],[f130,f123])).

fof(f130,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK2),k2_zfmisc_1(X1,sK6))
    | spl13_4 ),
    inference(resolution,[],[f66,f91])).

fof(f66,plain,
    ( ~ r2_hidden(sK2,sK6)
    | spl13_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl13_4
  <=> r2_hidden(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f129,plain,
    ( ~ spl13_1
    | spl13_2 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl13_1
    | spl13_2 ),
    inference(subsumption_resolution,[],[f127,f58])).

fof(f58,plain,
    ( ~ r2_hidden(sK0,sK4)
    | spl13_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl13_2
  <=> r2_hidden(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f127,plain,
    ( r2_hidden(sK0,sK4)
    | ~ spl13_1 ),
    inference(resolution,[],[f126,f121])).

fof(f96,plain,
    ( ~ spl13_1
    | spl13_5 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl13_1
    | spl13_5 ),
    inference(resolution,[],[f92,f53])).

fof(f92,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK3),k2_zfmisc_1(X1,sK7))
    | spl13_5 ),
    inference(resolution,[],[f91,f70])).

fof(f70,plain,
    ( ~ r2_hidden(sK3,sK7)
    | spl13_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl13_5
  <=> r2_hidden(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f83,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f81,f57])).

fof(f57,plain,
    ( r2_hidden(sK0,sK4)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f81,plain,
    ( ~ r2_hidden(sK0,sK4)
    | spl13_1
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f80,f61])).

fof(f61,plain,
    ( r2_hidden(sK1,sK5)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f80,plain,
    ( ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | spl13_1
    | ~ spl13_4
    | ~ spl13_5 ),
    inference(resolution,[],[f79,f47])).

fof(f47,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | spl13_1
    | ~ spl13_4
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f78,f65])).

fof(f65,plain,
    ( r2_hidden(sK2,sK6)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f78,plain,
    ( ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | spl13_1
    | ~ spl13_5 ),
    inference(resolution,[],[f77,f47])).

fof(f77,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl13_1
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f76,f69])).

fof(f69,plain,
    ( r2_hidden(sK3,sK7)
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f76,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl13_1 ),
    inference(resolution,[],[f47,f54])).

fof(f54,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f75,plain,
    ( spl13_1
    | spl13_2 ),
    inference(avatar_split_clause,[],[f45,f56,f52])).

fof(f45,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f20,f39,f40])).

% (21139)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (21144)Refutation not found, incomplete strategy% (21144)------------------------------
% (21144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f40,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f37,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f38,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f20,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ~ r2_hidden(sK3,sK7)
      | ~ r2_hidden(sK2,sK6)
      | ~ r2_hidden(sK1,sK5)
      | ~ r2_hidden(sK0,sK4)
      | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
    & ( ( r2_hidden(sK3,sK7)
        & r2_hidden(sK2,sK6)
        & r2_hidden(sK1,sK5)
        & r2_hidden(sK0,sK4) )
      | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( ~ r2_hidden(X3,X7)
          | ~ r2_hidden(X2,X6)
          | ~ r2_hidden(X1,X5)
          | ~ r2_hidden(X0,X4)
          | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
        & ( ( r2_hidden(X3,X7)
            & r2_hidden(X2,X6)
            & r2_hidden(X1,X5)
            & r2_hidden(X0,X4) )
          | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) )
   => ( ( ~ r2_hidden(sK3,sK7)
        | ~ r2_hidden(sK2,sK6)
        | ~ r2_hidden(sK1,sK5)
        | ~ r2_hidden(sK0,sK4)
        | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
      & ( ( r2_hidden(sK3,sK7)
          & r2_hidden(sK2,sK6)
          & r2_hidden(sK1,sK5)
          & r2_hidden(sK0,sK4) )
        | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( ~ r2_hidden(X3,X7)
        | ~ r2_hidden(X2,X6)
        | ~ r2_hidden(X1,X5)
        | ~ r2_hidden(X0,X4)
        | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
      & ( ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) )
        | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( ~ r2_hidden(X3,X7)
        | ~ r2_hidden(X2,X6)
        | ~ r2_hidden(X1,X5)
        | ~ r2_hidden(X0,X4)
        | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
      & ( ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) )
        | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <~> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      <=> ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <=> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_mcart_1)).

fof(f74,plain,
    ( spl13_1
    | spl13_3 ),
    inference(avatar_split_clause,[],[f44,f60,f52])).

fof(f44,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f21,f39,f40])).

fof(f21,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,
    ( spl13_1
    | spl13_4 ),
    inference(avatar_split_clause,[],[f43,f64,f52])).

fof(f43,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f22,f39,f40])).

fof(f22,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,
    ( spl13_1
    | spl13_5 ),
    inference(avatar_split_clause,[],[f42,f68,f52])).

fof(f42,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f23,f39,f40])).

fof(f23,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,
    ( ~ spl13_1
    | ~ spl13_2
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_5 ),
    inference(avatar_split_clause,[],[f41,f68,f64,f60,f56,f52])).

fof(f41,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f24,f39,f40])).

fof(f24,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n021.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:34:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (21137)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (21145)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (21133)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (21153)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (21129)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (21128)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (21150)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (21142)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (21127)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (21132)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (21149)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (21130)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (21131)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (21135)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (21134)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (21130)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (21152)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (21151)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (21141)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (21156)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (21147)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.55  % (21143)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.48/0.55  % (21149)Refutation not found, incomplete strategy% (21149)------------------------------
% 1.48/0.55  % (21149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (21149)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (21149)Memory used [KB]: 10746
% 1.48/0.55  % (21149)Time elapsed: 0.140 s
% 1.48/0.55  % (21149)------------------------------
% 1.48/0.55  % (21149)------------------------------
% 1.48/0.55  % (21140)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.55  % (21136)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.48/0.55  % SZS output start Proof for theBenchmark
% 1.48/0.55  fof(f142,plain,(
% 1.48/0.55    $false),
% 1.48/0.55    inference(avatar_sat_refutation,[],[f71,f72,f73,f74,f75,f83,f96,f129,f134,f140])).
% 1.48/0.55  fof(f140,plain,(
% 1.48/0.55    ~spl13_1 | spl13_3),
% 1.48/0.55    inference(avatar_contradiction_clause,[],[f138])).
% 1.48/0.55  fof(f138,plain,(
% 1.48/0.55    $false | (~spl13_1 | spl13_3)),
% 1.48/0.55    inference(resolution,[],[f136,f126])).
% 1.48/0.55  fof(f126,plain,(
% 1.48/0.55    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | ~spl13_1),
% 1.48/0.55    inference(resolution,[],[f123,f121])).
% 1.48/0.55  fof(f121,plain,(
% 1.48/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.48/0.55    inference(superposition,[],[f119,f25])).
% 1.48/0.55  fof(f25,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.48/0.55    inference(cnf_transformation,[],[f6])).
% 1.48/0.55  fof(f6,axiom,(
% 1.48/0.55    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.48/0.55  fof(f119,plain,(
% 1.48/0.55    ( ! [X4,X5,X3] : (r2_hidden(k1_mcart_1(X5),X3) | ~r2_hidden(X5,k2_zfmisc_1(X3,X4))) )),
% 1.48/0.55    inference(duplicate_literal_removal,[],[f118])).
% 1.48/0.55  fof(f118,plain,(
% 1.48/0.55    ( ! [X4,X5,X3] : (r2_hidden(k1_mcart_1(X5),X3) | ~r2_hidden(X5,k2_zfmisc_1(X3,X4)) | ~r2_hidden(X5,k2_zfmisc_1(X3,X4))) )),
% 1.48/0.55    inference(superposition,[],[f50,f86])).
% 1.48/0.55  fof(f86,plain,(
% 1.48/0.55    ( ! [X10,X8,X9] : (sK11(X8,X9,X10) = k1_mcart_1(X10) | ~r2_hidden(X10,k2_zfmisc_1(X8,X9))) )),
% 1.48/0.55    inference(superposition,[],[f25,f48])).
% 1.48/0.55  % (21144)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.48/0.55  fof(f48,plain,(
% 1.48/0.55    ( ! [X0,X8,X1] : (k4_tarski(sK11(X0,X1,X8),sK12(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.48/0.55    inference(equality_resolution,[],[f31])).
% 1.48/0.55  fof(f31,plain,(
% 1.48/0.55    ( ! [X2,X0,X8,X1] : (k4_tarski(sK11(X0,X1,X8),sK12(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.48/0.55    inference(cnf_transformation,[],[f19])).
% 1.48/0.55  fof(f19,plain,(
% 1.48/0.55    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK8(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((sK8(X0,X1,X2) = k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)) & r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK11(X0,X1,X8),sK12(X0,X1,X8)) = X8 & r2_hidden(sK12(X0,X1,X8),X1) & r2_hidden(sK11(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.48/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11,sK12])],[f15,f18,f17,f16])).
% 1.48/0.55  fof(f16,plain,(
% 1.48/0.55    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK8(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK8(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f17,plain,(
% 1.48/0.55    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK8(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK8(X0,X1,X2) = k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)) & r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f18,plain,(
% 1.48/0.55    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK11(X0,X1,X8),sK12(X0,X1,X8)) = X8 & r2_hidden(sK12(X0,X1,X8),X1) & r2_hidden(sK11(X0,X1,X8),X0)))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f15,plain,(
% 1.48/0.55    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.48/0.55    inference(rectify,[],[f14])).
% 1.48/0.55  fof(f14,plain,(
% 1.48/0.55    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.48/0.55    inference(nnf_transformation,[],[f1])).
% 1.48/0.55  fof(f1,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.48/0.55  fof(f50,plain,(
% 1.48/0.55    ( ! [X0,X8,X1] : (r2_hidden(sK11(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.48/0.55    inference(equality_resolution,[],[f29])).
% 1.48/0.55  fof(f29,plain,(
% 1.48/0.55    ( ! [X2,X0,X8,X1] : (r2_hidden(sK11(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.48/0.55    inference(cnf_transformation,[],[f19])).
% 1.48/0.55  fof(f123,plain,(
% 1.48/0.55    r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~spl13_1),
% 1.48/0.55    inference(resolution,[],[f121,f53])).
% 1.48/0.55  fof(f53,plain,(
% 1.48/0.55    r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | ~spl13_1),
% 1.48/0.55    inference(avatar_component_clause,[],[f52])).
% 1.48/0.55  fof(f52,plain,(
% 1.48/0.55    spl13_1 <=> r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.48/0.55  fof(f136,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK1),k2_zfmisc_1(X1,sK5))) ) | spl13_3),
% 1.48/0.55    inference(resolution,[],[f62,f91])).
% 1.48/0.55  fof(f91,plain,(
% 1.48/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X3,X2))) )),
% 1.48/0.55    inference(superposition,[],[f89,f26])).
% 1.48/0.55  fof(f26,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.48/0.55    inference(cnf_transformation,[],[f6])).
% 1.48/0.55  fof(f89,plain,(
% 1.48/0.55    ( ! [X4,X5,X3] : (r2_hidden(k2_mcart_1(X5),X4) | ~r2_hidden(X5,k2_zfmisc_1(X3,X4))) )),
% 1.48/0.55    inference(duplicate_literal_removal,[],[f88])).
% 1.48/0.55  fof(f88,plain,(
% 1.48/0.55    ( ! [X4,X5,X3] : (r2_hidden(k2_mcart_1(X5),X4) | ~r2_hidden(X5,k2_zfmisc_1(X3,X4)) | ~r2_hidden(X5,k2_zfmisc_1(X3,X4))) )),
% 1.48/0.55    inference(superposition,[],[f49,f85])).
% 1.48/0.55  fof(f85,plain,(
% 1.48/0.55    ( ! [X6,X7,X5] : (sK12(X5,X6,X7) = k2_mcart_1(X7) | ~r2_hidden(X7,k2_zfmisc_1(X5,X6))) )),
% 1.48/0.55    inference(superposition,[],[f26,f48])).
% 1.48/0.55  fof(f49,plain,(
% 1.48/0.55    ( ! [X0,X8,X1] : (r2_hidden(sK12(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.48/0.55    inference(equality_resolution,[],[f30])).
% 1.48/0.55  fof(f30,plain,(
% 1.48/0.55    ( ! [X2,X0,X8,X1] : (r2_hidden(sK12(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.48/0.55    inference(cnf_transformation,[],[f19])).
% 1.48/0.55  fof(f62,plain,(
% 1.48/0.55    ~r2_hidden(sK1,sK5) | spl13_3),
% 1.48/0.55    inference(avatar_component_clause,[],[f60])).
% 1.48/0.55  fof(f60,plain,(
% 1.48/0.55    spl13_3 <=> r2_hidden(sK1,sK5)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 1.48/0.55  fof(f134,plain,(
% 1.48/0.55    ~spl13_1 | spl13_4),
% 1.48/0.55    inference(avatar_contradiction_clause,[],[f132])).
% 1.48/0.55  fof(f132,plain,(
% 1.48/0.55    $false | (~spl13_1 | spl13_4)),
% 1.48/0.55    inference(resolution,[],[f130,f123])).
% 1.48/0.55  fof(f130,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK2),k2_zfmisc_1(X1,sK6))) ) | spl13_4),
% 1.48/0.55    inference(resolution,[],[f66,f91])).
% 1.48/0.55  fof(f66,plain,(
% 1.48/0.55    ~r2_hidden(sK2,sK6) | spl13_4),
% 1.48/0.55    inference(avatar_component_clause,[],[f64])).
% 1.48/0.55  fof(f64,plain,(
% 1.48/0.55    spl13_4 <=> r2_hidden(sK2,sK6)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 1.48/0.55  fof(f129,plain,(
% 1.48/0.55    ~spl13_1 | spl13_2),
% 1.48/0.55    inference(avatar_contradiction_clause,[],[f128])).
% 1.48/0.55  fof(f128,plain,(
% 1.48/0.55    $false | (~spl13_1 | spl13_2)),
% 1.48/0.55    inference(subsumption_resolution,[],[f127,f58])).
% 1.48/0.55  fof(f58,plain,(
% 1.48/0.55    ~r2_hidden(sK0,sK4) | spl13_2),
% 1.48/0.55    inference(avatar_component_clause,[],[f56])).
% 1.48/0.55  fof(f56,plain,(
% 1.48/0.55    spl13_2 <=> r2_hidden(sK0,sK4)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.48/0.55  fof(f127,plain,(
% 1.48/0.55    r2_hidden(sK0,sK4) | ~spl13_1),
% 1.48/0.55    inference(resolution,[],[f126,f121])).
% 1.48/0.55  fof(f96,plain,(
% 1.48/0.55    ~spl13_1 | spl13_5),
% 1.48/0.55    inference(avatar_contradiction_clause,[],[f94])).
% 1.48/0.55  fof(f94,plain,(
% 1.48/0.55    $false | (~spl13_1 | spl13_5)),
% 1.48/0.55    inference(resolution,[],[f92,f53])).
% 1.48/0.55  fof(f92,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK3),k2_zfmisc_1(X1,sK7))) ) | spl13_5),
% 1.48/0.55    inference(resolution,[],[f91,f70])).
% 1.48/0.55  fof(f70,plain,(
% 1.48/0.55    ~r2_hidden(sK3,sK7) | spl13_5),
% 1.48/0.55    inference(avatar_component_clause,[],[f68])).
% 1.48/0.55  fof(f68,plain,(
% 1.48/0.55    spl13_5 <=> r2_hidden(sK3,sK7)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 1.48/0.55  fof(f83,plain,(
% 1.48/0.55    spl13_1 | ~spl13_2 | ~spl13_3 | ~spl13_4 | ~spl13_5),
% 1.48/0.55    inference(avatar_contradiction_clause,[],[f82])).
% 1.48/0.55  fof(f82,plain,(
% 1.48/0.55    $false | (spl13_1 | ~spl13_2 | ~spl13_3 | ~spl13_4 | ~spl13_5)),
% 1.48/0.55    inference(subsumption_resolution,[],[f81,f57])).
% 1.48/0.55  fof(f57,plain,(
% 1.48/0.55    r2_hidden(sK0,sK4) | ~spl13_2),
% 1.48/0.55    inference(avatar_component_clause,[],[f56])).
% 1.48/0.55  fof(f81,plain,(
% 1.48/0.55    ~r2_hidden(sK0,sK4) | (spl13_1 | ~spl13_3 | ~spl13_4 | ~spl13_5)),
% 1.48/0.55    inference(subsumption_resolution,[],[f80,f61])).
% 1.48/0.55  fof(f61,plain,(
% 1.48/0.55    r2_hidden(sK1,sK5) | ~spl13_3),
% 1.48/0.55    inference(avatar_component_clause,[],[f60])).
% 1.48/0.55  fof(f80,plain,(
% 1.48/0.55    ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | (spl13_1 | ~spl13_4 | ~spl13_5)),
% 1.48/0.55    inference(resolution,[],[f79,f47])).
% 1.48/0.55  fof(f47,plain,(
% 1.48/0.55    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 1.48/0.55    inference(equality_resolution,[],[f46])).
% 1.48/0.55  fof(f46,plain,(
% 1.48/0.55    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.48/0.55    inference(equality_resolution,[],[f32])).
% 1.48/0.55  fof(f32,plain,(
% 1.48/0.55    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.48/0.55    inference(cnf_transformation,[],[f19])).
% 1.48/0.55  fof(f79,plain,(
% 1.48/0.55    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | (spl13_1 | ~spl13_4 | ~spl13_5)),
% 1.48/0.55    inference(subsumption_resolution,[],[f78,f65])).
% 1.48/0.55  fof(f65,plain,(
% 1.48/0.55    r2_hidden(sK2,sK6) | ~spl13_4),
% 1.48/0.55    inference(avatar_component_clause,[],[f64])).
% 1.48/0.55  fof(f78,plain,(
% 1.48/0.55    ~r2_hidden(sK2,sK6) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | (spl13_1 | ~spl13_5)),
% 1.48/0.55    inference(resolution,[],[f77,f47])).
% 1.48/0.55  fof(f77,plain,(
% 1.48/0.55    ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | (spl13_1 | ~spl13_5)),
% 1.48/0.55    inference(subsumption_resolution,[],[f76,f69])).
% 1.48/0.55  fof(f69,plain,(
% 1.48/0.55    r2_hidden(sK3,sK7) | ~spl13_5),
% 1.48/0.55    inference(avatar_component_clause,[],[f68])).
% 1.48/0.55  fof(f76,plain,(
% 1.48/0.55    ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | spl13_1),
% 1.48/0.55    inference(resolution,[],[f47,f54])).
% 1.48/0.55  fof(f54,plain,(
% 1.48/0.55    ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | spl13_1),
% 1.48/0.55    inference(avatar_component_clause,[],[f52])).
% 1.48/0.55  fof(f75,plain,(
% 1.48/0.55    spl13_1 | spl13_2),
% 1.48/0.55    inference(avatar_split_clause,[],[f45,f56,f52])).
% 1.48/0.55  fof(f45,plain,(
% 1.48/0.55    r2_hidden(sK0,sK4) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.48/0.55    inference(definition_unfolding,[],[f20,f39,f40])).
% 1.48/0.55  % (21139)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.55  % (21144)Refutation not found, incomplete strategy% (21144)------------------------------
% 1.48/0.55  % (21144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  fof(f40,plain,(
% 1.48/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.48/0.55    inference(definition_unfolding,[],[f37,f27])).
% 1.48/0.55  fof(f27,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f3])).
% 1.48/0.55  fof(f3,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.48/0.55  fof(f37,plain,(
% 1.48/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f5])).
% 1.48/0.55  fof(f5,axiom,(
% 1.48/0.55    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.48/0.55  fof(f39,plain,(
% 1.48/0.55    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 1.48/0.55    inference(definition_unfolding,[],[f38,f28])).
% 1.48/0.55  fof(f28,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f2])).
% 1.48/0.55  fof(f2,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.48/0.55  fof(f38,plain,(
% 1.48/0.55    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f4])).
% 1.48/0.55  fof(f4,axiom,(
% 1.48/0.55    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 1.48/0.55  fof(f20,plain,(
% 1.48/0.55    r2_hidden(sK0,sK4) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.48/0.55    inference(cnf_transformation,[],[f13])).
% 1.48/0.55  fof(f13,plain,(
% 1.48/0.55    (~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))) & ((r2_hidden(sK3,sK7) & r2_hidden(sK2,sK6) & r2_hidden(sK1,sK5) & r2_hidden(sK0,sK4)) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)))),
% 1.48/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f11,f12])).
% 1.48/0.55  fof(f12,plain,(
% 1.48/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)))) => ((~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))) & ((r2_hidden(sK3,sK7) & r2_hidden(sK2,sK6) & r2_hidden(sK1,sK5) & r2_hidden(sK0,sK4)) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f11,plain,(
% 1.48/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))))),
% 1.48/0.55    inference(flattening,[],[f10])).
% 1.48/0.55  fof(f10,plain,(
% 1.48/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4)) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))))),
% 1.48/0.55    inference(nnf_transformation,[],[f9])).
% 1.48/0.55  fof(f9,plain,(
% 1.48/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <~> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 1.48/0.55    inference(ennf_transformation,[],[f8])).
% 1.48/0.55  fof(f8,negated_conjecture,(
% 1.48/0.55    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 1.48/0.55    inference(negated_conjecture,[],[f7])).
% 1.48/0.55  fof(f7,conjecture,(
% 1.48/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_mcart_1)).
% 1.48/0.55  fof(f74,plain,(
% 1.48/0.55    spl13_1 | spl13_3),
% 1.48/0.55    inference(avatar_split_clause,[],[f44,f60,f52])).
% 1.48/0.55  fof(f44,plain,(
% 1.48/0.55    r2_hidden(sK1,sK5) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.48/0.55    inference(definition_unfolding,[],[f21,f39,f40])).
% 1.48/0.55  fof(f21,plain,(
% 1.48/0.55    r2_hidden(sK1,sK5) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.48/0.55    inference(cnf_transformation,[],[f13])).
% 1.48/0.55  fof(f73,plain,(
% 1.48/0.55    spl13_1 | spl13_4),
% 1.48/0.55    inference(avatar_split_clause,[],[f43,f64,f52])).
% 1.48/0.55  fof(f43,plain,(
% 1.48/0.55    r2_hidden(sK2,sK6) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.48/0.55    inference(definition_unfolding,[],[f22,f39,f40])).
% 1.48/0.55  fof(f22,plain,(
% 1.48/0.55    r2_hidden(sK2,sK6) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.48/0.55    inference(cnf_transformation,[],[f13])).
% 1.48/0.55  fof(f72,plain,(
% 1.48/0.55    spl13_1 | spl13_5),
% 1.48/0.55    inference(avatar_split_clause,[],[f42,f68,f52])).
% 1.48/0.55  fof(f42,plain,(
% 1.48/0.55    r2_hidden(sK3,sK7) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.48/0.55    inference(definition_unfolding,[],[f23,f39,f40])).
% 1.48/0.55  fof(f23,plain,(
% 1.48/0.55    r2_hidden(sK3,sK7) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.48/0.55    inference(cnf_transformation,[],[f13])).
% 1.48/0.55  fof(f71,plain,(
% 1.48/0.55    ~spl13_1 | ~spl13_2 | ~spl13_3 | ~spl13_4 | ~spl13_5),
% 1.48/0.55    inference(avatar_split_clause,[],[f41,f68,f64,f60,f56,f52])).
% 1.48/0.55  fof(f41,plain,(
% 1.48/0.55    ~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.48/0.55    inference(definition_unfolding,[],[f24,f39,f40])).
% 1.48/0.55  fof(f24,plain,(
% 1.48/0.55    ~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.48/0.55    inference(cnf_transformation,[],[f13])).
% 1.48/0.55  % SZS output end Proof for theBenchmark
% 1.48/0.55  % (21130)------------------------------
% 1.48/0.55  % (21130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (21130)Termination reason: Refutation
% 1.48/0.55  
% 1.48/0.55  % (21130)Memory used [KB]: 10746
% 1.48/0.55  % (21130)Time elapsed: 0.140 s
% 1.48/0.55  % (21130)------------------------------
% 1.48/0.55  % (21130)------------------------------
% 1.48/0.55  % (21126)Success in time 0.192 s
%------------------------------------------------------------------------------
