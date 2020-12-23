%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 348 expanded)
%              Number of leaves         :   21 ( 101 expanded)
%              Depth                    :   17
%              Number of atoms          :  441 (1433 expanded)
%              Number of equality atoms :  132 ( 560 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f103,f104,f105,f106,f130,f135,f150,f152,f158])).

fof(f158,plain,
    ( ~ spl18_1
    | spl18_3 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl18_1
    | spl18_3 ),
    inference(subsumption_resolution,[],[f147,f93])).

% (22956)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f93,plain,
    ( ~ r2_hidden(sK2,sK6)
    | spl18_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl18_3
  <=> r2_hidden(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).

fof(f147,plain,
    ( r2_hidden(sK2,sK6)
    | ~ spl18_1 ),
    inference(forward_demodulation,[],[f145,f116])).

fof(f116,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k2_mcart_1(k4_tarski(X4,X5)) = X5 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X5
      | k2_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X5
      | k4_tarski(X4,X5) != X0
      | k2_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ( sK12(X0,X1) != X1
              & k4_tarski(sK11(X0,X1),sK12(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X3
          & k4_tarski(X2,X3) = X0 )
     => ( sK12(X0,X1) != X1
        & k4_tarski(sK11(X0,X1),sK12(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X3
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k2_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X5
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).

fof(f145,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK2)),sK6)
    | ~ spl18_1 ),
    inference(resolution,[],[f144,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f144,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK5,sK6))
    | ~ spl18_1 ),
    inference(forward_demodulation,[],[f142,f114])).

fof(f114,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k1_mcart_1(k4_tarski(X4,X5)) = X4 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK9(X0,X1) != X1
              & k4_tarski(sK9(X0,X1),sK10(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK9(X0,X1) != X1
        & k4_tarski(sK9(X0,X1),sK10(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X2
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k1_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X4
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).

fof(f142,plain,
    ( r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(sK1,sK2),sK3)),k2_zfmisc_1(sK5,sK6))
    | ~ spl18_1 ),
    inference(resolution,[],[f136,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f136,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
    | ~ spl18_1 ),
    inference(forward_demodulation,[],[f132,f114])).

fof(f132,plain,
    ( r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4)),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
    | ~ spl18_1 ),
    inference(resolution,[],[f84,f51])).

fof(f84,plain,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8))
    | ~ spl18_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl18_1
  <=> r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).

fof(f152,plain,
    ( ~ spl18_1
    | spl18_4 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl18_1
    | spl18_4 ),
    inference(subsumption_resolution,[],[f143,f97])).

fof(f97,plain,
    ( ~ r2_hidden(sK3,sK7)
    | spl18_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl18_4
  <=> r2_hidden(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f143,plain,
    ( r2_hidden(sK3,sK7)
    | ~ spl18_1 ),
    inference(forward_demodulation,[],[f141,f116])).

fof(f141,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(sK1,sK2),sK3)),sK7)
    | ~ spl18_1 ),
    inference(resolution,[],[f136,f52])).

fof(f150,plain,
    ( ~ spl18_1
    | spl18_2 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl18_1
    | spl18_2 ),
    inference(subsumption_resolution,[],[f148,f89])).

fof(f89,plain,
    ( ~ r2_hidden(sK1,sK5)
    | spl18_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl18_2
  <=> r2_hidden(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f148,plain,
    ( r2_hidden(sK1,sK5)
    | ~ spl18_1 ),
    inference(forward_demodulation,[],[f146,f114])).

fof(f146,plain,
    ( r2_hidden(k1_mcart_1(k4_tarski(sK1,sK2)),sK5)
    | ~ spl18_1 ),
    inference(resolution,[],[f144,f51])).

fof(f135,plain,
    ( ~ spl18_1
    | spl18_5 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl18_1
    | spl18_5 ),
    inference(subsumption_resolution,[],[f133,f101])).

fof(f101,plain,
    ( ~ r2_hidden(sK4,sK8)
    | spl18_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl18_5
  <=> r2_hidden(sK4,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).

fof(f133,plain,
    ( r2_hidden(sK4,sK8)
    | ~ spl18_1 ),
    inference(forward_demodulation,[],[f131,f116])).

fof(f131,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4)),sK8)
    | ~ spl18_1 ),
    inference(resolution,[],[f84,f52])).

fof(f130,plain,
    ( spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_5 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_5 ),
    inference(subsumption_resolution,[],[f128,f92])).

fof(f92,plain,
    ( r2_hidden(sK2,sK6)
    | ~ spl18_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f128,plain,
    ( ~ r2_hidden(sK2,sK6)
    | spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_5 ),
    inference(subsumption_resolution,[],[f127,f88])).

fof(f88,plain,
    ( r2_hidden(sK1,sK5)
    | ~ spl18_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f127,plain,
    ( ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK2,sK6)
    | spl18_1
    | ~ spl18_4
    | ~ spl18_5 ),
    inference(resolution,[],[f126,f118])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1))
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f80,f81])).

fof(f81,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f17])).

fof(f17,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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

fof(f80,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
      | r2_hidden(k4_tarski(X9,X10),X2) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK13(X0,X1,X2)
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(sK13(X0,X1,X2),X2) )
          & ( ( sK13(X0,X1,X2) = k4_tarski(sK14(X0,X1,X2),sK15(X0,X1,X2))
              & r2_hidden(sK15(X0,X1,X2),X0)
              & r2_hidden(sK14(X0,X1,X2),X1) )
            | r2_hidden(sK13(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ( k4_tarski(sK16(X0,X1,X8),sK17(X0,X1,X8)) = X8
                & r2_hidden(sK17(X0,X1,X8),X0)
                & r2_hidden(sK16(X0,X1,X8),X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15,sK16,sK17])],[f32,f35,f34,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X0)
                & r2_hidden(X6,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK13(X0,X1,X2)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X1) )
          | ~ r2_hidden(sK13(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK13(X0,X1,X2)
              & r2_hidden(X7,X0)
              & r2_hidden(X6,X1) )
          | r2_hidden(sK13(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK13(X0,X1,X2)
          & r2_hidden(X7,X0)
          & r2_hidden(X6,X1) )
     => ( sK13(X0,X1,X2) = k4_tarski(sK14(X0,X1,X2),sK15(X0,X1,X2))
        & r2_hidden(sK15(X0,X1,X2),X0)
        & r2_hidden(sK14(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X0)
          & r2_hidden(X11,X1) )
     => ( k4_tarski(sK16(X0,X1,X8),sK17(X0,X1,X8)) = X8
        & r2_hidden(sK17(X0,X1,X8),X0)
        & r2_hidden(sK16(X0,X1,X8),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X0)
                  | ~ r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X0)
                  & r2_hidden(X6,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X0)
                  & r2_hidden(X11,X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f126,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK5,sK6))
    | spl18_1
    | ~ spl18_4
    | ~ spl18_5 ),
    inference(subsumption_resolution,[],[f125,f96])).

fof(f96,plain,
    ( r2_hidden(sK3,sK7)
    | ~ spl18_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f125,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK5,sK6))
    | ~ r2_hidden(sK3,sK7)
    | spl18_1
    | ~ spl18_5 ),
    inference(resolution,[],[f122,f118])).

fof(f122,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
    | spl18_1
    | ~ spl18_5 ),
    inference(subsumption_resolution,[],[f119,f100])).

fof(f100,plain,
    ( r2_hidden(sK4,sK8)
    | ~ spl18_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f119,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
    | ~ r2_hidden(sK4,sK8)
    | spl18_1 ),
    inference(resolution,[],[f118,f85])).

fof(f85,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8))
    | spl18_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f106,plain,
    ( spl18_1
    | spl18_2 ),
    inference(avatar_split_clause,[],[f71,f87,f83])).

fof(f71,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(definition_unfolding,[],[f38,f66,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f63,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f64,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f38,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r2_hidden(sK4,sK8)
      | ~ r2_hidden(sK3,sK7)
      | ~ r2_hidden(sK2,sK6)
      | ~ r2_hidden(sK1,sK5)
      | ~ r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8)) )
    & ( ( r2_hidden(sK4,sK8)
        & r2_hidden(sK3,sK7)
        & r2_hidden(sK2,sK6)
        & r2_hidden(sK1,sK5) )
      | r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f20,f21])).

fof(f21,plain,
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
   => ( ( ~ r2_hidden(sK4,sK8)
        | ~ r2_hidden(sK3,sK7)
        | ~ r2_hidden(sK2,sK6)
        | ~ r2_hidden(sK1,sK5)
        | ~ r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8)) )
      & ( ( r2_hidden(sK4,sK8)
          & r2_hidden(sK3,sK7)
          & r2_hidden(sK2,sK6)
          & r2_hidden(sK1,sK5) )
        | r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <~> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      <=> ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <=> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_mcart_1)).

fof(f105,plain,
    ( spl18_1
    | spl18_3 ),
    inference(avatar_split_clause,[],[f70,f91,f83])).

fof(f70,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(definition_unfolding,[],[f39,f66,f65])).

fof(f39,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,
    ( spl18_1
    | spl18_4 ),
    inference(avatar_split_clause,[],[f69,f95,f83])).

fof(f69,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(definition_unfolding,[],[f40,f66,f65])).

fof(f40,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f22])).

fof(f103,plain,
    ( spl18_1
    | spl18_5 ),
    inference(avatar_split_clause,[],[f68,f99,f83])).

fof(f68,plain,
    ( r2_hidden(sK4,sK8)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(definition_unfolding,[],[f41,f66,f65])).

fof(f41,plain,
    ( r2_hidden(sK4,sK8)
    | r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f22])).

fof(f102,plain,
    ( ~ spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_5 ),
    inference(avatar_split_clause,[],[f67,f99,f95,f91,f87,f83])).

fof(f67,plain,
    ( ~ r2_hidden(sK4,sK8)
    | ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(definition_unfolding,[],[f42,f66,f65])).

fof(f42,plain,
    ( ~ r2_hidden(sK4,sK8)
    | ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:46:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.55  % (22953)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (22969)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (22970)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (22962)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.57  % (22953)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f159,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f102,f103,f104,f105,f106,f130,f135,f150,f152,f158])).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    ~spl18_1 | spl18_3),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f157])).
% 0.21/0.57  fof(f157,plain,(
% 0.21/0.57    $false | (~spl18_1 | spl18_3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f147,f93])).
% 0.21/0.57  % (22956)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    ~r2_hidden(sK2,sK6) | spl18_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f91])).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    spl18_3 <=> r2_hidden(sK2,sK6)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    r2_hidden(sK2,sK6) | ~spl18_1),
% 0.21/0.57    inference(forward_demodulation,[],[f145,f116])).
% 0.21/0.57  fof(f116,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.57    inference(equality_resolution,[],[f79])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X6,X4,X7,X5] : (k4_tarski(X4,X5) != k4_tarski(X6,X7) | k2_mcart_1(k4_tarski(X4,X5)) = X5) )),
% 0.21/0.57    inference(equality_resolution,[],[f78])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    ( ! [X6,X4,X7,X5,X1] : (X1 = X5 | k2_mcart_1(k4_tarski(X4,X5)) != X1 | k4_tarski(X4,X5) != k4_tarski(X6,X7)) )),
% 0.21/0.57    inference(equality_resolution,[],[f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X6,X4,X0,X7,X5,X1] : (X1 = X5 | k4_tarski(X4,X5) != X0 | k2_mcart_1(X0) != X1 | k4_tarski(X6,X7) != X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((k2_mcart_1(X0) = X1 | (sK12(X0,X1) != X1 & k4_tarski(sK11(X0,X1),sK12(X0,X1)) = X0)) & (! [X4,X5] : (X1 = X5 | k4_tarski(X4,X5) != X0) | k2_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f28,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X2,X3] : (X1 != X3 & k4_tarski(X2,X3) = X0) => (sK12(X0,X1) != X1 & k4_tarski(sK11(X0,X1),sK12(X0,X1)) = X0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((k2_mcart_1(X0) = X1 | ? [X2,X3] : (X1 != X3 & k4_tarski(X2,X3) = X0)) & (! [X4,X5] : (X1 = X5 | k4_tarski(X4,X5) != X0) | k2_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 0.21/0.57    inference(rectify,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : (! [X3] : ((k2_mcart_1(X0) = X3 | ? [X4,X5] : (X3 != X5 & k4_tarski(X4,X5) = X0)) & (! [X4,X5] : (X3 = X5 | k4_tarski(X4,X5) != X0) | k2_mcart_1(X0) != X3)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.57    inference(nnf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,plain,(
% 0.21/0.58    ! [X0] : (! [X3] : (k2_mcart_1(X0) = X3 <=> ! [X4,X5] : (X3 = X5 | k4_tarski(X4,X5) != X0)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,plain,(
% 0.21/0.58    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X3] : (k2_mcart_1(X0) = X3 <=> ! [X4,X5] : (k4_tarski(X4,X5) = X0 => X3 = X5)))),
% 0.21/0.58    inference(rectify,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X1] : (k2_mcart_1(X0) = X1 <=> ! [X2,X3] : (k4_tarski(X2,X3) = X0 => X1 = X3)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).
% 0.21/0.58  fof(f145,plain,(
% 0.21/0.58    r2_hidden(k2_mcart_1(k4_tarski(sK1,sK2)),sK6) | ~spl18_1),
% 0.21/0.58    inference(resolution,[],[f144,f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.58  fof(f144,plain,(
% 0.21/0.58    r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK5,sK6)) | ~spl18_1),
% 0.21/0.58    inference(forward_demodulation,[],[f142,f114])).
% 0.21/0.58  fof(f114,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.58    inference(equality_resolution,[],[f75])).
% 0.21/0.58  fof(f75,plain,(
% 0.21/0.58    ( ! [X6,X4,X7,X5] : (k4_tarski(X4,X5) != k4_tarski(X6,X7) | k1_mcart_1(k4_tarski(X4,X5)) = X4) )),
% 0.21/0.58    inference(equality_resolution,[],[f74])).
% 0.21/0.58  fof(f74,plain,(
% 0.21/0.58    ( ! [X6,X4,X7,X5,X1] : (X1 = X4 | k1_mcart_1(k4_tarski(X4,X5)) != X1 | k4_tarski(X4,X5) != k4_tarski(X6,X7)) )),
% 0.21/0.58    inference(equality_resolution,[],[f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ( ! [X6,X4,X0,X7,X5,X1] : (X1 = X4 | k4_tarski(X4,X5) != X0 | k1_mcart_1(X0) != X1 | k4_tarski(X6,X7) != X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | (sK9(X0,X1) != X1 & k4_tarski(sK9(X0,X1),sK10(X0,X1)) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f24,f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X1,X0] : (? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0) => (sK9(X0,X1) != X1 & k4_tarski(sK9(X0,X1),sK10(X0,X1)) = X0))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | ? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 0.21/0.58    inference(rectify,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0] : (! [X3] : ((k1_mcart_1(X0) = X3 | ? [X4,X5] : (X3 != X4 & k4_tarski(X4,X5) = X0)) & (! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X3)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.58    inference(nnf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,plain,(
% 0.21/0.58    ! [X0] : (! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,plain,(
% 0.21/0.58    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (k4_tarski(X4,X5) = X0 => X3 = X4)))),
% 0.21/0.58    inference(rectify,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X1] : (k1_mcart_1(X0) = X1 <=> ! [X2,X3] : (k4_tarski(X2,X3) = X0 => X1 = X2)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).
% 0.21/0.58  fof(f142,plain,(
% 0.21/0.58    r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(sK1,sK2),sK3)),k2_zfmisc_1(sK5,sK6)) | ~spl18_1),
% 0.21/0.58    inference(resolution,[],[f136,f51])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  fof(f136,plain,(
% 0.21/0.58    r2_hidden(k4_tarski(k4_tarski(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) | ~spl18_1),
% 0.21/0.58    inference(forward_demodulation,[],[f132,f114])).
% 0.21/0.58  fof(f132,plain,(
% 0.21/0.58    r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4)),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) | ~spl18_1),
% 0.21/0.58    inference(resolution,[],[f84,f51])).
% 0.21/0.58  fof(f84,plain,(
% 0.21/0.58    r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) | ~spl18_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f83])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    spl18_1 <=> r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).
% 0.21/0.58  fof(f152,plain,(
% 0.21/0.58    ~spl18_1 | spl18_4),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.58  fof(f151,plain,(
% 0.21/0.58    $false | (~spl18_1 | spl18_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f143,f97])).
% 0.21/0.58  fof(f97,plain,(
% 0.21/0.58    ~r2_hidden(sK3,sK7) | spl18_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f95])).
% 0.21/0.58  fof(f95,plain,(
% 0.21/0.58    spl18_4 <=> r2_hidden(sK3,sK7)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).
% 0.21/0.58  fof(f143,plain,(
% 0.21/0.58    r2_hidden(sK3,sK7) | ~spl18_1),
% 0.21/0.58    inference(forward_demodulation,[],[f141,f116])).
% 0.21/0.58  fof(f141,plain,(
% 0.21/0.58    r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(sK1,sK2),sK3)),sK7) | ~spl18_1),
% 0.21/0.58    inference(resolution,[],[f136,f52])).
% 0.21/0.58  fof(f150,plain,(
% 0.21/0.58    ~spl18_1 | spl18_2),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f149])).
% 0.21/0.58  fof(f149,plain,(
% 0.21/0.58    $false | (~spl18_1 | spl18_2)),
% 0.21/0.58    inference(subsumption_resolution,[],[f148,f89])).
% 0.21/0.58  fof(f89,plain,(
% 0.21/0.58    ~r2_hidden(sK1,sK5) | spl18_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f87])).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    spl18_2 <=> r2_hidden(sK1,sK5)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).
% 0.21/0.58  fof(f148,plain,(
% 0.21/0.58    r2_hidden(sK1,sK5) | ~spl18_1),
% 0.21/0.58    inference(forward_demodulation,[],[f146,f114])).
% 0.21/0.58  fof(f146,plain,(
% 0.21/0.58    r2_hidden(k1_mcart_1(k4_tarski(sK1,sK2)),sK5) | ~spl18_1),
% 0.21/0.58    inference(resolution,[],[f144,f51])).
% 0.21/0.58  fof(f135,plain,(
% 0.21/0.58    ~spl18_1 | spl18_5),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f134])).
% 0.21/0.58  fof(f134,plain,(
% 0.21/0.58    $false | (~spl18_1 | spl18_5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f133,f101])).
% 0.21/0.58  fof(f101,plain,(
% 0.21/0.58    ~r2_hidden(sK4,sK8) | spl18_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f99])).
% 0.21/0.58  fof(f99,plain,(
% 0.21/0.58    spl18_5 <=> r2_hidden(sK4,sK8)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).
% 0.21/0.58  fof(f133,plain,(
% 0.21/0.58    r2_hidden(sK4,sK8) | ~spl18_1),
% 0.21/0.58    inference(forward_demodulation,[],[f131,f116])).
% 0.21/0.58  fof(f131,plain,(
% 0.21/0.58    r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4)),sK8) | ~spl18_1),
% 0.21/0.58    inference(resolution,[],[f84,f52])).
% 0.21/0.58  fof(f130,plain,(
% 0.21/0.58    spl18_1 | ~spl18_2 | ~spl18_3 | ~spl18_4 | ~spl18_5),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f129])).
% 0.21/0.58  fof(f129,plain,(
% 0.21/0.58    $false | (spl18_1 | ~spl18_2 | ~spl18_3 | ~spl18_4 | ~spl18_5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f128,f92])).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    r2_hidden(sK2,sK6) | ~spl18_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f91])).
% 0.21/0.58  fof(f128,plain,(
% 0.21/0.58    ~r2_hidden(sK2,sK6) | (spl18_1 | ~spl18_2 | ~spl18_4 | ~spl18_5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f127,f88])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    r2_hidden(sK1,sK5) | ~spl18_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f87])).
% 0.21/0.58  fof(f127,plain,(
% 0.21/0.58    ~r2_hidden(sK1,sK5) | ~r2_hidden(sK2,sK6) | (spl18_1 | ~spl18_4 | ~spl18_5)),
% 0.21/0.58    inference(resolution,[],[f126,f118])).
% 0.21/0.58  fof(f118,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) | ~r2_hidden(X2,X3) | ~r2_hidden(X0,X1)) )),
% 0.21/0.58    inference(resolution,[],[f80,f81])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    ( ! [X0,X1] : (sP0(X1,X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.58    inference(equality_resolution,[],[f61])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.58    inference(nnf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.58    inference(definition_folding,[],[f1,f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    ( ! [X2,X0,X10,X1,X9] : (~sP0(X0,X1,X2) | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | r2_hidden(k4_tarski(X9,X10),X2)) )),
% 0.21/0.58    inference(equality_resolution,[],[f56])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | ~sP0(X0,X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4,X5] : (k4_tarski(X4,X5) != sK13(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK13(X0,X1,X2),X2)) & ((sK13(X0,X1,X2) = k4_tarski(sK14(X0,X1,X2),sK15(X0,X1,X2)) & r2_hidden(sK15(X0,X1,X2),X0) & r2_hidden(sK14(X0,X1,X2),X1)) | r2_hidden(sK13(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & ((k4_tarski(sK16(X0,X1,X8),sK17(X0,X1,X8)) = X8 & r2_hidden(sK17(X0,X1,X8),X0) & r2_hidden(sK16(X0,X1,X8),X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15,sK16,sK17])],[f32,f35,f34,f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK13(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK13(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK13(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(sK13(X0,X1,X2),X2))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK13(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) => (sK13(X0,X1,X2) = k4_tarski(sK14(X0,X1,X2),sK15(X0,X1,X2)) & r2_hidden(sK15(X0,X1,X2),X0) & r2_hidden(sK14(X0,X1,X2),X1)))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f35,plain,(
% 0.21/0.59    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) => (k4_tarski(sK16(X0,X1,X8),sK17(X0,X1,X8)) = X8 & r2_hidden(sK17(X0,X1,X8),X0) & r2_hidden(sK16(X0,X1,X8),X1)))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.59    inference(rectify,[],[f31])).
% 0.21/0.59  fof(f31,plain,(
% 0.21/0.59    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.59    inference(nnf_transformation,[],[f17])).
% 0.21/0.59  fof(f126,plain,(
% 0.21/0.59    ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK5,sK6)) | (spl18_1 | ~spl18_4 | ~spl18_5)),
% 0.21/0.59    inference(subsumption_resolution,[],[f125,f96])).
% 0.21/0.59  fof(f96,plain,(
% 0.21/0.59    r2_hidden(sK3,sK7) | ~spl18_4),
% 0.21/0.59    inference(avatar_component_clause,[],[f95])).
% 0.21/0.59  fof(f125,plain,(
% 0.21/0.59    ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK5,sK6)) | ~r2_hidden(sK3,sK7) | (spl18_1 | ~spl18_5)),
% 0.21/0.59    inference(resolution,[],[f122,f118])).
% 0.21/0.59  fof(f122,plain,(
% 0.21/0.59    ~r2_hidden(k4_tarski(k4_tarski(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) | (spl18_1 | ~spl18_5)),
% 0.21/0.59    inference(subsumption_resolution,[],[f119,f100])).
% 0.21/0.59  fof(f100,plain,(
% 0.21/0.59    r2_hidden(sK4,sK8) | ~spl18_5),
% 0.21/0.59    inference(avatar_component_clause,[],[f99])).
% 0.21/0.59  fof(f119,plain,(
% 0.21/0.59    ~r2_hidden(k4_tarski(k4_tarski(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) | ~r2_hidden(sK4,sK8) | spl18_1),
% 0.21/0.59    inference(resolution,[],[f118,f85])).
% 0.21/0.59  fof(f85,plain,(
% 0.21/0.59    ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) | spl18_1),
% 0.21/0.59    inference(avatar_component_clause,[],[f83])).
% 0.21/0.59  fof(f106,plain,(
% 0.21/0.59    spl18_1 | spl18_2),
% 0.21/0.59    inference(avatar_split_clause,[],[f71,f87,f83])).
% 0.21/0.59  fof(f71,plain,(
% 0.21/0.59    r2_hidden(sK1,sK5) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8))),
% 0.21/0.59    inference(definition_unfolding,[],[f38,f66,f65])).
% 0.21/0.59  fof(f65,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f63,f49])).
% 0.21/0.59  fof(f49,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,axiom,(
% 0.21/0.59    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.59  fof(f66,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f64,f50])).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.59  fof(f64,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f6])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    r2_hidden(sK1,sK5) | r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8))),
% 0.21/0.59    inference(cnf_transformation,[],[f22])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    (~r2_hidden(sK4,sK8) | ~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8))) & ((r2_hidden(sK4,sK8) & r2_hidden(sK3,sK7) & r2_hidden(sK2,sK6) & r2_hidden(sK1,sK5)) | r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8)))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f20,f21])).
% 0.21/0.59  fof(f21,plain,(
% 0.21/0.59    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)))) => ((~r2_hidden(sK4,sK8) | ~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8))) & ((r2_hidden(sK4,sK8) & r2_hidden(sK3,sK7) & r2_hidden(sK2,sK6) & r2_hidden(sK1,sK5)) | r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8))))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f20,plain,(
% 0.21/0.59    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))))),
% 0.21/0.59    inference(flattening,[],[f19])).
% 0.21/0.59  fof(f19,plain,(
% 0.21/0.59    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4)) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))))),
% 0.21/0.59    inference(nnf_transformation,[],[f13])).
% 0.21/0.59  fof(f13,plain,(
% 0.21/0.59    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <~> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 0.21/0.59    inference(ennf_transformation,[],[f10])).
% 0.21/0.59  fof(f10,negated_conjecture,(
% 0.21/0.59    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 0.21/0.59    inference(negated_conjecture,[],[f9])).
% 0.21/0.59  fof(f9,conjecture,(
% 0.21/0.59    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_mcart_1)).
% 0.21/0.59  fof(f105,plain,(
% 0.21/0.59    spl18_1 | spl18_3),
% 0.21/0.59    inference(avatar_split_clause,[],[f70,f91,f83])).
% 0.21/0.59  fof(f70,plain,(
% 0.21/0.59    r2_hidden(sK2,sK6) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8))),
% 0.21/0.59    inference(definition_unfolding,[],[f39,f66,f65])).
% 0.21/0.59  fof(f39,plain,(
% 0.21/0.59    r2_hidden(sK2,sK6) | r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8))),
% 0.21/0.59    inference(cnf_transformation,[],[f22])).
% 0.21/0.59  fof(f104,plain,(
% 0.21/0.59    spl18_1 | spl18_4),
% 0.21/0.59    inference(avatar_split_clause,[],[f69,f95,f83])).
% 0.21/0.59  fof(f69,plain,(
% 0.21/0.59    r2_hidden(sK3,sK7) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8))),
% 0.21/0.59    inference(definition_unfolding,[],[f40,f66,f65])).
% 0.21/0.59  fof(f40,plain,(
% 0.21/0.59    r2_hidden(sK3,sK7) | r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8))),
% 0.21/0.59    inference(cnf_transformation,[],[f22])).
% 0.21/0.59  fof(f103,plain,(
% 0.21/0.59    spl18_1 | spl18_5),
% 0.21/0.59    inference(avatar_split_clause,[],[f68,f99,f83])).
% 0.21/0.59  fof(f68,plain,(
% 0.21/0.59    r2_hidden(sK4,sK8) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8))),
% 0.21/0.59    inference(definition_unfolding,[],[f41,f66,f65])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    r2_hidden(sK4,sK8) | r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8))),
% 0.21/0.59    inference(cnf_transformation,[],[f22])).
% 0.21/0.59  fof(f102,plain,(
% 0.21/0.59    ~spl18_1 | ~spl18_2 | ~spl18_3 | ~spl18_4 | ~spl18_5),
% 0.21/0.59    inference(avatar_split_clause,[],[f67,f99,f95,f91,f87,f83])).
% 0.21/0.59  fof(f67,plain,(
% 0.21/0.59    ~r2_hidden(sK4,sK8) | ~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK1,sK2),sK3),sK4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8))),
% 0.21/0.59    inference(definition_unfolding,[],[f42,f66,f65])).
% 0.21/0.59  fof(f42,plain,(
% 0.21/0.59    ~r2_hidden(sK4,sK8) | ~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(k4_mcart_1(sK1,sK2,sK3,sK4),k4_zfmisc_1(sK5,sK6,sK7,sK8))),
% 0.21/0.59    inference(cnf_transformation,[],[f22])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (22953)------------------------------
% 0.21/0.59  % (22953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (22953)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (22953)Memory used [KB]: 10746
% 0.21/0.59  % (22953)Time elapsed: 0.129 s
% 0.21/0.59  % (22953)------------------------------
% 0.21/0.59  % (22953)------------------------------
% 0.21/0.59  % (22946)Success in time 0.227 s
%------------------------------------------------------------------------------
