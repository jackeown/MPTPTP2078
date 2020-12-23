%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:51 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 162 expanded)
%              Number of leaves         :   15 (  55 expanded)
%              Depth                    :   22
%              Number of atoms          :  298 ( 571 expanded)
%              Number of equality atoms :   54 ( 130 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f142,f145,f158,f161,f164,f168,f180,f183,f186])).

fof(f186,plain,
    ( ~ spl14_2
    | spl14_10 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl14_2
    | spl14_10 ),
    inference(unit_resulting_resolution,[],[f123,f179,f11])).

fof(f11,plain,(
    ! [X5] :
      ( r2_hidden(sK7(X5),sK3)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k4_zfmisc_1(X1,X2,X3,X4) != X0
      & ! [X5] :
          ( r2_hidden(X5,X0)
        <=> ? [X6,X7,X8,X9] :
              ( k4_mcart_1(X6,X7,X8,X9) = X5
              & r2_hidden(X9,X4)
              & r2_hidden(X8,X3)
              & r2_hidden(X7,X2)
              & r2_hidden(X6,X1) ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ! [X5] :
            ( r2_hidden(X5,X0)
          <=> ? [X6,X7,X8,X9] :
                ( k4_mcart_1(X6,X7,X8,X9) = X5
                & r2_hidden(X9,X4)
                & r2_hidden(X8,X3)
                & r2_hidden(X7,X2)
                & r2_hidden(X6,X1) ) )
       => k4_zfmisc_1(X1,X2,X3,X4) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5] :
          ( r2_hidden(X5,X0)
        <=> ? [X6,X7,X8,X9] :
              ( k4_mcart_1(X6,X7,X8,X9) = X5
              & r2_hidden(X9,X4)
              & r2_hidden(X8,X3)
              & r2_hidden(X7,X2)
              & r2_hidden(X6,X1) ) )
     => k4_zfmisc_1(X1,X2,X3,X4) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_mcart_1)).

fof(f179,plain,
    ( ~ r2_hidden(sK7(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK3)
    | spl14_10 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl14_10
  <=> r2_hidden(sK7(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f123,plain,
    ( r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK0)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl14_2
  <=> r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f183,plain,
    ( ~ spl14_2
    | spl14_9 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl14_2
    | spl14_9 ),
    inference(unit_resulting_resolution,[],[f123,f175,f12])).

fof(f12,plain,(
    ! [X5] :
      ( r2_hidden(sK8(X5),sK4)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f175,plain,
    ( ~ r2_hidden(sK8(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK4)
    | spl14_9 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl14_9
  <=> r2_hidden(sK8(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f180,plain,
    ( ~ spl14_9
    | ~ spl14_2
    | ~ spl14_10
    | ~ spl14_4
    | ~ spl14_8 ),
    inference(avatar_split_clause,[],[f171,f166,f132,f177,f121,f173])).

fof(f132,plain,
    ( spl14_4
  <=> r2_hidden(k4_tarski(sK5(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK6(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f166,plain,
    ( spl14_8
  <=> ! [X0] :
        ( sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0) != X0
        | ~ r2_hidden(k4_tarski(sK5(X0),sK6(X0)),k2_zfmisc_1(sK1,sK2))
        | ~ r2_hidden(sK7(X0),sK3)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK8(X0),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f171,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK6(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),k2_zfmisc_1(sK1,sK2))
    | ~ r2_hidden(sK7(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK3)
    | ~ r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK0)
    | ~ r2_hidden(sK8(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK4)
    | ~ spl14_8 ),
    inference(equality_resolution,[],[f167])).

fof(f167,plain,
    ( ! [X0] :
        ( sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0) != X0
        | ~ r2_hidden(k4_tarski(sK5(X0),sK6(X0)),k2_zfmisc_1(sK1,sK2))
        | ~ r2_hidden(sK7(X0),sK3)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK8(X0),sK4) )
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f166])).

fof(f168,plain,
    ( spl14_1
    | spl14_8
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f146,f121,f166,f40])).

fof(f40,plain,
    ( spl14_1
  <=> sK0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f146,plain,
    ( ! [X0] :
        ( sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0) != X0
        | ~ r2_hidden(sK8(X0),sK4)
        | sK0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK7(X0),sK3)
        | ~ r2_hidden(k4_tarski(sK5(X0),sK6(X0)),k2_zfmisc_1(sK1,sK2)) )
    | ~ spl14_2 ),
    inference(resolution,[],[f123,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK9(k2_zfmisc_1(X2,X3),X1,X4),X4)
      | sK9(k2_zfmisc_1(X2,X3),X1,X4) != X0
      | ~ r2_hidden(sK8(X0),X1)
      | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1) = X4
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK7(X0),X3)
      | ~ r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X2) ) ),
    inference(resolution,[],[f44,f35])).

fof(f35,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(k4_tarski(sK5(X0),sK6(X0)),sK7(X0)),X1)
      | ~ r2_hidden(sK8(X0),X2)
      | sK9(X1,X2,X3) != X0
      | ~ r2_hidden(sK9(X1,X2,X3),X3)
      | k2_zfmisc_1(X1,X2) = X3
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f18,f32])).

fof(f32,plain,(
    ! [X5] :
      ( k4_tarski(k4_tarski(k4_tarski(sK5(X5),sK6(X5)),sK7(X5)),sK8(X5)) = X5
      | ~ r2_hidden(X5,sK0) ) ),
    inference(definition_unfolding,[],[f13,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f26,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f13,plain,(
    ! [X5] :
      ( k4_mcart_1(sK5(X5),sK6(X5),sK7(X5),sK8(X5)) = X5
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( k4_tarski(X4,X5) != sK9(X0,X1,X2)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(sK9(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f164,plain,
    ( ~ spl14_2
    | spl14_7 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl14_2
    | spl14_7 ),
    inference(unit_resulting_resolution,[],[f123,f157,f10])).

fof(f10,plain,(
    ! [X5] :
      ( r2_hidden(sK6(X5),sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f157,plain,
    ( ~ r2_hidden(sK6(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK2)
    | spl14_7 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl14_7
  <=> r2_hidden(sK6(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f161,plain,
    ( ~ spl14_2
    | spl14_6 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl14_2
    | spl14_6 ),
    inference(unit_resulting_resolution,[],[f123,f153,f9])).

fof(f9,plain,(
    ! [X5] :
      ( r2_hidden(sK5(X5),sK1)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f153,plain,
    ( ~ r2_hidden(sK5(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK1)
    | spl14_6 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl14_6
  <=> r2_hidden(sK5(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f158,plain,
    ( ~ spl14_6
    | ~ spl14_7
    | spl14_4 ),
    inference(avatar_split_clause,[],[f147,f132,f155,f151])).

fof(f147,plain,
    ( ~ r2_hidden(sK6(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK2)
    | ~ r2_hidden(sK5(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK1)
    | spl14_4 ),
    inference(resolution,[],[f134,f35])).

fof(f134,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK6(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),k2_zfmisc_1(sK1,sK2))
    | spl14_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f145,plain,
    ( spl14_1
    | spl14_2
    | spl14_5 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl14_1
    | spl14_2
    | spl14_5 ),
    inference(unit_resulting_resolution,[],[f42,f122,f141,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK13(X0,X1,X2),X1)
      | r2_hidden(sK9(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f141,plain,
    ( ~ r2_hidden(sK13(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK4)
    | spl14_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl14_5
  <=> r2_hidden(sK13(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f122,plain,
    ( ~ r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK0)
    | spl14_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f42,plain,
    ( sK0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f142,plain,
    ( spl14_1
    | ~ spl14_5
    | spl14_2 ),
    inference(avatar_split_clause,[],[f136,f121,f139,f40])).

fof(f136,plain,
    ( ~ r2_hidden(sK13(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK4)
    | sK0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)
    | spl14_2 ),
    inference(resolution,[],[f122,f105])).

fof(f105,plain,(
    ! [X0] :
      ( r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,sK0),sK0)
      | ~ r2_hidden(sK13(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,sK0),sK4)
      | sK0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0) ) ),
    inference(factoring,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),sK0)
      | ~ r2_hidden(sK13(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),sK4)
      | r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),X1)
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),sK0)
      | ~ r2_hidden(sK13(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),sK4)
      | r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),X1)
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0) = X1
      | r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),X1)
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0) = X1 ) ),
    inference(superposition,[],[f78,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( sK9(X0,X1,X2) = k4_tarski(sK12(X0,X1,X2),sK13(X0,X1,X2))
      | r2_hidden(sK9(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f78,plain,(
    ! [X12,X13,X11] :
      ( r2_hidden(k4_tarski(sK12(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X12,X13),X11),sK0)
      | ~ r2_hidden(X11,sK4)
      | r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X12,X13),X13)
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X12) = X13 ) ),
    inference(resolution,[],[f73,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK12(X0,X1,X2),X0)
      | r2_hidden(sK9(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
      | ~ r2_hidden(X1,sK4)
      | r2_hidden(k4_tarski(X0,X1),sK0) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ) ),
    inference(resolution,[],[f71,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK11(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK11(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),X2,X1),sK3)
      | r2_hidden(k4_tarski(X1,X0),sK0)
      | ~ r2_hidden(X0,sK4)
      | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X2)) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK4)
      | r2_hidden(k4_tarski(X1,X0),sK0)
      | ~ r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),X2,X1),sK3)
      | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X2))
      | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X2)) ) ),
    inference(resolution,[],[f69,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK10(X0,X1,X2),k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X3,sK4)
      | r2_hidden(k4_tarski(X2,X3),sK0)
      | ~ r2_hidden(sK11(X0,X1,X2),sK3)
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK11(X0,X1,X2),sK3)
      | ~ r2_hidden(X3,sK4)
      | r2_hidden(k4_tarski(X2,X3),sK0)
      | ~ r2_hidden(sK10(X0,X1,X2),k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK10(X0,X1,X2),k2_zfmisc_1(sK1,sK2)) ) ),
    inference(resolution,[],[f67,f38])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK10(X4,sK2,sK10(X2,X3,X0)),sK1)
      | ~ r2_hidden(sK11(X2,X3,X0),sK3)
      | ~ r2_hidden(X1,sK4)
      | r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ r2_hidden(sK10(X2,X3,X0),k2_zfmisc_1(X4,sK2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ r2_hidden(sK11(X2,X3,X0),sK3)
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(sK10(X4,sK2,sK10(X2,X3,X0)),sK1)
      | ~ r2_hidden(sK10(X2,X3,X0),k2_zfmisc_1(X4,sK2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(sK10(X2,X3,X0),k2_zfmisc_1(X4,sK2)) ) ),
    inference(resolution,[],[f54,f37])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(sK11(X4,X5,sK10(X0,X1,X2)),sK2)
      | r2_hidden(k4_tarski(X2,X3),sK0)
      | ~ r2_hidden(sK11(X0,X1,X2),sK3)
      | ~ r2_hidden(X3,sK4)
      | ~ r2_hidden(sK10(X4,X5,sK10(X0,X1,X2)),sK1)
      | ~ r2_hidden(sK10(X0,X1,X2),k2_zfmisc_1(X4,X5))
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f46,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( k4_tarski(sK10(X0,X1,X3),sK11(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK10(X0,X1,X3),sK11(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(k4_tarski(X2,X3),X4),sK0)
      | ~ r2_hidden(sK11(X0,X1,X2),sK2)
      | ~ r2_hidden(X3,sK3)
      | ~ r2_hidden(X4,sK4)
      | ~ r2_hidden(sK10(X0,X1,X2),sK1)
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f33,f36])).

fof(f33,plain,(
    ! [X6,X8,X7,X9] :
      ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9),sK0)
      | ~ r2_hidden(X7,sK2)
      | ~ r2_hidden(X8,sK3)
      | ~ r2_hidden(X9,sK4)
      | ~ r2_hidden(X6,sK1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(X6,sK1)
      | ~ r2_hidden(X7,sK2)
      | ~ r2_hidden(X8,sK3)
      | ~ r2_hidden(X9,sK4)
      | k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) != X5
      | r2_hidden(X5,sK0) ) ),
    inference(definition_unfolding,[],[f14,f28])).

fof(f14,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(X6,sK1)
      | ~ r2_hidden(X7,sK2)
      | ~ r2_hidden(X8,sK3)
      | ~ r2_hidden(X9,sK4)
      | k4_mcart_1(X6,X7,X8,X9) != X5
      | r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,(
    ~ spl14_1 ),
    inference(avatar_split_clause,[],[f30,f40])).

fof(f30,plain,(
    sK0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4) ),
    inference(definition_unfolding,[],[f15,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f27,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f15,plain,(
    sK0 != k4_zfmisc_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:32:48 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (29723)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (29732)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (29748)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (29724)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.52  % (29731)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.30/0.53  % (29729)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.53  % (29746)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.30/0.53  % (29747)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.54  % (29745)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.54  % (29725)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.42/0.54  % (29727)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.42/0.54  % (29733)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.55  % (29737)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.42/0.55  % (29739)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.55  % (29749)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.55  % (29752)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.55  % (29726)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.42/0.56  % (29744)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.56  % (29741)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.56  % (29736)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.56  % (29750)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.57  % (29742)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.57  % (29728)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.42/0.57  % (29745)Refutation found. Thanks to Tanya!
% 1.42/0.57  % SZS status Theorem for theBenchmark
% 1.42/0.57  % SZS output start Proof for theBenchmark
% 1.42/0.57  fof(f187,plain,(
% 1.42/0.57    $false),
% 1.42/0.57    inference(avatar_sat_refutation,[],[f43,f142,f145,f158,f161,f164,f168,f180,f183,f186])).
% 1.42/0.57  fof(f186,plain,(
% 1.42/0.57    ~spl14_2 | spl14_10),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f184])).
% 1.42/0.57  fof(f184,plain,(
% 1.42/0.57    $false | (~spl14_2 | spl14_10)),
% 1.42/0.57    inference(unit_resulting_resolution,[],[f123,f179,f11])).
% 1.42/0.57  fof(f11,plain,(
% 1.42/0.57    ( ! [X5] : (r2_hidden(sK7(X5),sK3) | ~r2_hidden(X5,sK0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f8])).
% 1.42/0.57  fof(f8,plain,(
% 1.42/0.57    ? [X0,X1,X2,X3,X4] : (k4_zfmisc_1(X1,X2,X3,X4) != X0 & ! [X5] : (r2_hidden(X5,X0) <=> ? [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X5 & r2_hidden(X9,X4) & r2_hidden(X8,X3) & r2_hidden(X7,X2) & r2_hidden(X6,X1))))),
% 1.42/0.57    inference(ennf_transformation,[],[f7])).
% 1.42/0.57  fof(f7,negated_conjecture,(
% 1.42/0.57    ~! [X0,X1,X2,X3,X4] : (! [X5] : (r2_hidden(X5,X0) <=> ? [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X5 & r2_hidden(X9,X4) & r2_hidden(X8,X3) & r2_hidden(X7,X2) & r2_hidden(X6,X1))) => k4_zfmisc_1(X1,X2,X3,X4) = X0)),
% 1.42/0.57    inference(negated_conjecture,[],[f6])).
% 1.42/0.57  fof(f6,conjecture,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4] : (! [X5] : (r2_hidden(X5,X0) <=> ? [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X5 & r2_hidden(X9,X4) & r2_hidden(X8,X3) & r2_hidden(X7,X2) & r2_hidden(X6,X1))) => k4_zfmisc_1(X1,X2,X3,X4) = X0)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_mcart_1)).
% 1.42/0.57  fof(f179,plain,(
% 1.42/0.57    ~r2_hidden(sK7(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK3) | spl14_10),
% 1.42/0.57    inference(avatar_component_clause,[],[f177])).
% 1.42/0.57  fof(f177,plain,(
% 1.42/0.57    spl14_10 <=> r2_hidden(sK7(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK3)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).
% 1.42/0.57  fof(f123,plain,(
% 1.42/0.57    r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK0) | ~spl14_2),
% 1.42/0.57    inference(avatar_component_clause,[],[f121])).
% 1.42/0.57  fof(f121,plain,(
% 1.42/0.57    spl14_2 <=> r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK0)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 1.42/0.57  fof(f183,plain,(
% 1.42/0.57    ~spl14_2 | spl14_9),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f181])).
% 1.42/0.57  fof(f181,plain,(
% 1.42/0.57    $false | (~spl14_2 | spl14_9)),
% 1.42/0.57    inference(unit_resulting_resolution,[],[f123,f175,f12])).
% 1.42/0.57  fof(f12,plain,(
% 1.42/0.57    ( ! [X5] : (r2_hidden(sK8(X5),sK4) | ~r2_hidden(X5,sK0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f8])).
% 1.42/0.57  fof(f175,plain,(
% 1.42/0.57    ~r2_hidden(sK8(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK4) | spl14_9),
% 1.42/0.57    inference(avatar_component_clause,[],[f173])).
% 1.42/0.57  fof(f173,plain,(
% 1.42/0.57    spl14_9 <=> r2_hidden(sK8(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK4)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).
% 1.42/0.57  fof(f180,plain,(
% 1.42/0.57    ~spl14_9 | ~spl14_2 | ~spl14_10 | ~spl14_4 | ~spl14_8),
% 1.42/0.57    inference(avatar_split_clause,[],[f171,f166,f132,f177,f121,f173])).
% 1.42/0.57  fof(f132,plain,(
% 1.42/0.57    spl14_4 <=> r2_hidden(k4_tarski(sK5(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK6(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),k2_zfmisc_1(sK1,sK2))),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).
% 1.42/0.57  fof(f166,plain,(
% 1.42/0.57    spl14_8 <=> ! [X0] : (sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0) != X0 | ~r2_hidden(k4_tarski(sK5(X0),sK6(X0)),k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK7(X0),sK3) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK8(X0),sK4))),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).
% 1.42/0.57  fof(f171,plain,(
% 1.42/0.57    ~r2_hidden(k4_tarski(sK5(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK6(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK7(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK3) | ~r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK0) | ~r2_hidden(sK8(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK4) | ~spl14_8),
% 1.42/0.57    inference(equality_resolution,[],[f167])).
% 1.42/0.57  fof(f167,plain,(
% 1.42/0.57    ( ! [X0] : (sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0) != X0 | ~r2_hidden(k4_tarski(sK5(X0),sK6(X0)),k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK7(X0),sK3) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK8(X0),sK4)) ) | ~spl14_8),
% 1.42/0.57    inference(avatar_component_clause,[],[f166])).
% 1.42/0.57  fof(f168,plain,(
% 1.42/0.57    spl14_1 | spl14_8 | ~spl14_2),
% 1.42/0.57    inference(avatar_split_clause,[],[f146,f121,f166,f40])).
% 1.42/0.57  fof(f40,plain,(
% 1.42/0.57    spl14_1 <=> sK0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 1.42/0.57  fof(f146,plain,(
% 1.42/0.57    ( ! [X0] : (sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0) != X0 | ~r2_hidden(sK8(X0),sK4) | sK0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK7(X0),sK3) | ~r2_hidden(k4_tarski(sK5(X0),sK6(X0)),k2_zfmisc_1(sK1,sK2))) ) | ~spl14_2),
% 1.42/0.57    inference(resolution,[],[f123,f58])).
% 1.42/0.57  fof(f58,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(sK9(k2_zfmisc_1(X2,X3),X1,X4),X4) | sK9(k2_zfmisc_1(X2,X3),X1,X4) != X0 | ~r2_hidden(sK8(X0),X1) | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1) = X4 | ~r2_hidden(X0,sK0) | ~r2_hidden(sK7(X0),X3) | ~r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X2)) )),
% 1.42/0.57    inference(resolution,[],[f44,f35])).
% 1.42/0.57  fof(f35,plain,(
% 1.42/0.57    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 1.42/0.57    inference(equality_resolution,[],[f34])).
% 1.42/0.57  fof(f34,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.42/0.57    inference(equality_resolution,[],[f25])).
% 1.42/0.57  fof(f25,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.42/0.57    inference(cnf_transformation,[],[f1])).
% 1.42/0.57  fof(f1,axiom,(
% 1.42/0.57    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.42/0.57  fof(f44,plain,(
% 1.42/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(k4_tarski(sK5(X0),sK6(X0)),sK7(X0)),X1) | ~r2_hidden(sK8(X0),X2) | sK9(X1,X2,X3) != X0 | ~r2_hidden(sK9(X1,X2,X3),X3) | k2_zfmisc_1(X1,X2) = X3 | ~r2_hidden(X0,sK0)) )),
% 1.42/0.57    inference(superposition,[],[f18,f32])).
% 1.42/0.57  fof(f32,plain,(
% 1.42/0.57    ( ! [X5] : (k4_tarski(k4_tarski(k4_tarski(sK5(X5),sK6(X5)),sK7(X5)),sK8(X5)) = X5 | ~r2_hidden(X5,sK0)) )),
% 1.42/0.57    inference(definition_unfolding,[],[f13,f28])).
% 1.42/0.57  fof(f28,plain,(
% 1.42/0.57    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 1.42/0.57    inference(definition_unfolding,[],[f26,f16])).
% 1.42/0.57  fof(f16,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f2])).
% 1.42/0.57  fof(f2,axiom,(
% 1.42/0.57    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.42/0.57  fof(f26,plain,(
% 1.42/0.57    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f4])).
% 1.42/0.57  fof(f4,axiom,(
% 1.42/0.57    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 1.42/0.57  fof(f13,plain,(
% 1.42/0.57    ( ! [X5] : (k4_mcart_1(sK5(X5),sK6(X5),sK7(X5),sK8(X5)) = X5 | ~r2_hidden(X5,sK0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f8])).
% 1.42/0.57  fof(f18,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X5,X1] : (k4_tarski(X4,X5) != sK9(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0) | ~r2_hidden(sK9(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.42/0.57    inference(cnf_transformation,[],[f1])).
% 1.42/0.57  fof(f164,plain,(
% 1.42/0.57    ~spl14_2 | spl14_7),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f162])).
% 1.42/0.57  fof(f162,plain,(
% 1.42/0.57    $false | (~spl14_2 | spl14_7)),
% 1.42/0.57    inference(unit_resulting_resolution,[],[f123,f157,f10])).
% 1.42/0.57  fof(f10,plain,(
% 1.42/0.57    ( ! [X5] : (r2_hidden(sK6(X5),sK2) | ~r2_hidden(X5,sK0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f8])).
% 1.42/0.57  fof(f157,plain,(
% 1.42/0.57    ~r2_hidden(sK6(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK2) | spl14_7),
% 1.42/0.57    inference(avatar_component_clause,[],[f155])).
% 1.42/0.57  fof(f155,plain,(
% 1.42/0.57    spl14_7 <=> r2_hidden(sK6(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK2)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).
% 1.42/0.57  fof(f161,plain,(
% 1.42/0.57    ~spl14_2 | spl14_6),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f159])).
% 1.42/0.57  fof(f159,plain,(
% 1.42/0.57    $false | (~spl14_2 | spl14_6)),
% 1.42/0.57    inference(unit_resulting_resolution,[],[f123,f153,f9])).
% 1.42/0.57  fof(f9,plain,(
% 1.42/0.57    ( ! [X5] : (r2_hidden(sK5(X5),sK1) | ~r2_hidden(X5,sK0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f8])).
% 1.42/0.57  fof(f153,plain,(
% 1.42/0.57    ~r2_hidden(sK5(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK1) | spl14_6),
% 1.42/0.57    inference(avatar_component_clause,[],[f151])).
% 1.42/0.57  fof(f151,plain,(
% 1.42/0.57    spl14_6 <=> r2_hidden(sK5(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK1)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).
% 1.42/0.57  fof(f158,plain,(
% 1.42/0.57    ~spl14_6 | ~spl14_7 | spl14_4),
% 1.42/0.57    inference(avatar_split_clause,[],[f147,f132,f155,f151])).
% 1.42/0.57  fof(f147,plain,(
% 1.42/0.57    ~r2_hidden(sK6(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK2) | ~r2_hidden(sK5(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK1) | spl14_4),
% 1.42/0.57    inference(resolution,[],[f134,f35])).
% 1.42/0.57  fof(f134,plain,(
% 1.42/0.57    ~r2_hidden(k4_tarski(sK5(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK6(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),k2_zfmisc_1(sK1,sK2)) | spl14_4),
% 1.42/0.57    inference(avatar_component_clause,[],[f132])).
% 1.42/0.57  fof(f145,plain,(
% 1.42/0.57    spl14_1 | spl14_2 | spl14_5),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f143])).
% 1.42/0.57  fof(f143,plain,(
% 1.42/0.57    $false | (spl14_1 | spl14_2 | spl14_5)),
% 1.42/0.57    inference(unit_resulting_resolution,[],[f42,f122,f141,f20])).
% 1.42/0.57  fof(f20,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK13(X0,X1,X2),X1) | r2_hidden(sK9(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.42/0.57    inference(cnf_transformation,[],[f1])).
% 1.42/0.57  fof(f141,plain,(
% 1.42/0.57    ~r2_hidden(sK13(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK4) | spl14_5),
% 1.42/0.57    inference(avatar_component_clause,[],[f139])).
% 1.42/0.57  fof(f139,plain,(
% 1.42/0.57    spl14_5 <=> r2_hidden(sK13(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK4)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).
% 1.42/0.57  fof(f122,plain,(
% 1.42/0.57    ~r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK0) | spl14_2),
% 1.42/0.57    inference(avatar_component_clause,[],[f121])).
% 1.42/0.57  fof(f42,plain,(
% 1.42/0.57    sK0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4) | spl14_1),
% 1.42/0.57    inference(avatar_component_clause,[],[f40])).
% 1.42/0.57  fof(f142,plain,(
% 1.42/0.57    spl14_1 | ~spl14_5 | spl14_2),
% 1.42/0.57    inference(avatar_split_clause,[],[f136,f121,f139,f40])).
% 1.42/0.57  fof(f136,plain,(
% 1.42/0.57    ~r2_hidden(sK13(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK4) | sK0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4) | spl14_2),
% 1.42/0.57    inference(resolution,[],[f122,f105])).
% 1.42/0.57  fof(f105,plain,(
% 1.42/0.57    ( ! [X0] : (r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,sK0),sK0) | ~r2_hidden(sK13(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,sK0),sK4) | sK0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0)) )),
% 1.42/0.57    inference(factoring,[],[f102])).
% 1.42/0.57  fof(f102,plain,(
% 1.42/0.57    ( ! [X0,X1] : (r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),sK0) | ~r2_hidden(sK13(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),sK4) | r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),X1) | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0) = X1) )),
% 1.42/0.57    inference(duplicate_literal_removal,[],[f101])).
% 1.42/0.57  fof(f101,plain,(
% 1.42/0.57    ( ! [X0,X1] : (r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),sK0) | ~r2_hidden(sK13(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),sK4) | r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),X1) | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0) = X1 | r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0,X1),X1) | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X0) = X1) )),
% 1.42/0.57    inference(superposition,[],[f78,f21])).
% 1.42/0.57  fof(f21,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (sK9(X0,X1,X2) = k4_tarski(sK12(X0,X1,X2),sK13(X0,X1,X2)) | r2_hidden(sK9(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.42/0.57    inference(cnf_transformation,[],[f1])).
% 1.42/0.57  fof(f78,plain,(
% 1.42/0.57    ( ! [X12,X13,X11] : (r2_hidden(k4_tarski(sK12(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X12,X13),X11),sK0) | ~r2_hidden(X11,sK4) | r2_hidden(sK9(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X12,X13),X13) | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),X12) = X13) )),
% 1.42/0.57    inference(resolution,[],[f73,f19])).
% 1.42/0.57  fof(f19,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK12(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.42/0.57    inference(cnf_transformation,[],[f1])).
% 1.42/0.57  fof(f73,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X1,sK4) | r2_hidden(k4_tarski(X0,X1),sK0)) )),
% 1.42/0.57    inference(duplicate_literal_removal,[],[f72])).
% 1.42/0.57  fof(f72,plain,(
% 1.42/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(X1,sK4) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) )),
% 1.42/0.57    inference(resolution,[],[f71,f37])).
% 1.42/0.57  fof(f37,plain,(
% 1.42/0.57    ( ! [X0,X3,X1] : (r2_hidden(sK11(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.42/0.57    inference(equality_resolution,[],[f23])).
% 1.42/0.57  fof(f23,plain,(
% 1.42/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(sK11(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.42/0.57    inference(cnf_transformation,[],[f1])).
% 1.42/0.57  fof(f71,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),X2,X1),sK3) | r2_hidden(k4_tarski(X1,X0),sK0) | ~r2_hidden(X0,sK4) | ~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X2))) )),
% 1.42/0.57    inference(duplicate_literal_removal,[],[f70])).
% 1.42/0.57  fof(f70,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK4) | r2_hidden(k4_tarski(X1,X0),sK0) | ~r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),X2,X1),sK3) | ~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X2)) | ~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X2))) )),
% 1.42/0.57    inference(resolution,[],[f69,f38])).
% 1.42/0.57  fof(f38,plain,(
% 1.42/0.57    ( ! [X0,X3,X1] : (r2_hidden(sK10(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.42/0.57    inference(equality_resolution,[],[f22])).
% 1.42/0.57  fof(f22,plain,(
% 1.42/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(sK10(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.42/0.57    inference(cnf_transformation,[],[f1])).
% 1.42/0.57  fof(f69,plain,(
% 1.42/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK10(X0,X1,X2),k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X3,sK4) | r2_hidden(k4_tarski(X2,X3),sK0) | ~r2_hidden(sK11(X0,X1,X2),sK3) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 1.42/0.57    inference(duplicate_literal_removal,[],[f68])).
% 1.42/0.57  fof(f68,plain,(
% 1.42/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK11(X0,X1,X2),sK3) | ~r2_hidden(X3,sK4) | r2_hidden(k4_tarski(X2,X3),sK0) | ~r2_hidden(sK10(X0,X1,X2),k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK10(X0,X1,X2),k2_zfmisc_1(sK1,sK2))) )),
% 1.42/0.57    inference(resolution,[],[f67,f38])).
% 1.42/0.57  fof(f67,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(sK10(X4,sK2,sK10(X2,X3,X0)),sK1) | ~r2_hidden(sK11(X2,X3,X0),sK3) | ~r2_hidden(X1,sK4) | r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(sK10(X2,X3,X0),k2_zfmisc_1(X4,sK2)) | ~r2_hidden(X0,k2_zfmisc_1(X2,X3))) )),
% 1.42/0.57    inference(duplicate_literal_removal,[],[f66])).
% 1.42/0.57  fof(f66,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(sK11(X2,X3,X0),sK3) | ~r2_hidden(X1,sK4) | ~r2_hidden(sK10(X4,sK2,sK10(X2,X3,X0)),sK1) | ~r2_hidden(sK10(X2,X3,X0),k2_zfmisc_1(X4,sK2)) | ~r2_hidden(X0,k2_zfmisc_1(X2,X3)) | ~r2_hidden(sK10(X2,X3,X0),k2_zfmisc_1(X4,sK2))) )),
% 1.42/0.57    inference(resolution,[],[f54,f37])).
% 1.42/0.57  fof(f54,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(sK11(X4,X5,sK10(X0,X1,X2)),sK2) | r2_hidden(k4_tarski(X2,X3),sK0) | ~r2_hidden(sK11(X0,X1,X2),sK3) | ~r2_hidden(X3,sK4) | ~r2_hidden(sK10(X4,X5,sK10(X0,X1,X2)),sK1) | ~r2_hidden(sK10(X0,X1,X2),k2_zfmisc_1(X4,X5)) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 1.42/0.57    inference(superposition,[],[f46,f36])).
% 1.42/0.57  fof(f36,plain,(
% 1.42/0.57    ( ! [X0,X3,X1] : (k4_tarski(sK10(X0,X1,X3),sK11(X0,X1,X3)) = X3 | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.42/0.57    inference(equality_resolution,[],[f24])).
% 1.42/0.57  fof(f24,plain,(
% 1.42/0.57    ( ! [X2,X0,X3,X1] : (k4_tarski(sK10(X0,X1,X3),sK11(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.42/0.57    inference(cnf_transformation,[],[f1])).
% 1.42/0.57  fof(f46,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(k4_tarski(X2,X3),X4),sK0) | ~r2_hidden(sK11(X0,X1,X2),sK2) | ~r2_hidden(X3,sK3) | ~r2_hidden(X4,sK4) | ~r2_hidden(sK10(X0,X1,X2),sK1) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 1.42/0.57    inference(superposition,[],[f33,f36])).
% 1.42/0.57  fof(f33,plain,(
% 1.42/0.57    ( ! [X6,X8,X7,X9] : (r2_hidden(k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9),sK0) | ~r2_hidden(X7,sK2) | ~r2_hidden(X8,sK3) | ~r2_hidden(X9,sK4) | ~r2_hidden(X6,sK1)) )),
% 1.42/0.57    inference(equality_resolution,[],[f31])).
% 1.42/0.57  fof(f31,plain,(
% 1.42/0.57    ( ! [X6,X8,X7,X5,X9] : (~r2_hidden(X6,sK1) | ~r2_hidden(X7,sK2) | ~r2_hidden(X8,sK3) | ~r2_hidden(X9,sK4) | k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) != X5 | r2_hidden(X5,sK0)) )),
% 1.42/0.57    inference(definition_unfolding,[],[f14,f28])).
% 1.42/0.57  fof(f14,plain,(
% 1.42/0.57    ( ! [X6,X8,X7,X5,X9] : (~r2_hidden(X6,sK1) | ~r2_hidden(X7,sK2) | ~r2_hidden(X8,sK3) | ~r2_hidden(X9,sK4) | k4_mcart_1(X6,X7,X8,X9) != X5 | r2_hidden(X5,sK0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f8])).
% 1.42/0.57  fof(f43,plain,(
% 1.42/0.57    ~spl14_1),
% 1.42/0.57    inference(avatar_split_clause,[],[f30,f40])).
% 1.42/0.57  fof(f30,plain,(
% 1.42/0.57    sK0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)),
% 1.42/0.57    inference(definition_unfolding,[],[f15,f29])).
% 1.42/0.57  fof(f29,plain,(
% 1.42/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.42/0.57    inference(definition_unfolding,[],[f27,f17])).
% 1.42/0.57  fof(f17,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f3])).
% 1.42/0.57  fof(f3,axiom,(
% 1.42/0.57    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.42/0.57  fof(f27,plain,(
% 1.42/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f5])).
% 1.42/0.57  fof(f5,axiom,(
% 1.42/0.57    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.42/0.57  fof(f15,plain,(
% 1.42/0.57    sK0 != k4_zfmisc_1(sK1,sK2,sK3,sK4)),
% 1.42/0.57    inference(cnf_transformation,[],[f8])).
% 1.42/0.57  % SZS output end Proof for theBenchmark
% 1.42/0.57  % (29745)------------------------------
% 1.42/0.57  % (29745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (29745)Termination reason: Refutation
% 1.42/0.57  
% 1.42/0.57  % (29745)Memory used [KB]: 11129
% 1.42/0.57  % (29745)Time elapsed: 0.150 s
% 1.42/0.57  % (29745)------------------------------
% 1.42/0.57  % (29745)------------------------------
% 1.42/0.57  % (29735)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.57  % (29734)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.57  % (29738)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.57  % (29730)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.58  % (29751)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.58  % (29740)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.58  % (29743)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.42/0.59  % (29740)Refutation not found, incomplete strategy% (29740)------------------------------
% 1.42/0.59  % (29740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.59  % (29740)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.59  
% 1.42/0.59  % (29740)Memory used [KB]: 10618
% 1.42/0.59  % (29740)Time elapsed: 0.157 s
% 1.42/0.59  % (29740)------------------------------
% 1.42/0.59  % (29740)------------------------------
% 1.42/0.59  % (29722)Success in time 0.23 s
%------------------------------------------------------------------------------
