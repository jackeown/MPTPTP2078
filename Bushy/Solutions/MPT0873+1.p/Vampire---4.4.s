%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t33_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:06 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 132 expanded)
%              Number of leaves         :   16 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  170 ( 322 expanded)
%              Number of equality atoms :   88 ( 199 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f52,f64,f73,f83,f84,f93,f94,f103,f113,f114,f123,f135])).

fof(f135,plain,
    ( spl8_5
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f133,f39])).

fof(f39,plain,
    ( sK2 != sK6
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl8_5
  <=> sK2 != sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f133,plain,
    ( sK2 = sK6
    | ~ spl8_16 ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,
    ( ! [X2,X0,X1] :
        ( k3_mcart_1(sK0,sK1,sK2) != k3_mcart_1(X0,X1,X2)
        | sK6 = X2 )
    | ~ spl8_16 ),
    inference(superposition,[],[f19,f122])).

fof(f122,plain,
    ( k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK0,sK1,sK6)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl8_16
  <=> k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK0,sK1,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t33_mcart_1.p',t28_mcart_1)).

fof(f123,plain,
    ( spl8_16
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f116,f101,f41,f121])).

fof(f41,plain,
    ( spl8_6
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f101,plain,
    ( spl8_14
  <=> k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK0,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f116,plain,
    ( k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK0,sK1,sK6)
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(backward_demodulation,[],[f42,f102])).

fof(f102,plain,
    ( k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK0,sK5,sK6)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f42,plain,
    ( sK1 = sK5
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f41])).

fof(f114,plain,
    ( spl8_6
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f111,f101,f41])).

fof(f111,plain,
    ( sK1 = sK5
    | ~ spl8_14 ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,
    ( ! [X2,X0,X1] :
        ( k3_mcart_1(sK0,sK1,sK2) != k3_mcart_1(X0,X1,X2)
        | sK5 = X1 )
    | ~ spl8_14 ),
    inference(superposition,[],[f18,f102])).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f113,plain,
    ( spl8_7
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f111,f45])).

fof(f45,plain,
    ( sK1 != sK5
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl8_7
  <=> sK1 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f103,plain,
    ( spl8_14
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f96,f62,f47,f101])).

fof(f47,plain,
    ( spl8_8
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f62,plain,
    ( spl8_10
  <=> k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f96,plain,
    ( k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK0,sK5,sK6)
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f48,f63])).

fof(f63,plain,
    ( k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK4,sK5,sK6)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f62])).

fof(f48,plain,
    ( sK0 = sK4
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f47])).

fof(f94,plain,
    ( spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f91,f62,f47])).

fof(f91,plain,
    ( sK0 = sK4
    | ~ spl8_10 ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,
    ( ! [X2,X0,X1] :
        ( k3_mcart_1(sK0,sK1,sK2) != k3_mcart_1(X0,X1,X2)
        | sK4 = X0 )
    | ~ spl8_10 ),
    inference(superposition,[],[f17,f63])).

fof(f17,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f93,plain,
    ( spl8_9
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f91,f51])).

fof(f51,plain,
    ( sK0 != sK4
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl8_9
  <=> sK0 != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f84,plain,
    ( spl8_2
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f81,f71,f29])).

fof(f29,plain,
    ( spl8_2
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f71,plain,
    ( spl8_12
  <=> k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) = k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f81,plain,
    ( sK3 = sK7
    | ~ spl8_12 ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( k4_tarski(X0,X1) != k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3)
        | sK7 = X1 )
    | ~ spl8_12 ),
    inference(superposition,[],[f16,f72])).

fof(f72,plain,
    ( k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) = k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK7)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f71])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t33_mcart_1.p',t33_zfmisc_1)).

fof(f83,plain,
    ( spl8_3
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f81,f33])).

fof(f33,plain,
    ( sK3 != sK7
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl8_3
  <=> sK3 != sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f73,plain,
    ( spl8_12
    | ~ spl8_0
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f66,f62,f25,f71])).

fof(f25,plain,
    ( spl8_0
  <=> k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) = k4_tarski(k3_mcart_1(sK4,sK5,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f66,plain,
    ( k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) = k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK7)
    | ~ spl8_0
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f63,f26])).

fof(f26,plain,
    ( k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) = k4_tarski(k3_mcart_1(sK4,sK5,sK6),sK7)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f25])).

fof(f64,plain,
    ( spl8_10
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f57,f25,f62])).

fof(f57,plain,
    ( k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK4,sK5,sK6)
    | ~ spl8_0 ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( k4_tarski(X0,X1) != k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3)
        | k3_mcart_1(sK4,sK5,sK6) = X0 )
    | ~ spl8_0 ),
    inference(superposition,[],[f15,f26])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,
    ( ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f12,f50,f44,f38,f32])).

fof(f12,plain,
    ( sK0 != sK4
    | sK1 != sK5
    | sK2 != sK6
    | sK3 != sK7 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t33_mcart_1.p',t33_mcart_1)).

fof(f27,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f20,f25])).

fof(f20,plain,(
    k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) = k4_tarski(k3_mcart_1(sK4,sK5,sK6),sK7) ),
    inference(definition_unfolding,[],[f13,f14,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t33_mcart_1.p',d4_mcart_1)).

fof(f13,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
