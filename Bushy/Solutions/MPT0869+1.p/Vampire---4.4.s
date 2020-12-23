%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t28_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:06 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 124 expanded)
%              Number of leaves         :   16 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :  147 ( 288 expanded)
%              Number of equality atoms :   69 ( 171 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f40,f52,f63,f67,f68,f77,f105,f107,f108,f117,f121])).

fof(f121,plain,
    ( spl6_3
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f119,f27])).

fof(f27,plain,
    ( sK2 != sK5
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl6_3
  <=> sK2 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f119,plain,
    ( sK2 = sK5
    | ~ spl6_10 ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != k4_tarski(k4_tarski(sK0,sK1),sK2)
        | sK5 = X3 )
    | ~ spl6_10 ),
    inference(superposition,[],[f13,f62])).

fof(f62,plain,
    ( k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK0,sK1),sK5)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl6_10
  <=> k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK0,sK1),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t28_mcart_1.p',t33_zfmisc_1)).

fof(f117,plain,
    ( ~ spl6_19
    | ~ spl6_4
    | spl6_15 ),
    inference(avatar_split_clause,[],[f110,f94,f29,f115])).

fof(f115,plain,
    ( spl6_19
  <=> sK1 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f29,plain,
    ( spl6_4
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f94,plain,
    ( spl6_15
  <=> sK4 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f110,plain,
    ( sK1 != sK5
    | ~ spl6_4
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f95,f30])).

fof(f30,plain,
    ( sK1 = sK4
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f95,plain,
    ( sK4 != sK5
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f94])).

fof(f108,plain,
    ( spl6_4
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f92,f75,f29])).

fof(f75,plain,
    ( spl6_12
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f92,plain,
    ( sK1 = sK4
    | ~ spl6_12 ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( k4_tarski(sK0,sK1) != k4_tarski(X0,X1)
        | sK4 = X1 )
    | ~ spl6_12 ),
    inference(superposition,[],[f13,f76])).

fof(f76,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK0,sK4)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f75])).

fof(f107,plain,
    ( spl6_5
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f92,f33])).

fof(f33,plain,
    ( sK1 != sK4
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl6_5
  <=> sK1 != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f105,plain,
    ( spl6_14
    | ~ spl6_17
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f91,f75,f61,f103,f97])).

fof(f97,plain,
    ( spl6_14
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f103,plain,
    ( spl6_17
  <=> k4_tarski(sK0,sK1) != k4_tarski(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f91,plain,
    ( k4_tarski(sK0,sK1) != k4_tarski(k4_tarski(sK0,sK1),sK2)
    | sK4 = sK5
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(superposition,[],[f85,f62])).

fof(f77,plain,
    ( spl6_12
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f70,f50,f35,f75])).

fof(f35,plain,
    ( spl6_6
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f50,plain,
    ( spl6_8
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f70,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK0,sK4)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f36,f51])).

fof(f51,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK3,sK4)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f50])).

fof(f36,plain,
    ( sK0 = sK3
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f35])).

fof(f68,plain,
    ( spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f65,f50,f35])).

fof(f65,plain,
    ( sK0 = sK3
    | ~ spl6_8 ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( k4_tarski(sK0,sK1) != k4_tarski(X0,X1)
        | sK3 = X0 )
    | ~ spl6_8 ),
    inference(superposition,[],[f12,f51])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,
    ( spl6_7
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f65,f39])).

fof(f39,plain,
    ( sK0 != sK3
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl6_7
  <=> sK0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f63,plain,
    ( spl6_10
    | ~ spl6_0
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f54,f50,f19,f61])).

fof(f19,plain,
    ( spl6_0
  <=> k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f54,plain,
    ( k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK0,sK1),sK5)
    | ~ spl6_0
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f51,f20])).

fof(f20,plain,
    ( k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK3,sK4),sK5)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f19])).

fof(f52,plain,
    ( spl6_8
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f45,f19,f50])).

fof(f45,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK3,sK4)
    | ~ spl6_0 ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( k4_tarski(X0,X1) != k4_tarski(k4_tarski(sK0,sK1),sK2)
        | k4_tarski(sK3,sK4) = X0 )
    | ~ spl6_0 ),
    inference(superposition,[],[f12,f20])).

fof(f40,plain,
    ( ~ spl6_3
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f9,f38,f32,f26])).

fof(f9,plain,
    ( sK0 != sK3
    | sK1 != sK4
    | sK2 != sK5 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
       => ( X2 = X5
          & X1 = X4
          & X0 = X3 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t28_mcart_1.p',t28_mcart_1)).

fof(f21,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f14,f19])).

fof(f14,plain,(
    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f10,f11,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t28_mcart_1.p',d3_mcart_1)).

fof(f10,plain,(
    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
