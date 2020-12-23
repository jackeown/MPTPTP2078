%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t63_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:30 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 136 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  170 ( 306 expanded)
%              Number of equality atoms :   26 (  46 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f57,f64,f71,f81,f90,f100,f107,f146,f153,f168,f175,f182,f197])).

fof(f197,plain,
    ( ~ spl3_2
    | ~ spl3_16
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f189,f159])).

fof(f159,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0)
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f152,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t63_xboole_1.p',t3_xboole_1)).

fof(f152,plain,
    ( k3_xboole_0(sK0,sK2) != k1_xboole_0
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl3_19
  <=> k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f189,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(superposition,[],[f155,f145])).

fof(f145,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl3_16
  <=> k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f155,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK1,X0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f56,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t63_xboole_1.p',t26_xboole_1)).

fof(f56,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f182,plain,
    ( ~ spl3_25
    | spl3_15 ),
    inference(avatar_split_clause,[],[f127,f105,f180])).

fof(f180,plain,
    ( spl3_25
  <=> k3_xboole_0(sK2,sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f105,plain,
    ( spl3_15
  <=> ~ r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f127,plain,
    ( k3_xboole_0(sK2,sK0) != k1_xboole_0
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f106,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t63_xboole_1.p',d7_xboole_0)).

fof(f106,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f105])).

fof(f175,plain,
    ( spl3_22
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f122,f98,f173])).

fof(f173,plain,
    ( spl3_22
  <=> k3_xboole_0(sK2,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f98,plain,
    ( spl3_12
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f122,plain,
    ( k3_xboole_0(sK2,sK1) = k1_xboole_0
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f99,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f99,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f168,plain,
    ( ~ spl3_21
    | ~ spl3_8
    | spl3_19 ),
    inference(avatar_split_clause,[],[f161,f151,f79,f166])).

fof(f166,plain,
    ( spl3_21
  <=> ~ v1_xboole_0(k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f79,plain,
    ( spl3_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f161,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,sK2))
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f80,f152,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t63_xboole_1.p',t8_boole)).

fof(f80,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f153,plain,
    ( ~ spl3_19
    | spl3_7 ),
    inference(avatar_split_clause,[],[f126,f69,f151])).

fof(f69,plain,
    ( spl3_7
  <=> ~ r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f126,plain,
    ( k3_xboole_0(sK0,sK2) != k1_xboole_0
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f70,f41])).

fof(f70,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f146,plain,
    ( spl3_16
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f121,f62,f144])).

fof(f62,plain,
    ( spl3_4
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f121,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f63,f40])).

fof(f63,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f107,plain,
    ( ~ spl3_15
    | spl3_7 ),
    inference(avatar_split_clause,[],[f92,f69,f105])).

fof(f92,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f70,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t63_xboole_1.p',symmetry_r1_xboole_0)).

fof(f100,plain,
    ( spl3_12
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f91,f62,f98])).

fof(f91,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f63,f39])).

fof(f90,plain,
    ( spl3_10
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f72,f48,f88])).

fof(f88,plain,
    ( spl3_10
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f48,plain,
    ( spl3_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f72,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t63_xboole_1.p',t6_boole)).

fof(f49,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f48])).

fof(f81,plain,
    ( spl3_8
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f74,f48,f79])).

fof(f74,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_0 ),
    inference(backward_demodulation,[],[f72,f49])).

fof(f71,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t63_xboole_1.p',t63_xboole_1)).

fof(f64,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f31,f62])).

fof(f31,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f33,f48])).

fof(f33,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t63_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
