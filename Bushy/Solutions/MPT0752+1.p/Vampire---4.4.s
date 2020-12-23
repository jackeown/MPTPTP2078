%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t45_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:27 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 137 expanded)
%              Number of leaves         :   25 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  190 ( 304 expanded)
%              Number of equality atoms :    8 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f80,f89,f96,f109,f121,f128,f135,f144,f151,f173,f204,f217])).

fof(f217,plain,
    ( ~ spl2_10
    | ~ spl2_20
    | spl2_23 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl2_10
    | ~ spl2_20
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f215,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t45_ordinal1.p',t2_xboole_1)).

fof(f215,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl2_10
    | ~ spl2_20
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f212,f172])).

fof(f172,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl2_20
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f212,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0)
    | ~ spl2_10
    | ~ spl2_23 ),
    inference(unit_resulting_resolution,[],[f203,f120,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t45_ordinal1.p',d19_relat_1)).

fof(f120,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl2_10
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f203,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl2_23
  <=> ~ v5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f204,plain,
    ( ~ spl2_11
    | ~ spl2_23
    | ~ spl2_15
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f46,f123,f130,f202,f116])).

fof(f116,plain,
    ( spl2_11
  <=> ~ v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f130,plain,
    ( spl2_15
  <=> ~ v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f123,plain,
    ( spl2_13
  <=> ~ v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f46,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ~ v5_ordinal1(k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
   => ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,sK0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v5_ordinal1(k1_xboole_0)
        & v1_funct_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X0)
        & v1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t45_ordinal1.p',t45_ordinal1)).

fof(f173,plain,
    ( spl2_20
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f155,f149,f171])).

fof(f149,plain,
    ( spl2_18
  <=> v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f155,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_18 ),
    inference(unit_resulting_resolution,[],[f150,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t45_ordinal1.p',t6_boole)).

fof(f150,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( spl2_18
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f136,f107,f149])).

fof(f107,plain,
    ( spl2_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f136,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f108,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t45_ordinal1.p',fc11_relat_1)).

fof(f108,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f144,plain,
    ( spl2_16
    | ~ spl2_0 ),
    inference(avatar_split_clause,[],[f97,f70,f142])).

fof(f142,plain,
    ( spl2_16
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f70,plain,
    ( spl2_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f97,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl2_0 ),
    inference(unit_resulting_resolution,[],[f71,f52])).

fof(f71,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl2_0 ),
    inference(avatar_component_clause,[],[f70])).

fof(f135,plain,
    ( spl2_14
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f101,f78,f70,f133])).

fof(f133,plain,
    ( spl2_14
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f78,plain,
    ( spl2_2
  <=> v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f101,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f97,f79])).

fof(f79,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f128,plain,
    ( spl2_12
    | ~ spl2_0
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f100,f87,f70,f126])).

fof(f126,plain,
    ( spl2_12
  <=> v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f87,plain,
    ( spl2_4
  <=> v5_ordinal1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f100,plain,
    ( v5_ordinal1(k1_xboole_0)
    | ~ spl2_0
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f97,f88])).

fof(f88,plain,
    ( v5_ordinal1(o_0_0_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f121,plain,
    ( spl2_10
    | ~ spl2_0
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f99,f94,f70,f119])).

fof(f94,plain,
    ( spl2_6
  <=> v1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f99,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_0
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f97,f95])).

fof(f95,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f109,plain,
    ( spl2_8
    | ~ spl2_0 ),
    inference(avatar_split_clause,[],[f102,f70,f107])).

fof(f102,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_0 ),
    inference(backward_demodulation,[],[f97,f71])).

fof(f96,plain,
    ( spl2_6
    | ~ spl2_0 ),
    inference(avatar_split_clause,[],[f82,f70,f94])).

fof(f82,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl2_0 ),
    inference(unit_resulting_resolution,[],[f71,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t45_ordinal1.p',cc1_relat_1)).

fof(f89,plain,
    ( spl2_4
    | ~ spl2_0 ),
    inference(avatar_split_clause,[],[f81,f70,f87])).

fof(f81,plain,
    ( v5_ordinal1(o_0_0_xboole_0)
    | ~ spl2_0 ),
    inference(unit_resulting_resolution,[],[f71,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v5_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t45_ordinal1.p',cc4_ordinal1)).

fof(f80,plain,
    ( spl2_2
    | ~ spl2_0 ),
    inference(avatar_split_clause,[],[f73,f70,f78])).

fof(f73,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl2_0 ),
    inference(unit_resulting_resolution,[],[f71,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t45_ordinal1.p',cc1_funct_1)).

fof(f72,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f47,f70])).

fof(f47,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t45_ordinal1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
