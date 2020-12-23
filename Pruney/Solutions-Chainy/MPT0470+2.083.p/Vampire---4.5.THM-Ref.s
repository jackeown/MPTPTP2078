%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 373 expanded)
%              Number of leaves         :   39 ( 159 expanded)
%              Depth                    :    9
%              Number of atoms          :  385 ( 885 expanded)
%              Number of equality atoms :   24 (  58 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f446,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f68,f84,f108,f113,f139,f144,f149,f161,f237,f282,f287,f292,f297,f302,f307,f312,f317,f322,f326,f329,f416,f422,f430,f438,f442,f445])).

fof(f445,plain,
    ( ~ spl1_11
    | ~ spl1_18
    | spl1_25 ),
    inference(avatar_contradiction_clause,[],[f444])).

fof(f444,plain,
    ( $false
    | ~ spl1_11
    | ~ spl1_18
    | spl1_25 ),
    inference(subsumption_resolution,[],[f443,f32])).

fof(f32,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f443,plain,
    ( ~ r1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)
    | ~ spl1_11
    | ~ spl1_18
    | spl1_25 ),
    inference(subsumption_resolution,[],[f440,f425])).

fof(f425,plain,
    ( ~ v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_11
    | spl1_25 ),
    inference(unit_resulting_resolution,[],[f143,f421,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f421,plain,
    ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | spl1_25 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl1_25
  <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).

fof(f143,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl1_11
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f440,plain,
    ( v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ r1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)
    | ~ spl1_18 ),
    inference(resolution,[],[f296,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f296,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl1_18
  <=> r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f442,plain,
    ( ~ spl1_11
    | ~ spl1_18
    | spl1_25 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | ~ spl1_11
    | ~ spl1_18
    | spl1_25 ),
    inference(subsumption_resolution,[],[f439,f425])).

fof(f439,plain,
    ( v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_18 ),
    inference(unit_resulting_resolution,[],[f32,f296,f39])).

fof(f438,plain,
    ( ~ spl1_27
    | spl1_25 ),
    inference(avatar_split_clause,[],[f423,f419,f435])).

fof(f435,plain,
    ( spl1_27
  <=> r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).

fof(f423,plain,
    ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | spl1_25 ),
    inference(unit_resulting_resolution,[],[f32,f421,f39])).

fof(f430,plain,
    ( spl1_26
    | ~ spl1_1
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f369,f77,f65,f52,f42,f427])).

fof(f427,plain,
    ( spl1_26
  <=> r1_tarski(k1_xboole_0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).

fof(f42,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f52,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f65,plain,
    ( spl1_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

% (20669)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f77,plain,
    ( spl1_6
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f369,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f331,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f331,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(backward_demodulation,[],[f97,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f97,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f44,f67,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f67,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f44,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f422,plain,
    ( ~ spl1_25
    | spl1_7 ),
    inference(avatar_split_clause,[],[f417,f81,f419])).

fof(f81,plain,
    ( spl1_7
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f417,plain,
    ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | spl1_7 ),
    inference(unit_resulting_resolution,[],[f83,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f83,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f416,plain,
    ( spl1_24
    | ~ spl1_1
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f372,f158,f77,f57,f42,f413])).

fof(f413,plain,
    ( spl1_24
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).

fof(f57,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f158,plain,
    ( spl1_13
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f372,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f371,f59])).

fof(f59,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f371,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f370,f78])).

fof(f370,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f337,f59])).

% (20666)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f337,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ spl1_1
    | ~ spl1_6
    | ~ spl1_13 ),
    inference(backward_demodulation,[],[f202,f78])).

fof(f202,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_1
    | ~ spl1_13 ),
    inference(unit_resulting_resolution,[],[f44,f160,f33])).

% (20669)Refutation not found, incomplete strategy% (20669)------------------------------
% (20669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20669)Termination reason: Refutation not found, incomplete strategy

% (20669)Memory used [KB]: 6140
% (20669)Time elapsed: 0.123 s
% (20669)------------------------------
% (20669)------------------------------
fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f160,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f329,plain,
    ( ~ spl1_17
    | spl1_21 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl1_17
    | spl1_21 ),
    inference(subsumption_resolution,[],[f327,f32])).

fof(f327,plain,
    ( ~ r1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl1_17
    | spl1_21 ),
    inference(subsumption_resolution,[],[f324,f311])).

fof(f311,plain,
    ( ~ v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | spl1_21 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl1_21
  <=> v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f324,plain,
    ( v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ r1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl1_17 ),
    inference(resolution,[],[f291,f39])).

fof(f291,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl1_17
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f326,plain,
    ( ~ spl1_17
    | spl1_21 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl1_17
    | spl1_21 ),
    inference(subsumption_resolution,[],[f323,f311])).

fof(f323,plain,
    ( v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_17 ),
    inference(unit_resulting_resolution,[],[f32,f291,f39])).

fof(f322,plain,
    ( spl1_23
    | ~ spl1_5
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f130,f105,f65,f319])).

fof(f319,plain,
    ( spl1_23
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f105,plain,
    ( spl1_8
  <=> v1_relat_1(k5_relat_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f130,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,sK0)))
    | ~ spl1_5
    | ~ spl1_8 ),
    inference(unit_resulting_resolution,[],[f67,f107,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f107,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f317,plain,
    ( spl1_22
    | ~ spl1_1
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f129,f105,f42,f314])).

fof(f314,plain,
    ( spl1_22
  <=> v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f129,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,sK0)))
    | ~ spl1_1
    | ~ spl1_8 ),
    inference(unit_resulting_resolution,[],[f44,f107,f40])).

fof(f312,plain,
    ( ~ spl1_21
    | spl1_9
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f218,f158,f110,f309])).

fof(f110,plain,
    ( spl1_9
  <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f218,plain,
    ( ~ v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | spl1_9
    | ~ spl1_13 ),
    inference(unit_resulting_resolution,[],[f112,f160,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f112,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | spl1_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f307,plain,
    ( spl1_20
    | ~ spl1_5
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f127,f105,f65,f304])).

fof(f304,plain,
    ( spl1_20
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK0,sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f127,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK0,sK0),k1_xboole_0))
    | ~ spl1_5
    | ~ spl1_8 ),
    inference(unit_resulting_resolution,[],[f67,f107,f40])).

fof(f302,plain,
    ( spl1_19
    | ~ spl1_1
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f126,f105,f42,f299])).

fof(f299,plain,
    ( spl1_19
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK0,sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f126,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK0,sK0),sK0))
    | ~ spl1_1
    | ~ spl1_8 ),
    inference(unit_resulting_resolution,[],[f44,f107,f40])).

fof(f297,plain,
    ( spl1_18
    | ~ spl1_1
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f102,f65,f52,f42,f294])).

fof(f102,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f96,f54])).

fof(f96,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0))
    | ~ spl1_1
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f67,f44,f34])).

fof(f292,plain,
    ( spl1_17
    | ~ spl1_1
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f93,f65,f57,f42,f289])).

fof(f93,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f88,f59])).

fof(f88,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ spl1_1
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f44,f67,f33])).

fof(f287,plain,
    ( ~ spl1_16
    | spl1_9
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f217,f158,f110,f284])).

fof(f284,plain,
    ( spl1_16
  <=> v1_xboole_0(k1_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f217,plain,
    ( ~ v1_xboole_0(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | spl1_9
    | ~ spl1_13 ),
    inference(unit_resulting_resolution,[],[f112,f160,f37])).

fof(f282,plain,
    ( ~ spl1_15
    | spl1_9 ),
    inference(avatar_split_clause,[],[f134,f110,f279])).

fof(f279,plain,
    ( spl1_15
  <=> r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f134,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
    | spl1_9 ),
    inference(unit_resulting_resolution,[],[f32,f112,f39])).

fof(f237,plain,
    ( spl1_14
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f75,f65,f234])).

fof(f234,plain,
    ( spl1_14
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f75,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f67,f67,f40])).

fof(f161,plain,
    ( spl1_13
    | ~ spl1_1
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f74,f65,f42,f158])).

fof(f74,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_1
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f44,f67,f40])).

fof(f149,plain,
    ( spl1_12
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f95,f42,f146])).

fof(f146,plain,
    ( spl1_12
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK0,sK0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f95,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK0)),k1_relat_1(sK0))
    | ~ spl1_1 ),
    inference(unit_resulting_resolution,[],[f44,f44,f34])).

fof(f144,plain,
    ( spl1_11
    | ~ spl1_1
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f72,f65,f42,f141])).

fof(f72,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_1
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f44,f67,f40])).

fof(f139,plain,
    ( spl1_10
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f86,f42,f136])).

fof(f136,plain,
    ( spl1_10
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK0,sK0)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f86,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,sK0)),k2_relat_1(sK0))
    | ~ spl1_1 ),
    inference(unit_resulting_resolution,[],[f44,f44,f33])).

fof(f113,plain,
    ( ~ spl1_9
    | spl1_6 ),
    inference(avatar_split_clause,[],[f85,f77,f110])).

fof(f85,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | spl1_6 ),
    inference(unit_resulting_resolution,[],[f79,f36])).

fof(f79,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f108,plain,
    ( spl1_8
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f71,f42,f105])).

fof(f71,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK0))
    | ~ spl1_1 ),
    inference(unit_resulting_resolution,[],[f44,f44,f40])).

fof(f84,plain,
    ( ~ spl1_6
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f27,f81,f77])).

fof(f27,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f68,plain,
    ( spl1_5
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f61,f47,f65])).

fof(f47,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f61,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f49,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f60,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f55,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f30,f52])).

fof(f30,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f29,f47])).

fof(f29,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f45,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f28,f42])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (20686)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.42  % (20686)Refutation not found, incomplete strategy% (20686)------------------------------
% 0.20/0.42  % (20686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (20686)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.42  
% 0.20/0.42  % (20686)Memory used [KB]: 10618
% 0.20/0.42  % (20686)Time elapsed: 0.005 s
% 0.20/0.42  % (20686)------------------------------
% 0.20/0.42  % (20686)------------------------------
% 0.20/0.47  % (20678)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.50  % (20663)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.52  % (20670)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.52  % (20672)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.53  % (20672)Refutation not found, incomplete strategy% (20672)------------------------------
% 0.20/0.53  % (20672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20672)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (20672)Memory used [KB]: 10490
% 0.20/0.53  % (20672)Time elapsed: 0.102 s
% 0.20/0.53  % (20672)------------------------------
% 0.20/0.53  % (20672)------------------------------
% 0.20/0.53  % (20665)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.53  % (20665)Refutation not found, incomplete strategy% (20665)------------------------------
% 0.20/0.53  % (20665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20665)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (20665)Memory used [KB]: 10490
% 0.20/0.53  % (20665)Time elapsed: 0.097 s
% 0.20/0.53  % (20665)------------------------------
% 0.20/0.53  % (20665)------------------------------
% 0.20/0.53  % (20668)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.53  % (20664)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.53  % (20684)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.53  % (20680)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.54  % (20679)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.55  % (20681)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.55  % (20674)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.55  % (20667)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.55  % (20662)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.55  % (20675)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.55  % (20678)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f446,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f68,f84,f108,f113,f139,f144,f149,f161,f237,f282,f287,f292,f297,f302,f307,f312,f317,f322,f326,f329,f416,f422,f430,f438,f442,f445])).
% 0.20/0.55  fof(f445,plain,(
% 0.20/0.55    ~spl1_11 | ~spl1_18 | spl1_25),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f444])).
% 0.20/0.55  fof(f444,plain,(
% 0.20/0.55    $false | (~spl1_11 | ~spl1_18 | spl1_25)),
% 0.20/0.55    inference(subsumption_resolution,[],[f443,f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.55  fof(f443,plain,(
% 0.20/0.55    ~r1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) | (~spl1_11 | ~spl1_18 | spl1_25)),
% 0.20/0.55    inference(subsumption_resolution,[],[f440,f425])).
% 0.20/0.55  fof(f425,plain,(
% 0.20/0.55    ~v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl1_11 | spl1_25)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f143,f421,f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.55    inference(flattening,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.20/0.55  fof(f421,plain,(
% 0.20/0.55    ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | spl1_25),
% 0.20/0.55    inference(avatar_component_clause,[],[f419])).
% 0.20/0.55  fof(f419,plain,(
% 0.20/0.55    spl1_25 <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).
% 0.20/0.55  fof(f143,plain,(
% 0.20/0.55    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f141])).
% 0.20/0.55  fof(f141,plain,(
% 0.20/0.55    spl1_11 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.55  fof(f440,plain,(
% 0.20/0.55    v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~r1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) | ~spl1_18),
% 0.20/0.55    inference(resolution,[],[f296,f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_xboole_0(X1) | ~r1_xboole_0(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.55    inference(flattening,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.55  fof(f296,plain,(
% 0.20/0.55    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) | ~spl1_18),
% 0.20/0.55    inference(avatar_component_clause,[],[f294])).
% 0.20/0.55  fof(f294,plain,(
% 0.20/0.55    spl1_18 <=> r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.20/0.55  fof(f442,plain,(
% 0.20/0.55    ~spl1_11 | ~spl1_18 | spl1_25),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f441])).
% 0.20/0.55  fof(f441,plain,(
% 0.20/0.55    $false | (~spl1_11 | ~spl1_18 | spl1_25)),
% 0.20/0.55    inference(subsumption_resolution,[],[f439,f425])).
% 0.20/0.55  fof(f439,plain,(
% 0.20/0.55    v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~spl1_18),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f32,f296,f39])).
% 0.20/0.55  fof(f438,plain,(
% 0.20/0.55    ~spl1_27 | spl1_25),
% 0.20/0.55    inference(avatar_split_clause,[],[f423,f419,f435])).
% 0.20/0.55  fof(f435,plain,(
% 0.20/0.55    spl1_27 <=> r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).
% 0.20/0.55  fof(f423,plain,(
% 0.20/0.55    ~r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) | spl1_25),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f32,f421,f39])).
% 0.20/0.55  fof(f430,plain,(
% 0.20/0.55    spl1_26 | ~spl1_1 | ~spl1_3 | ~spl1_5 | ~spl1_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f369,f77,f65,f52,f42,f427])).
% 0.20/0.55  fof(f427,plain,(
% 0.20/0.55    spl1_26 <=> r1_tarski(k1_xboole_0,k1_relat_1(sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    spl1_1 <=> v1_relat_1(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    spl1_5 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.55  % (20669)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    spl1_6 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.55  fof(f369,plain,(
% 0.20/0.55    r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | (~spl1_1 | ~spl1_3 | ~spl1_5 | ~spl1_6)),
% 0.20/0.55    inference(forward_demodulation,[],[f331,f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f52])).
% 0.20/0.55  fof(f331,plain,(
% 0.20/0.55    r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(sK0)) | (~spl1_1 | ~spl1_5 | ~spl1_6)),
% 0.20/0.55    inference(backward_demodulation,[],[f97,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl1_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f77])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    r1_tarski(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_relat_1(sK0)) | (~spl1_1 | ~spl1_5)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f44,f67,f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    v1_relat_1(k1_xboole_0) | ~spl1_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f65])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    v1_relat_1(sK0) | ~spl1_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f42])).
% 0.20/0.55  fof(f422,plain,(
% 0.20/0.55    ~spl1_25 | spl1_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f417,f81,f419])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    spl1_7 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.55  fof(f417,plain,(
% 0.20/0.55    ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | spl1_7),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f83,f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f81])).
% 0.20/0.55  fof(f416,plain,(
% 0.20/0.55    spl1_24 | ~spl1_1 | ~spl1_4 | ~spl1_6 | ~spl1_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f372,f158,f77,f57,f42,f413])).
% 0.20/0.55  fof(f413,plain,(
% 0.20/0.55    spl1_24 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    spl1_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.55  fof(f158,plain,(
% 0.20/0.55    spl1_13 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.20/0.55  fof(f372,plain,(
% 0.20/0.55    r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl1_1 | ~spl1_4 | ~spl1_6 | ~spl1_13)),
% 0.20/0.55    inference(forward_demodulation,[],[f371,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f57])).
% 0.20/0.55  fof(f371,plain,(
% 0.20/0.55    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | (~spl1_1 | ~spl1_4 | ~spl1_6 | ~spl1_13)),
% 0.20/0.55    inference(forward_demodulation,[],[f370,f78])).
% 0.20/0.55  fof(f370,plain,(
% 0.20/0.55    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | (~spl1_1 | ~spl1_4 | ~spl1_6 | ~spl1_13)),
% 0.20/0.55    inference(forward_demodulation,[],[f337,f59])).
% 0.20/0.55  % (20666)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.55  fof(f337,plain,(
% 0.20/0.55    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0)) | (~spl1_1 | ~spl1_6 | ~spl1_13)),
% 0.20/0.55    inference(backward_demodulation,[],[f202,f78])).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    r1_tarski(k2_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_1 | ~spl1_13)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f44,f160,f33])).
% 0.20/0.55  % (20669)Refutation not found, incomplete strategy% (20669)------------------------------
% 0.20/0.55  % (20669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20669)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (20669)Memory used [KB]: 6140
% 0.20/0.55  % (20669)Time elapsed: 0.123 s
% 0.20/0.55  % (20669)------------------------------
% 0.20/0.55  % (20669)------------------------------
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 0.20/0.55  fof(f160,plain,(
% 0.20/0.55    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f158])).
% 0.20/0.55  fof(f329,plain,(
% 0.20/0.55    ~spl1_17 | spl1_21),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f328])).
% 0.20/0.55  fof(f328,plain,(
% 0.20/0.55    $false | (~spl1_17 | spl1_21)),
% 0.20/0.55    inference(subsumption_resolution,[],[f327,f32])).
% 0.20/0.55  fof(f327,plain,(
% 0.20/0.55    ~r1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | (~spl1_17 | spl1_21)),
% 0.20/0.55    inference(subsumption_resolution,[],[f324,f311])).
% 0.20/0.55  fof(f311,plain,(
% 0.20/0.55    ~v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) | spl1_21),
% 0.20/0.55    inference(avatar_component_clause,[],[f309])).
% 0.20/0.55  fof(f309,plain,(
% 0.20/0.55    spl1_21 <=> v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.20/0.55  fof(f324,plain,(
% 0.20/0.55    v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~r1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | ~spl1_17),
% 0.20/0.55    inference(resolution,[],[f291,f39])).
% 0.20/0.55  fof(f291,plain,(
% 0.20/0.55    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | ~spl1_17),
% 0.20/0.55    inference(avatar_component_clause,[],[f289])).
% 0.20/0.55  fof(f289,plain,(
% 0.20/0.55    spl1_17 <=> r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.20/0.55  fof(f326,plain,(
% 0.20/0.55    ~spl1_17 | spl1_21),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f325])).
% 0.20/0.55  fof(f325,plain,(
% 0.20/0.55    $false | (~spl1_17 | spl1_21)),
% 0.20/0.55    inference(subsumption_resolution,[],[f323,f311])).
% 0.20/0.55  fof(f323,plain,(
% 0.20/0.55    v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_17),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f32,f291,f39])).
% 0.20/0.55  fof(f322,plain,(
% 0.20/0.55    spl1_23 | ~spl1_5 | ~spl1_8),
% 0.20/0.55    inference(avatar_split_clause,[],[f130,f105,f65,f319])).
% 0.20/0.55  fof(f319,plain,(
% 0.20/0.55    spl1_23 <=> v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    spl1_8 <=> v1_relat_1(k5_relat_1(sK0,sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.55  fof(f130,plain,(
% 0.20/0.55    v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK0,sK0))) | (~spl1_5 | ~spl1_8)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f67,f107,f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    v1_relat_1(k5_relat_1(sK0,sK0)) | ~spl1_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f105])).
% 0.20/0.55  fof(f317,plain,(
% 0.20/0.55    spl1_22 | ~spl1_1 | ~spl1_8),
% 0.20/0.55    inference(avatar_split_clause,[],[f129,f105,f42,f314])).
% 0.20/0.55  fof(f314,plain,(
% 0.20/0.55    spl1_22 <=> v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.20/0.55  fof(f129,plain,(
% 0.20/0.55    v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,sK0))) | (~spl1_1 | ~spl1_8)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f44,f107,f40])).
% 0.20/0.55  fof(f312,plain,(
% 0.20/0.55    ~spl1_21 | spl1_9 | ~spl1_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f218,f158,f110,f309])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    spl1_9 <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.55  fof(f218,plain,(
% 0.20/0.55    ~v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (spl1_9 | ~spl1_13)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f112,f160,f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.56    inference(flattening,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.20/0.56  fof(f112,plain,(
% 0.20/0.56    ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | spl1_9),
% 0.20/0.56    inference(avatar_component_clause,[],[f110])).
% 0.20/0.56  fof(f307,plain,(
% 0.20/0.56    spl1_20 | ~spl1_5 | ~spl1_8),
% 0.20/0.56    inference(avatar_split_clause,[],[f127,f105,f65,f304])).
% 0.20/0.56  fof(f304,plain,(
% 0.20/0.56    spl1_20 <=> v1_relat_1(k5_relat_1(k5_relat_1(sK0,sK0),k1_xboole_0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.20/0.56  fof(f127,plain,(
% 0.20/0.56    v1_relat_1(k5_relat_1(k5_relat_1(sK0,sK0),k1_xboole_0)) | (~spl1_5 | ~spl1_8)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f67,f107,f40])).
% 0.20/0.56  fof(f302,plain,(
% 0.20/0.56    spl1_19 | ~spl1_1 | ~spl1_8),
% 0.20/0.56    inference(avatar_split_clause,[],[f126,f105,f42,f299])).
% 0.20/0.56  fof(f299,plain,(
% 0.20/0.56    spl1_19 <=> v1_relat_1(k5_relat_1(k5_relat_1(sK0,sK0),sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.20/0.56  fof(f126,plain,(
% 0.20/0.56    v1_relat_1(k5_relat_1(k5_relat_1(sK0,sK0),sK0)) | (~spl1_1 | ~spl1_8)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f44,f107,f40])).
% 0.20/0.56  fof(f297,plain,(
% 0.20/0.56    spl1_18 | ~spl1_1 | ~spl1_3 | ~spl1_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f102,f65,f52,f42,f294])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) | (~spl1_1 | ~spl1_3 | ~spl1_5)),
% 0.20/0.56    inference(forward_demodulation,[],[f96,f54])).
% 0.20/0.56  fof(f96,plain,(
% 0.20/0.56    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0)) | (~spl1_1 | ~spl1_5)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f67,f44,f34])).
% 0.20/0.56  fof(f292,plain,(
% 0.20/0.56    spl1_17 | ~spl1_1 | ~spl1_4 | ~spl1_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f93,f65,f57,f42,f289])).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | (~spl1_1 | ~spl1_4 | ~spl1_5)),
% 0.20/0.56    inference(forward_demodulation,[],[f88,f59])).
% 0.20/0.56  fof(f88,plain,(
% 0.20/0.56    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0)) | (~spl1_1 | ~spl1_5)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f44,f67,f33])).
% 0.20/0.56  fof(f287,plain,(
% 0.20/0.56    ~spl1_16 | spl1_9 | ~spl1_13),
% 0.20/0.56    inference(avatar_split_clause,[],[f217,f158,f110,f284])).
% 0.20/0.56  fof(f284,plain,(
% 0.20/0.56    spl1_16 <=> v1_xboole_0(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.20/0.56  fof(f217,plain,(
% 0.20/0.56    ~v1_xboole_0(k1_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (spl1_9 | ~spl1_13)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f112,f160,f37])).
% 0.20/0.56  fof(f282,plain,(
% 0.20/0.56    ~spl1_15 | spl1_9),
% 0.20/0.56    inference(avatar_split_clause,[],[f134,f110,f279])).
% 0.20/0.56  fof(f279,plain,(
% 0.20/0.56    spl1_15 <=> r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.20/0.56  fof(f134,plain,(
% 0.20/0.56    ~r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) | spl1_9),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f32,f112,f39])).
% 0.20/0.56  fof(f237,plain,(
% 0.20/0.56    spl1_14 | ~spl1_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f75,f65,f234])).
% 0.20/0.56  fof(f234,plain,(
% 0.20/0.56    spl1_14 <=> v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.20/0.56  fof(f75,plain,(
% 0.20/0.56    v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) | ~spl1_5),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f67,f67,f40])).
% 0.20/0.56  fof(f161,plain,(
% 0.20/0.56    spl1_13 | ~spl1_1 | ~spl1_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f74,f65,f42,f158])).
% 0.20/0.56  fof(f74,plain,(
% 0.20/0.56    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_1 | ~spl1_5)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f44,f67,f40])).
% 0.20/0.56  fof(f149,plain,(
% 0.20/0.56    spl1_12 | ~spl1_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f95,f42,f146])).
% 0.20/0.56  fof(f146,plain,(
% 0.20/0.56    spl1_12 <=> r1_tarski(k1_relat_1(k5_relat_1(sK0,sK0)),k1_relat_1(sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.20/0.56  fof(f95,plain,(
% 0.20/0.56    r1_tarski(k1_relat_1(k5_relat_1(sK0,sK0)),k1_relat_1(sK0)) | ~spl1_1),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f44,f44,f34])).
% 0.20/0.56  fof(f144,plain,(
% 0.20/0.56    spl1_11 | ~spl1_1 | ~spl1_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f72,f65,f42,f141])).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_1 | ~spl1_5)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f44,f67,f40])).
% 0.20/0.56  fof(f139,plain,(
% 0.20/0.56    spl1_10 | ~spl1_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f86,f42,f136])).
% 0.20/0.56  fof(f136,plain,(
% 0.20/0.56    spl1_10 <=> r1_tarski(k2_relat_1(k5_relat_1(sK0,sK0)),k2_relat_1(sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    r1_tarski(k2_relat_1(k5_relat_1(sK0,sK0)),k2_relat_1(sK0)) | ~spl1_1),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f44,f44,f33])).
% 0.20/0.56  fof(f113,plain,(
% 0.20/0.56    ~spl1_9 | spl1_6),
% 0.20/0.56    inference(avatar_split_clause,[],[f85,f77,f110])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | spl1_6),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f79,f36])).
% 0.20/0.56  fof(f79,plain,(
% 0.20/0.56    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_6),
% 0.20/0.56    inference(avatar_component_clause,[],[f77])).
% 0.20/0.56  fof(f108,plain,(
% 0.20/0.56    spl1_8 | ~spl1_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f71,f42,f105])).
% 0.20/0.56  fof(f71,plain,(
% 0.20/0.56    v1_relat_1(k5_relat_1(sK0,sK0)) | ~spl1_1),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f44,f44,f40])).
% 0.20/0.56  fof(f84,plain,(
% 0.20/0.56    ~spl1_6 | ~spl1_7),
% 0.20/0.56    inference(avatar_split_clause,[],[f27,f81,f77])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,negated_conjecture,(
% 0.20/0.56    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.56    inference(negated_conjecture,[],[f12])).
% 0.20/0.56  fof(f12,conjecture,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.20/0.56  fof(f68,plain,(
% 0.20/0.56    spl1_5 | ~spl1_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f61,f47,f65])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    v1_relat_1(k1_xboole_0) | ~spl1_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f49,f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f47])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    spl1_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f31,f57])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,axiom,(
% 0.20/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    spl1_3),
% 0.20/0.56    inference(avatar_split_clause,[],[f30,f52])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    spl1_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f29,f47])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    inference(cnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    spl1_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f28,f42])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    v1_relat_1(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (20678)------------------------------
% 0.20/0.56  % (20678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (20678)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (20678)Memory used [KB]: 1791
% 0.20/0.56  % (20678)Time elapsed: 0.116 s
% 0.20/0.56  % (20678)------------------------------
% 0.20/0.56  % (20678)------------------------------
% 0.20/0.56  % (20673)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.56  % (20655)Success in time 0.201 s
%------------------------------------------------------------------------------
