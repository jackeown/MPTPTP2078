%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:20 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 206 expanded)
%              Number of leaves         :   27 (  93 expanded)
%              Depth                    :    7
%              Number of atoms          :  245 ( 435 expanded)
%              Number of equality atoms :   58 ( 122 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f310,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f57,f64,f69,f80,f99,f104,f114,f119,f130,f153,f161,f179,f196,f224,f238,f246,f271,f285,f309])).

fof(f309,plain,
    ( spl4_32
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f304,f270])).

fof(f270,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1))
    | spl4_32 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl4_32
  <=> r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f304,plain,
    ( r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1))
    | ~ spl4_34 ),
    inference(superposition,[],[f24,f284])).

fof(f284,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_xboole_0,sK1),sK1)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl4_34
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_xboole_0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f285,plain,
    ( spl4_34
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f252,f243,f282])).

fof(f243,plain,
    ( spl4_29
  <=> r1_tarski(k3_xboole_0(k1_xboole_0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f252,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_xboole_0,sK1),sK1)
    | ~ spl4_29 ),
    inference(resolution,[],[f245,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f245,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,sK1),sK1)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f243])).

fof(f271,plain,
    ( ~ spl4_32
    | spl4_21
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f261,f235,f193,f268])).

fof(f193,plain,
    ( spl4_21
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f235,plain,
    ( spl4_28
  <=> r1_tarski(k3_xboole_0(k1_xboole_0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f261,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1))
    | spl4_21
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f260,f195])).

fof(f195,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f193])).

fof(f260,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1))
    | k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_28 ),
    inference(resolution,[],[f237,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f237,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f235])).

fof(f246,plain,
    ( spl4_29
    | ~ spl4_3
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f241,f176,f54,f243])).

fof(f54,plain,
    ( spl4_3
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f176,plain,
    ( spl4_19
  <=> k4_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k3_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f241,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,sK1),sK1)
    | ~ spl4_3
    | ~ spl4_19 ),
    inference(resolution,[],[f185,f56])).

fof(f56,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k10_relat_1(sK0,sK2),X0)
        | r1_tarski(k3_xboole_0(k1_xboole_0,sK1),X0) )
    | ~ spl4_19 ),
    inference(superposition,[],[f39,f178])).

fof(f178,plain,
    ( k4_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f176])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f238,plain,
    ( spl4_28
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f228,f221,f235])).

fof(f221,plain,
    ( spl4_26
  <=> k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f228,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl4_26 ),
    inference(superposition,[],[f24,f223])).

fof(f223,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f221])).

fof(f224,plain,
    ( spl4_26
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f167,f158,f221])).

fof(f158,plain,
    ( spl4_18
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f167,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_18 ),
    inference(superposition,[],[f28,f160])).

fof(f160,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f158])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f196,plain,
    ( ~ spl4_21
    | spl4_17
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f189,f176,f150,f193])).

fof(f150,plain,
    ( spl4_17
  <=> r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f189,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1)
    | spl4_17
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f186,f152])).

fof(f152,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f150])).

fof(f186,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1)
    | r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))
    | ~ spl4_19 ),
    inference(superposition,[],[f36,f178])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f179,plain,
    ( spl4_19
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f170,f158,f116,f111,f176])).

fof(f111,plain,
    ( spl4_11
  <=> k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f116,plain,
    ( spl4_12
  <=> k3_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f170,plain,
    ( k4_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f125,f167])).

fof(f125,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f124,f118])).

fof(f118,plain,
    ( k3_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2)) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f124,plain,
    ( k3_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2)) = k4_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f122,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f122,plain,
    ( k3_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0) = k4_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))
    | ~ spl4_11 ),
    inference(superposition,[],[f28,f113])).

fof(f113,plain,
    ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f161,plain,
    ( spl4_18
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f156,f66,f54,f158])).

fof(f66,plain,
    ( spl4_5
  <=> k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f156,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(resolution,[],[f93,f56])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k10_relat_1(sK0,sK2),X0)
        | k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f70,f35])).

fof(f70,plain,
    ( ! [X0] :
        ( r1_tarski(k1_xboole_0,X0)
        | ~ r1_tarski(k10_relat_1(sK0,sK2),X0) )
    | ~ spl4_5 ),
    inference(superposition,[],[f39,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f153,plain,
    ( ~ spl4_17
    | spl4_10
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f133,f127,f101,f150])).

fof(f101,plain,
    ( spl4_10
  <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f127,plain,
    ( spl4_13
  <=> r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f133,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))
    | spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f132,f103])).

fof(f103,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f132,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))
    | k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ spl4_13 ),
    inference(resolution,[],[f129,f31])).

fof(f129,plain,
    ( r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f130,plain,
    ( spl4_13
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f123,f111,f127])).

fof(f123,plain,
    ( r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | ~ spl4_11 ),
    inference(superposition,[],[f24,f113])).

fof(f119,plain,
    ( spl4_12
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f107,f96,f116])).

fof(f96,plain,
    ( spl4_9
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f107,plain,
    ( k3_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2)) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_9 ),
    inference(superposition,[],[f28,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f114,plain,
    ( spl4_11
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f75,f66,f111])).

fof(f75,plain,
    ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f72,f25])).

fof(f72,plain,
    ( k3_xboole_0(k10_relat_1(sK0,sK2),sK1) = k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0)
    | ~ spl4_5 ),
    inference(superposition,[],[f28,f68])).

fof(f104,plain,
    ( ~ spl4_10
    | ~ spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f90,f61,f43,f101])).

fof(f43,plain,
    ( spl4_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f61,plain,
    ( spl4_4
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f90,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ spl4_1
    | spl4_4 ),
    inference(superposition,[],[f63,f52])).

fof(f52,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1))
    | ~ spl4_1 ),
    inference(resolution,[],[f45,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f45,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f63,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f99,plain,
    ( spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f91,f77,f96])).

fof(f77,plain,
    ( spl4_6
  <=> r1_tarski(k1_xboole_0,k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f91,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f79,f35])).

fof(f79,plain,
    ( r1_tarski(k1_xboole_0,k10_relat_1(sK0,sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f80,plain,
    ( spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f73,f66,f77])).

fof(f73,plain,
    ( r1_tarski(k1_xboole_0,k10_relat_1(sK0,sK2))
    | ~ spl4_5 ),
    inference(superposition,[],[f24,f68])).

fof(f69,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f58,f54,f66])).

fof(f58,plain,
    ( k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f56,f35])).

fof(f64,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f21,f61])).

fof(f21,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f57,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f54])).

fof(f20,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:52:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.13/0.52  % (4499)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.13/0.52  % (4495)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.13/0.53  % (4494)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.13/0.53  % (4502)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.13/0.53  % (4493)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.26/0.54  % (4510)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.26/0.54  % (4496)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.26/0.54  % (4501)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.26/0.54  % (4507)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.26/0.54  % (4515)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.26/0.54  % (4521)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.26/0.54  % (4517)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.26/0.55  % (4509)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.26/0.55  % (4522)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.26/0.55  % (4520)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.26/0.55  % (4508)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.26/0.55  % (4495)Refutation not found, incomplete strategy% (4495)------------------------------
% 1.26/0.55  % (4495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.55  % (4495)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.55  
% 1.26/0.55  % (4495)Memory used [KB]: 10746
% 1.26/0.55  % (4495)Time elapsed: 0.128 s
% 1.26/0.55  % (4495)------------------------------
% 1.26/0.55  % (4495)------------------------------
% 1.26/0.55  % (4514)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.26/0.55  % (4506)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.26/0.55  % (4515)Refutation not found, incomplete strategy% (4515)------------------------------
% 1.26/0.55  % (4515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.55  % (4515)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.55  
% 1.26/0.55  % (4515)Memory used [KB]: 10746
% 1.26/0.55  % (4515)Time elapsed: 0.125 s
% 1.26/0.55  % (4515)------------------------------
% 1.26/0.55  % (4515)------------------------------
% 1.26/0.55  % (4513)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.26/0.55  % (4510)Refutation not found, incomplete strategy% (4510)------------------------------
% 1.26/0.55  % (4510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.55  % (4510)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.55  
% 1.26/0.55  % (4510)Memory used [KB]: 10618
% 1.26/0.55  % (4510)Time elapsed: 0.141 s
% 1.26/0.55  % (4510)------------------------------
% 1.26/0.55  % (4510)------------------------------
% 1.26/0.56  % (4498)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.26/0.56  % (4503)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.26/0.56  % (4503)Refutation not found, incomplete strategy% (4503)------------------------------
% 1.26/0.56  % (4503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.56  % (4503)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.56  
% 1.26/0.56  % (4503)Memory used [KB]: 10618
% 1.26/0.56  % (4503)Time elapsed: 0.145 s
% 1.26/0.56  % (4503)------------------------------
% 1.26/0.56  % (4503)------------------------------
% 1.26/0.56  % (4512)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.26/0.56  % (4505)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.56  % (4500)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.26/0.57  % (4504)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.26/0.57  % (4504)Refutation not found, incomplete strategy% (4504)------------------------------
% 1.26/0.57  % (4504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.57  % (4504)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.57  
% 1.26/0.57  % (4504)Memory used [KB]: 10618
% 1.26/0.57  % (4504)Time elapsed: 0.150 s
% 1.26/0.57  % (4504)------------------------------
% 1.26/0.57  % (4504)------------------------------
% 1.26/0.57  % (4519)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.26/0.57  % (4497)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.26/0.58  % (4513)Refutation found. Thanks to Tanya!
% 1.26/0.58  % SZS status Theorem for theBenchmark
% 1.26/0.58  % SZS output start Proof for theBenchmark
% 1.26/0.58  fof(f310,plain,(
% 1.26/0.58    $false),
% 1.26/0.58    inference(avatar_sat_refutation,[],[f46,f57,f64,f69,f80,f99,f104,f114,f119,f130,f153,f161,f179,f196,f224,f238,f246,f271,f285,f309])).
% 1.26/0.58  fof(f309,plain,(
% 1.26/0.58    spl4_32 | ~spl4_34),
% 1.26/0.58    inference(avatar_contradiction_clause,[],[f308])).
% 1.26/0.58  fof(f308,plain,(
% 1.26/0.58    $false | (spl4_32 | ~spl4_34)),
% 1.26/0.58    inference(subsumption_resolution,[],[f304,f270])).
% 1.26/0.58  fof(f270,plain,(
% 1.26/0.58    ~r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) | spl4_32),
% 1.26/0.58    inference(avatar_component_clause,[],[f268])).
% 1.26/0.58  fof(f268,plain,(
% 1.26/0.58    spl4_32 <=> r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1))),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.26/0.58  fof(f304,plain,(
% 1.26/0.58    r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) | ~spl4_34),
% 1.26/0.58    inference(superposition,[],[f24,f284])).
% 1.26/0.58  fof(f284,plain,(
% 1.26/0.58    k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_xboole_0,sK1),sK1) | ~spl4_34),
% 1.26/0.58    inference(avatar_component_clause,[],[f282])).
% 1.26/0.58  fof(f282,plain,(
% 1.26/0.58    spl4_34 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_xboole_0,sK1),sK1)),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.26/0.58  fof(f24,plain,(
% 1.26/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.26/0.58    inference(cnf_transformation,[],[f6])).
% 1.26/0.58  fof(f6,axiom,(
% 1.26/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.26/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.26/0.58  fof(f285,plain,(
% 1.26/0.58    spl4_34 | ~spl4_29),
% 1.26/0.58    inference(avatar_split_clause,[],[f252,f243,f282])).
% 1.26/0.58  fof(f243,plain,(
% 1.26/0.58    spl4_29 <=> r1_tarski(k3_xboole_0(k1_xboole_0,sK1),sK1)),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.26/0.58  fof(f252,plain,(
% 1.26/0.58    k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_xboole_0,sK1),sK1) | ~spl4_29),
% 1.26/0.58    inference(resolution,[],[f245,f35])).
% 1.26/0.58  fof(f35,plain,(
% 1.26/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.26/0.58    inference(cnf_transformation,[],[f4])).
% 1.26/0.58  fof(f4,axiom,(
% 1.26/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.26/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.26/0.58  fof(f245,plain,(
% 1.26/0.58    r1_tarski(k3_xboole_0(k1_xboole_0,sK1),sK1) | ~spl4_29),
% 1.26/0.58    inference(avatar_component_clause,[],[f243])).
% 1.26/0.58  fof(f271,plain,(
% 1.26/0.58    ~spl4_32 | spl4_21 | ~spl4_28),
% 1.26/0.58    inference(avatar_split_clause,[],[f261,f235,f193,f268])).
% 1.26/0.58  fof(f193,plain,(
% 1.26/0.58    spl4_21 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.26/0.58  fof(f235,plain,(
% 1.26/0.58    spl4_28 <=> r1_tarski(k3_xboole_0(k1_xboole_0,sK1),k1_xboole_0)),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.26/0.58  fof(f261,plain,(
% 1.26/0.58    ~r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) | (spl4_21 | ~spl4_28)),
% 1.26/0.58    inference(subsumption_resolution,[],[f260,f195])).
% 1.26/0.58  fof(f195,plain,(
% 1.26/0.58    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1) | spl4_21),
% 1.26/0.58    inference(avatar_component_clause,[],[f193])).
% 1.26/0.58  fof(f260,plain,(
% 1.26/0.58    ~r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) | ~spl4_28),
% 1.26/0.58    inference(resolution,[],[f237,f31])).
% 1.26/0.58  fof(f31,plain,(
% 1.26/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.26/0.58    inference(cnf_transformation,[],[f3])).
% 1.26/0.58  fof(f3,axiom,(
% 1.26/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.26/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.26/0.58  fof(f237,plain,(
% 1.26/0.58    r1_tarski(k3_xboole_0(k1_xboole_0,sK1),k1_xboole_0) | ~spl4_28),
% 1.26/0.58    inference(avatar_component_clause,[],[f235])).
% 1.26/0.58  fof(f246,plain,(
% 1.26/0.58    spl4_29 | ~spl4_3 | ~spl4_19),
% 1.26/0.58    inference(avatar_split_clause,[],[f241,f176,f54,f243])).
% 1.26/0.58  fof(f54,plain,(
% 1.26/0.58    spl4_3 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.26/0.58  fof(f176,plain,(
% 1.26/0.58    spl4_19 <=> k4_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k3_xboole_0(k1_xboole_0,sK1)),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.26/0.58  fof(f241,plain,(
% 1.26/0.58    r1_tarski(k3_xboole_0(k1_xboole_0,sK1),sK1) | (~spl4_3 | ~spl4_19)),
% 1.26/0.58    inference(resolution,[],[f185,f56])).
% 1.26/0.58  fof(f56,plain,(
% 1.26/0.58    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl4_3),
% 1.26/0.58    inference(avatar_component_clause,[],[f54])).
% 1.26/0.58  fof(f185,plain,(
% 1.26/0.58    ( ! [X0] : (~r1_tarski(k10_relat_1(sK0,sK2),X0) | r1_tarski(k3_xboole_0(k1_xboole_0,sK1),X0)) ) | ~spl4_19),
% 1.26/0.58    inference(superposition,[],[f39,f178])).
% 1.26/0.58  fof(f178,plain,(
% 1.26/0.58    k4_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k3_xboole_0(k1_xboole_0,sK1) | ~spl4_19),
% 1.26/0.58    inference(avatar_component_clause,[],[f176])).
% 1.26/0.58  fof(f39,plain,(
% 1.26/0.58    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.26/0.58    inference(cnf_transformation,[],[f19])).
% 1.26/0.58  fof(f19,plain,(
% 1.26/0.58    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.26/0.58    inference(ennf_transformation,[],[f5])).
% 1.26/0.58  fof(f5,axiom,(
% 1.26/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 1.26/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 1.26/0.58  fof(f238,plain,(
% 1.26/0.58    spl4_28 | ~spl4_26),
% 1.26/0.58    inference(avatar_split_clause,[],[f228,f221,f235])).
% 1.26/0.58  fof(f221,plain,(
% 1.26/0.58    spl4_26 <=> k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK1)),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.26/0.58  fof(f228,plain,(
% 1.26/0.58    r1_tarski(k3_xboole_0(k1_xboole_0,sK1),k1_xboole_0) | ~spl4_26),
% 1.26/0.58    inference(superposition,[],[f24,f223])).
% 1.26/0.58  fof(f223,plain,(
% 1.26/0.58    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK1) | ~spl4_26),
% 1.26/0.58    inference(avatar_component_clause,[],[f221])).
% 1.26/0.58  fof(f224,plain,(
% 1.26/0.58    spl4_26 | ~spl4_18),
% 1.26/0.58    inference(avatar_split_clause,[],[f167,f158,f221])).
% 1.26/0.58  fof(f158,plain,(
% 1.26/0.58    spl4_18 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.26/0.58  fof(f167,plain,(
% 1.26/0.58    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK1) | ~spl4_18),
% 1.26/0.58    inference(superposition,[],[f28,f160])).
% 1.26/0.58  fof(f160,plain,(
% 1.26/0.58    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | ~spl4_18),
% 1.26/0.58    inference(avatar_component_clause,[],[f158])).
% 1.26/0.58  fof(f28,plain,(
% 1.26/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.26/0.58    inference(cnf_transformation,[],[f7])).
% 1.26/0.58  fof(f7,axiom,(
% 1.26/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.26/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.26/0.58  fof(f196,plain,(
% 1.26/0.58    ~spl4_21 | spl4_17 | ~spl4_19),
% 1.26/0.58    inference(avatar_split_clause,[],[f189,f176,f150,f193])).
% 1.26/0.58  fof(f150,plain,(
% 1.26/0.58    spl4_17 <=> r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.26/0.58  fof(f189,plain,(
% 1.26/0.58    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1) | (spl4_17 | ~spl4_19)),
% 1.26/0.58    inference(subsumption_resolution,[],[f186,f152])).
% 1.26/0.58  fof(f152,plain,(
% 1.26/0.58    ~r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) | spl4_17),
% 1.26/0.58    inference(avatar_component_clause,[],[f150])).
% 1.26/0.58  fof(f186,plain,(
% 1.26/0.58    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1) | r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) | ~spl4_19),
% 1.26/0.58    inference(superposition,[],[f36,f178])).
% 1.26/0.58  fof(f36,plain,(
% 1.26/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.26/0.58    inference(cnf_transformation,[],[f4])).
% 1.26/0.58  fof(f179,plain,(
% 1.26/0.58    spl4_19 | ~spl4_11 | ~spl4_12 | ~spl4_18),
% 1.26/0.58    inference(avatar_split_clause,[],[f170,f158,f116,f111,f176])).
% 1.26/0.58  fof(f111,plain,(
% 1.26/0.58    spl4_11 <=> k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0)),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.26/0.58  fof(f116,plain,(
% 1.26/0.58    spl4_12 <=> k3_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2)) = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.26/0.58  fof(f170,plain,(
% 1.26/0.58    k4_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k3_xboole_0(k1_xboole_0,sK1) | (~spl4_11 | ~spl4_12 | ~spl4_18)),
% 1.26/0.58    inference(backward_demodulation,[],[f125,f167])).
% 1.26/0.58  fof(f125,plain,(
% 1.26/0.58    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) | (~spl4_11 | ~spl4_12)),
% 1.26/0.58    inference(forward_demodulation,[],[f124,f118])).
% 1.26/0.58  fof(f118,plain,(
% 1.26/0.58    k3_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_12),
% 1.26/0.58    inference(avatar_component_clause,[],[f116])).
% 1.26/0.58  fof(f124,plain,(
% 1.26/0.58    k3_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2)) = k4_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) | ~spl4_11),
% 1.26/0.58    inference(forward_demodulation,[],[f122,f25])).
% 1.26/0.58  fof(f25,plain,(
% 1.26/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.26/0.58    inference(cnf_transformation,[],[f1])).
% 1.26/0.58  fof(f1,axiom,(
% 1.26/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.26/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.26/0.58  fof(f122,plain,(
% 1.26/0.58    k3_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0) = k4_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) | ~spl4_11),
% 1.26/0.58    inference(superposition,[],[f28,f113])).
% 1.26/0.58  fof(f113,plain,(
% 1.26/0.58    k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0) | ~spl4_11),
% 1.26/0.58    inference(avatar_component_clause,[],[f111])).
% 1.26/0.58  fof(f161,plain,(
% 1.26/0.58    spl4_18 | ~spl4_3 | ~spl4_5),
% 1.26/0.58    inference(avatar_split_clause,[],[f156,f66,f54,f158])).
% 1.26/0.58  fof(f66,plain,(
% 1.26/0.58    spl4_5 <=> k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1)),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.26/0.58  fof(f156,plain,(
% 1.26/0.58    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | (~spl4_3 | ~spl4_5)),
% 1.26/0.58    inference(resolution,[],[f93,f56])).
% 1.26/0.58  fof(f93,plain,(
% 1.26/0.58    ( ! [X0] : (~r1_tarski(k10_relat_1(sK0,sK2),X0) | k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl4_5),
% 1.26/0.58    inference(resolution,[],[f70,f35])).
% 1.26/0.58  fof(f70,plain,(
% 1.26/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~r1_tarski(k10_relat_1(sK0,sK2),X0)) ) | ~spl4_5),
% 1.26/0.58    inference(superposition,[],[f39,f68])).
% 1.26/0.58  fof(f68,plain,(
% 1.26/0.58    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1) | ~spl4_5),
% 1.26/0.58    inference(avatar_component_clause,[],[f66])).
% 1.26/0.58  fof(f153,plain,(
% 1.26/0.58    ~spl4_17 | spl4_10 | ~spl4_13),
% 1.26/0.58    inference(avatar_split_clause,[],[f133,f127,f101,f150])).
% 1.26/0.58  fof(f101,plain,(
% 1.26/0.58    spl4_10 <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.26/0.58  fof(f127,plain,(
% 1.26/0.58    spl4_13 <=> r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.26/0.58  fof(f133,plain,(
% 1.26/0.58    ~r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) | (spl4_10 | ~spl4_13)),
% 1.26/0.58    inference(subsumption_resolution,[],[f132,f103])).
% 1.26/0.58  fof(f103,plain,(
% 1.26/0.58    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | spl4_10),
% 1.26/0.58    inference(avatar_component_clause,[],[f101])).
% 1.26/0.58  fof(f132,plain,(
% 1.26/0.58    ~r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) | k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~spl4_13),
% 1.26/0.58    inference(resolution,[],[f129,f31])).
% 1.26/0.58  fof(f129,plain,(
% 1.26/0.58    r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | ~spl4_13),
% 1.26/0.58    inference(avatar_component_clause,[],[f127])).
% 1.26/0.58  fof(f130,plain,(
% 1.26/0.58    spl4_13 | ~spl4_11),
% 1.26/0.58    inference(avatar_split_clause,[],[f123,f111,f127])).
% 1.26/0.58  fof(f123,plain,(
% 1.26/0.58    r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | ~spl4_11),
% 1.26/0.58    inference(superposition,[],[f24,f113])).
% 1.26/0.58  fof(f119,plain,(
% 1.26/0.58    spl4_12 | ~spl4_9),
% 1.26/0.58    inference(avatar_split_clause,[],[f107,f96,f116])).
% 1.26/0.58  fof(f96,plain,(
% 1.26/0.58    spl4_9 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2))),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.26/0.58  fof(f107,plain,(
% 1.26/0.58    k3_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_9),
% 1.26/0.58    inference(superposition,[],[f28,f98])).
% 1.26/0.58  fof(f98,plain,(
% 1.26/0.58    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2)) | ~spl4_9),
% 1.26/0.58    inference(avatar_component_clause,[],[f96])).
% 1.26/0.58  fof(f114,plain,(
% 1.26/0.58    spl4_11 | ~spl4_5),
% 1.26/0.58    inference(avatar_split_clause,[],[f75,f66,f111])).
% 1.26/0.58  fof(f75,plain,(
% 1.26/0.58    k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0) | ~spl4_5),
% 1.26/0.58    inference(forward_demodulation,[],[f72,f25])).
% 1.26/0.58  fof(f72,plain,(
% 1.26/0.58    k3_xboole_0(k10_relat_1(sK0,sK2),sK1) = k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0) | ~spl4_5),
% 1.26/0.58    inference(superposition,[],[f28,f68])).
% 1.26/0.58  fof(f104,plain,(
% 1.26/0.58    ~spl4_10 | ~spl4_1 | spl4_4),
% 1.26/0.58    inference(avatar_split_clause,[],[f90,f61,f43,f101])).
% 1.26/0.58  fof(f43,plain,(
% 1.26/0.58    spl4_1 <=> v1_relat_1(sK0)),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.26/0.58  fof(f61,plain,(
% 1.26/0.58    spl4_4 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.26/0.58  fof(f90,plain,(
% 1.26/0.58    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | (~spl4_1 | spl4_4)),
% 1.26/0.58    inference(superposition,[],[f63,f52])).
% 1.26/0.58  fof(f52,plain,(
% 1.26/0.58    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1))) ) | ~spl4_1),
% 1.26/0.58    inference(resolution,[],[f45,f38])).
% 1.26/0.58  fof(f38,plain,(
% 1.26/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.26/0.58    inference(cnf_transformation,[],[f18])).
% 1.26/0.58  fof(f18,plain,(
% 1.26/0.58    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.26/0.58    inference(ennf_transformation,[],[f10])).
% 1.26/0.58  fof(f10,axiom,(
% 1.26/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.26/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.26/0.58  fof(f45,plain,(
% 1.26/0.58    v1_relat_1(sK0) | ~spl4_1),
% 1.26/0.58    inference(avatar_component_clause,[],[f43])).
% 1.26/0.58  fof(f63,plain,(
% 1.26/0.58    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) | spl4_4),
% 1.26/0.58    inference(avatar_component_clause,[],[f61])).
% 1.26/0.58  fof(f99,plain,(
% 1.26/0.58    spl4_9 | ~spl4_6),
% 1.26/0.58    inference(avatar_split_clause,[],[f91,f77,f96])).
% 1.26/0.58  fof(f77,plain,(
% 1.26/0.58    spl4_6 <=> r1_tarski(k1_xboole_0,k10_relat_1(sK0,sK2))),
% 1.26/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.26/0.58  fof(f91,plain,(
% 1.26/0.58    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k10_relat_1(sK0,sK2)) | ~spl4_6),
% 1.26/0.58    inference(resolution,[],[f79,f35])).
% 1.26/0.58  fof(f79,plain,(
% 1.26/0.58    r1_tarski(k1_xboole_0,k10_relat_1(sK0,sK2)) | ~spl4_6),
% 1.26/0.58    inference(avatar_component_clause,[],[f77])).
% 1.26/0.58  fof(f80,plain,(
% 1.26/0.58    spl4_6 | ~spl4_5),
% 1.26/0.58    inference(avatar_split_clause,[],[f73,f66,f77])).
% 1.26/0.58  fof(f73,plain,(
% 1.26/0.58    r1_tarski(k1_xboole_0,k10_relat_1(sK0,sK2)) | ~spl4_5),
% 1.26/0.58    inference(superposition,[],[f24,f68])).
% 1.26/0.58  fof(f69,plain,(
% 1.26/0.58    spl4_5 | ~spl4_3),
% 1.26/0.58    inference(avatar_split_clause,[],[f58,f54,f66])).
% 1.26/0.58  fof(f58,plain,(
% 1.26/0.58    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1) | ~spl4_3),
% 1.26/0.58    inference(resolution,[],[f56,f35])).
% 1.26/0.58  fof(f64,plain,(
% 1.26/0.58    ~spl4_4),
% 1.26/0.58    inference(avatar_split_clause,[],[f21,f61])).
% 1.26/0.58  fof(f21,plain,(
% 1.26/0.58    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.26/0.58    inference(cnf_transformation,[],[f15])).
% 1.26/0.58  fof(f15,plain,(
% 1.26/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.26/0.58    inference(flattening,[],[f14])).
% 1.26/0.58  fof(f14,plain,(
% 1.26/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.26/0.58    inference(ennf_transformation,[],[f13])).
% 1.26/0.58  fof(f13,negated_conjecture,(
% 1.26/0.58    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.26/0.58    inference(negated_conjecture,[],[f12])).
% 1.26/0.58  fof(f12,conjecture,(
% 1.26/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.26/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 1.26/0.58  fof(f57,plain,(
% 1.26/0.58    spl4_3),
% 1.26/0.58    inference(avatar_split_clause,[],[f20,f54])).
% 1.26/0.58  fof(f20,plain,(
% 1.26/0.58    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.26/0.58    inference(cnf_transformation,[],[f15])).
% 1.26/0.58  fof(f46,plain,(
% 1.26/0.58    spl4_1),
% 1.26/0.58    inference(avatar_split_clause,[],[f22,f43])).
% 1.26/0.58  fof(f22,plain,(
% 1.26/0.58    v1_relat_1(sK0)),
% 1.26/0.58    inference(cnf_transformation,[],[f15])).
% 1.26/0.58  % SZS output end Proof for theBenchmark
% 1.26/0.58  % (4513)------------------------------
% 1.26/0.58  % (4513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.58  % (4513)Termination reason: Refutation
% 1.26/0.58  
% 1.26/0.58  % (4513)Memory used [KB]: 10874
% 1.26/0.58  % (4513)Time elapsed: 0.145 s
% 1.26/0.58  % (4513)------------------------------
% 1.26/0.58  % (4513)------------------------------
% 1.26/0.58  % (4492)Success in time 0.209 s
%------------------------------------------------------------------------------
