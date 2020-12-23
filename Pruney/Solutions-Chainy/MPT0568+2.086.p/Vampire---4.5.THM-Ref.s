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
% DateTime   : Thu Dec  3 12:50:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 233 expanded)
%              Number of leaves         :   41 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  399 ( 583 expanded)
%              Number of equality atoms :  103 ( 169 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f713,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f75,f89,f93,f97,f101,f105,f109,f113,f117,f138,f142,f146,f169,f173,f209,f224,f230,f245,f269,f306,f311,f426,f566,f712])).

fof(f712,plain,
    ( spl1_1
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_10
    | ~ spl1_18
    | ~ spl1_22
    | ~ spl1_28
    | ~ spl1_32
    | ~ spl1_35
    | ~ spl1_36
    | ~ spl1_38
    | ~ spl1_43
    | ~ spl1_48 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | spl1_1
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_10
    | ~ spl1_18
    | ~ spl1_22
    | ~ spl1_28
    | ~ spl1_32
    | ~ spl1_35
    | ~ spl1_36
    | ~ spl1_38
    | ~ spl1_43
    | ~ spl1_48 ),
    inference(subsumption_resolution,[],[f65,f710])).

fof(f710,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_10
    | ~ spl1_18
    | ~ spl1_22
    | ~ spl1_28
    | ~ spl1_32
    | ~ spl1_35
    | ~ spl1_36
    | ~ spl1_38
    | ~ spl1_43
    | ~ spl1_48 ),
    inference(forward_demodulation,[],[f709,f702])).

fof(f702,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_32
    | ~ spl1_48 ),
    inference(superposition,[],[f229,f565])).

fof(f565,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_48 ),
    inference(avatar_component_clause,[],[f563])).

fof(f563,plain,
    ( spl1_48
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_48])])).

fof(f229,plain,
    ( ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0
    | ~ spl1_32 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl1_32
  <=> ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_32])])).

fof(f709,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_10
    | ~ spl1_18
    | ~ spl1_22
    | ~ spl1_28
    | ~ spl1_35
    | ~ spl1_36
    | ~ spl1_38
    | ~ spl1_43
    | ~ spl1_48 ),
    inference(forward_demodulation,[],[f703,f460])).

fof(f460,plain,
    ( ! [X13] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X13)
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_10
    | ~ spl1_18
    | ~ spl1_22
    | ~ spl1_28
    | ~ spl1_35
    | ~ spl1_36
    | ~ spl1_43 ),
    inference(forward_demodulation,[],[f459,f88])).

fof(f88,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl1_6
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f459,plain,
    ( ! [X13] : k4_xboole_0(k1_xboole_0,X13) = k3_xboole_0(k1_xboole_0,X13)
    | ~ spl1_7
    | ~ spl1_10
    | ~ spl1_18
    | ~ spl1_22
    | ~ spl1_28
    | ~ spl1_35
    | ~ spl1_36
    | ~ spl1_43 ),
    inference(forward_demodulation,[],[f458,f260])).

fof(f260,plain,
    ( ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X3,X4)))) = X4
    | ~ spl1_7
    | ~ spl1_10
    | ~ spl1_18
    | ~ spl1_22
    | ~ spl1_28
    | ~ spl1_35 ),
    inference(forward_demodulation,[],[f259,f168])).

fof(f168,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl1_22
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f259,plain,
    ( ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X2,X3),X4))) = X4
    | ~ spl1_7
    | ~ spl1_10
    | ~ spl1_18
    | ~ spl1_22
    | ~ spl1_28
    | ~ spl1_35 ),
    inference(forward_demodulation,[],[f251,f254])).

fof(f254,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl1_7
    | ~ spl1_10
    | ~ spl1_18
    | ~ spl1_28
    | ~ spl1_35 ),
    inference(forward_demodulation,[],[f246,f211])).

fof(f211,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_10
    | ~ spl1_18
    | ~ spl1_28 ),
    inference(forward_demodulation,[],[f210,f104])).

fof(f104,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl1_10
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f210,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0)
    | ~ spl1_18
    | ~ spl1_28 ),
    inference(superposition,[],[f141,f208])).

fof(f208,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl1_28 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl1_28
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).

fof(f141,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl1_18
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f246,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)
    | ~ spl1_7
    | ~ spl1_35 ),
    inference(superposition,[],[f244,f92])).

fof(f92,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl1_7
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f244,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)
    | ~ spl1_35 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl1_35
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).

fof(f251,plain,
    ( ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X2,X3),X4))) = k5_xboole_0(k1_xboole_0,X4)
    | ~ spl1_22
    | ~ spl1_35 ),
    inference(superposition,[],[f244,f168])).

fof(f458,plain,
    ( ! [X12,X13,X11] : k4_xboole_0(k1_xboole_0,X13) = k5_xboole_0(X11,k5_xboole_0(X12,k5_xboole_0(X11,k5_xboole_0(X12,k3_xboole_0(k1_xboole_0,X13)))))
    | ~ spl1_22
    | ~ spl1_36
    | ~ spl1_43 ),
    inference(forward_demodulation,[],[f457,f168])).

fof(f457,plain,
    ( ! [X12,X13,X11] : k4_xboole_0(k1_xboole_0,X13) = k5_xboole_0(X11,k5_xboole_0(X12,k5_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(k1_xboole_0,X13))))
    | ~ spl1_22
    | ~ spl1_36
    | ~ spl1_43 ),
    inference(forward_demodulation,[],[f431,f168])).

fof(f431,plain,
    ( ! [X12,X13,X11] : k4_xboole_0(k1_xboole_0,X13) = k5_xboole_0(X11,k5_xboole_0(k5_xboole_0(X12,k5_xboole_0(X11,X12)),k3_xboole_0(k1_xboole_0,X13)))
    | ~ spl1_36
    | ~ spl1_43 ),
    inference(superposition,[],[f425,f268])).

fof(f268,plain,
    ( ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))
    | ~ spl1_36 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl1_36
  <=> ! [X3,X4] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_36])])).

fof(f425,plain,
    ( ! [X10,X8,X9] : k4_xboole_0(k5_xboole_0(X8,X9),X10) = k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(k5_xboole_0(X8,X9),X10)))
    | ~ spl1_43 ),
    inference(avatar_component_clause,[],[f424])).

fof(f424,plain,
    ( spl1_43
  <=> ! [X9,X8,X10] : k4_xboole_0(k5_xboole_0(X8,X9),X10) = k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(k5_xboole_0(X8,X9),X10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_43])])).

fof(f703,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | ~ spl1_38
    | ~ spl1_48 ),
    inference(superposition,[],[f305,f565])).

fof(f305,plain,
    ( ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl1_38 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl1_38
  <=> ! [X1,X0] : k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_38])])).

fof(f65,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl1_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f566,plain,
    ( spl1_48
    | ~ spl1_2
    | ~ spl1_13
    | ~ spl1_39 ),
    inference(avatar_split_clause,[],[f484,f308,f115,f68,f563])).

fof(f68,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f115,plain,
    ( spl1_13
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | X0 = X1
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f308,plain,
    ( spl1_39
  <=> v1_xboole_0(k6_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_39])])).

fof(f484,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_13
    | ~ spl1_39 ),
    inference(unit_resulting_resolution,[],[f70,f310,f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | ~ v1_xboole_0(X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f310,plain,
    ( v1_xboole_0(k6_relat_1(k1_xboole_0))
    | ~ spl1_39 ),
    inference(avatar_component_clause,[],[f308])).

fof(f70,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f426,plain,
    ( spl1_43
    | ~ spl1_19
    | ~ spl1_22 ),
    inference(avatar_split_clause,[],[f184,f167,f144,f424])).

fof(f144,plain,
    ( spl1_19
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f184,plain,
    ( ! [X10,X8,X9] : k4_xboole_0(k5_xboole_0(X8,X9),X10) = k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(k5_xboole_0(X8,X9),X10)))
    | ~ spl1_19
    | ~ spl1_22 ),
    inference(superposition,[],[f168,f145])).

fof(f145,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl1_19 ),
    inference(avatar_component_clause,[],[f144])).

fof(f311,plain,
    ( spl1_39
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_31 ),
    inference(avatar_split_clause,[],[f225,f222,f73,f68,f308])).

fof(f73,plain,
    ( spl1_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f222,plain,
    ( spl1_31
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | v1_xboole_0(k6_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).

fof(f225,plain,
    ( v1_xboole_0(k6_relat_1(k1_xboole_0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_31 ),
    inference(unit_resulting_resolution,[],[f70,f74,f223])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_xboole_0(X0)
        | v1_xboole_0(k6_relat_1(X0)) )
    | ~ spl1_31 ),
    inference(avatar_component_clause,[],[f222])).

fof(f74,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f306,plain,
    ( spl1_38
    | ~ spl1_3
    | ~ spl1_9
    | ~ spl1_23 ),
    inference(avatar_split_clause,[],[f193,f171,f99,f73,f304])).

fof(f99,plain,
    ( spl1_9
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f171,plain,
    ( spl1_23
  <=> ! [X1,X0] :
        ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f193,plain,
    ( ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl1_3
    | ~ spl1_9
    | ~ spl1_23 ),
    inference(forward_demodulation,[],[f190,f100])).

fof(f100,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f190,plain,
    ( ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),k3_xboole_0(k2_relat_1(k6_relat_1(X0)),X1))
    | ~ spl1_3
    | ~ spl1_23 ),
    inference(unit_resulting_resolution,[],[f74,f172])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
        | ~ v1_relat_1(X1) )
    | ~ spl1_23 ),
    inference(avatar_component_clause,[],[f171])).

fof(f269,plain,
    ( spl1_36
    | ~ spl1_7
    | ~ spl1_22 ),
    inference(avatar_split_clause,[],[f182,f167,f91,f267])).

fof(f182,plain,
    ( ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))
    | ~ spl1_7
    | ~ spl1_22 ),
    inference(superposition,[],[f168,f92])).

fof(f245,plain,
    ( spl1_35
    | ~ spl1_7
    | ~ spl1_22 ),
    inference(avatar_split_clause,[],[f178,f167,f91,f243])).

fof(f178,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)
    | ~ spl1_7
    | ~ spl1_22 ),
    inference(superposition,[],[f168,f92])).

fof(f230,plain,
    ( spl1_32
    | ~ spl1_3
    | ~ spl1_8
    | ~ spl1_9
    | ~ spl1_17 ),
    inference(avatar_split_clause,[],[f155,f136,f99,f95,f73,f228])).

fof(f95,plain,
    ( spl1_8
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f136,plain,
    ( spl1_17
  <=> ! [X0] :
        ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f155,plain,
    ( ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0
    | ~ spl1_3
    | ~ spl1_8
    | ~ spl1_9
    | ~ spl1_17 ),
    inference(forward_demodulation,[],[f154,f96])).

fof(f96,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f154,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)
    | ~ spl1_3
    | ~ spl1_9
    | ~ spl1_17 ),
    inference(forward_demodulation,[],[f151,f100])).

fof(f151,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))
    | ~ spl1_3
    | ~ spl1_17 ),
    inference(unit_resulting_resolution,[],[f74,f137])).

fof(f137,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f136])).

fof(f224,plain,
    ( spl1_31
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f131,f111,f95,f222])).

fof(f111,plain,
    ( spl1_12
  <=> ! [X0] :
        ( ~ v1_xboole_0(k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | v1_xboole_0(k6_relat_1(X0)) )
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(superposition,[],[f112,f96])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f209,plain,
    ( spl1_28
    | ~ spl1_7
    | ~ spl1_11
    | ~ spl1_19 ),
    inference(avatar_split_clause,[],[f165,f144,f107,f91,f207])).

fof(f107,plain,
    ( spl1_11
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f165,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl1_7
    | ~ spl1_11
    | ~ spl1_19 ),
    inference(forward_demodulation,[],[f164,f92])).

fof(f164,plain,
    ( ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)
    | ~ spl1_11
    | ~ spl1_19 ),
    inference(superposition,[],[f145,f108])).

fof(f108,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f173,plain,(
    spl1_23 ),
    inference(avatar_split_clause,[],[f54,f171])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f169,plain,(
    spl1_22 ),
    inference(avatar_split_clause,[],[f57,f167])).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f146,plain,(
    spl1_19 ),
    inference(avatar_split_clause,[],[f53,f144])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f142,plain,(
    spl1_18 ),
    inference(avatar_split_clause,[],[f52,f140])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f138,plain,(
    spl1_17 ),
    inference(avatar_split_clause,[],[f45,f136])).

fof(f45,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f117,plain,(
    spl1_13 ),
    inference(avatar_split_clause,[],[f55,f115])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f113,plain,(
    spl1_12 ),
    inference(avatar_split_clause,[],[f46,f111])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f109,plain,(
    spl1_11 ),
    inference(avatar_split_clause,[],[f48,f107])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f105,plain,(
    spl1_10 ),
    inference(avatar_split_clause,[],[f47,f103])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f101,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f44,f99])).

fof(f44,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f97,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f43,f95])).

fof(f43,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f93,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f42,f91])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f89,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f41,f87])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f75,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f40,f73])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f71,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f37,f68])).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f66,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f36,f63])).

fof(f36,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f34])).

fof(f34,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:21:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (18324)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.46  % (18336)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (18331)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (18321)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (18328)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (18325)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (18322)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (18326)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (18330)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (18323)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (18333)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (18332)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (18334)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (18332)Refutation not found, incomplete strategy% (18332)------------------------------
% 0.22/0.48  % (18332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (18332)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (18332)Memory used [KB]: 10618
% 0.22/0.48  % (18332)Time elapsed: 0.071 s
% 0.22/0.48  % (18332)------------------------------
% 0.22/0.48  % (18332)------------------------------
% 0.22/0.49  % (18329)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (18335)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (18338)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (18326)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f713,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f66,f71,f75,f89,f93,f97,f101,f105,f109,f113,f117,f138,f142,f146,f169,f173,f209,f224,f230,f245,f269,f306,f311,f426,f566,f712])).
% 0.22/0.50  fof(f712,plain,(
% 0.22/0.50    spl1_1 | ~spl1_6 | ~spl1_7 | ~spl1_10 | ~spl1_18 | ~spl1_22 | ~spl1_28 | ~spl1_32 | ~spl1_35 | ~spl1_36 | ~spl1_38 | ~spl1_43 | ~spl1_48),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f711])).
% 0.22/0.50  fof(f711,plain,(
% 0.22/0.50    $false | (spl1_1 | ~spl1_6 | ~spl1_7 | ~spl1_10 | ~spl1_18 | ~spl1_22 | ~spl1_28 | ~spl1_32 | ~spl1_35 | ~spl1_36 | ~spl1_38 | ~spl1_43 | ~spl1_48)),
% 0.22/0.50    inference(subsumption_resolution,[],[f65,f710])).
% 0.22/0.50  fof(f710,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl1_6 | ~spl1_7 | ~spl1_10 | ~spl1_18 | ~spl1_22 | ~spl1_28 | ~spl1_32 | ~spl1_35 | ~spl1_36 | ~spl1_38 | ~spl1_43 | ~spl1_48)),
% 0.22/0.50    inference(forward_demodulation,[],[f709,f702])).
% 0.22/0.50  fof(f702,plain,(
% 0.22/0.50    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_32 | ~spl1_48)),
% 0.22/0.50    inference(superposition,[],[f229,f565])).
% 0.22/0.50  fof(f565,plain,(
% 0.22/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_48),
% 0.22/0.50    inference(avatar_component_clause,[],[f563])).
% 0.22/0.50  fof(f563,plain,(
% 0.22/0.50    spl1_48 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_48])])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) ) | ~spl1_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f228])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    spl1_32 <=> ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_32])])).
% 0.22/0.50  fof(f709,plain,(
% 0.22/0.50    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)) ) | (~spl1_6 | ~spl1_7 | ~spl1_10 | ~spl1_18 | ~spl1_22 | ~spl1_28 | ~spl1_35 | ~spl1_36 | ~spl1_38 | ~spl1_43 | ~spl1_48)),
% 0.22/0.50    inference(forward_demodulation,[],[f703,f460])).
% 0.22/0.50  fof(f460,plain,(
% 0.22/0.50    ( ! [X13] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X13)) ) | (~spl1_6 | ~spl1_7 | ~spl1_10 | ~spl1_18 | ~spl1_22 | ~spl1_28 | ~spl1_35 | ~spl1_36 | ~spl1_43)),
% 0.22/0.50    inference(forward_demodulation,[],[f459,f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl1_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f87])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    spl1_6 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.50  fof(f459,plain,(
% 0.22/0.50    ( ! [X13] : (k4_xboole_0(k1_xboole_0,X13) = k3_xboole_0(k1_xboole_0,X13)) ) | (~spl1_7 | ~spl1_10 | ~spl1_18 | ~spl1_22 | ~spl1_28 | ~spl1_35 | ~spl1_36 | ~spl1_43)),
% 0.22/0.50    inference(forward_demodulation,[],[f458,f260])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X3,X4)))) = X4) ) | (~spl1_7 | ~spl1_10 | ~spl1_18 | ~spl1_22 | ~spl1_28 | ~spl1_35)),
% 0.22/0.50    inference(forward_demodulation,[],[f259,f168])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl1_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f167])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    spl1_22 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X2,X3),X4))) = X4) ) | (~spl1_7 | ~spl1_10 | ~spl1_18 | ~spl1_22 | ~spl1_28 | ~spl1_35)),
% 0.22/0.50    inference(forward_demodulation,[],[f251,f254])).
% 0.22/0.50  fof(f254,plain,(
% 0.22/0.50    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl1_7 | ~spl1_10 | ~spl1_18 | ~spl1_28 | ~spl1_35)),
% 0.22/0.50    inference(forward_demodulation,[],[f246,f211])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl1_10 | ~spl1_18 | ~spl1_28)),
% 0.22/0.50    inference(forward_demodulation,[],[f210,f104])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl1_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl1_10 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0)) ) | (~spl1_18 | ~spl1_28)),
% 0.22/0.50    inference(superposition,[],[f141,f208])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl1_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f207])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    spl1_28 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl1_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f140])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    spl1_18 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.22/0.50  fof(f246,plain,(
% 0.22/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) ) | (~spl1_7 | ~spl1_35)),
% 0.22/0.50    inference(superposition,[],[f244,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl1_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl1_7 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) ) | ~spl1_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f243])).
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    spl1_35 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X2,X3),X4))) = k5_xboole_0(k1_xboole_0,X4)) ) | (~spl1_22 | ~spl1_35)),
% 0.22/0.50    inference(superposition,[],[f244,f168])).
% 0.22/0.50  fof(f458,plain,(
% 0.22/0.50    ( ! [X12,X13,X11] : (k4_xboole_0(k1_xboole_0,X13) = k5_xboole_0(X11,k5_xboole_0(X12,k5_xboole_0(X11,k5_xboole_0(X12,k3_xboole_0(k1_xboole_0,X13)))))) ) | (~spl1_22 | ~spl1_36 | ~spl1_43)),
% 0.22/0.50    inference(forward_demodulation,[],[f457,f168])).
% 0.22/0.50  fof(f457,plain,(
% 0.22/0.50    ( ! [X12,X13,X11] : (k4_xboole_0(k1_xboole_0,X13) = k5_xboole_0(X11,k5_xboole_0(X12,k5_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(k1_xboole_0,X13))))) ) | (~spl1_22 | ~spl1_36 | ~spl1_43)),
% 0.22/0.50    inference(forward_demodulation,[],[f431,f168])).
% 0.22/0.50  fof(f431,plain,(
% 0.22/0.50    ( ! [X12,X13,X11] : (k4_xboole_0(k1_xboole_0,X13) = k5_xboole_0(X11,k5_xboole_0(k5_xboole_0(X12,k5_xboole_0(X11,X12)),k3_xboole_0(k1_xboole_0,X13)))) ) | (~spl1_36 | ~spl1_43)),
% 0.22/0.50    inference(superposition,[],[f425,f268])).
% 0.22/0.50  fof(f268,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) ) | ~spl1_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f267])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    spl1_36 <=> ! [X3,X4] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_36])])).
% 0.22/0.50  fof(f425,plain,(
% 0.22/0.50    ( ! [X10,X8,X9] : (k4_xboole_0(k5_xboole_0(X8,X9),X10) = k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(k5_xboole_0(X8,X9),X10)))) ) | ~spl1_43),
% 0.22/0.50    inference(avatar_component_clause,[],[f424])).
% 0.22/0.50  fof(f424,plain,(
% 0.22/0.50    spl1_43 <=> ! [X9,X8,X10] : k4_xboole_0(k5_xboole_0(X8,X9),X10) = k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(k5_xboole_0(X8,X9),X10)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_43])])).
% 0.22/0.50  fof(f703,plain,(
% 0.22/0.50    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ) | (~spl1_38 | ~spl1_48)),
% 0.22/0.50    inference(superposition,[],[f305,f565])).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | ~spl1_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f304])).
% 0.22/0.50  fof(f304,plain,(
% 0.22/0.50    spl1_38 <=> ! [X1,X0] : k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_38])])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl1_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.50  fof(f566,plain,(
% 0.22/0.50    spl1_48 | ~spl1_2 | ~spl1_13 | ~spl1_39),
% 0.22/0.50    inference(avatar_split_clause,[],[f484,f308,f115,f68,f563])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    spl1_13 <=> ! [X1,X0] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.22/0.50  fof(f308,plain,(
% 0.22/0.50    spl1_39 <=> v1_xboole_0(k6_relat_1(k1_xboole_0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_39])])).
% 0.22/0.50  fof(f484,plain,(
% 0.22/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_13 | ~spl1_39)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f70,f310,f116])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    ( ! [X0,X1] : (X0 = X1 | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) ) | ~spl1_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f115])).
% 0.22/0.50  fof(f310,plain,(
% 0.22/0.50    v1_xboole_0(k6_relat_1(k1_xboole_0)) | ~spl1_39),
% 0.22/0.50    inference(avatar_component_clause,[],[f308])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f68])).
% 0.22/0.50  fof(f426,plain,(
% 0.22/0.50    spl1_43 | ~spl1_19 | ~spl1_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f184,f167,f144,f424])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    spl1_19 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    ( ! [X10,X8,X9] : (k4_xboole_0(k5_xboole_0(X8,X9),X10) = k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(k5_xboole_0(X8,X9),X10)))) ) | (~spl1_19 | ~spl1_22)),
% 0.22/0.50    inference(superposition,[],[f168,f145])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl1_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f144])).
% 0.22/0.50  fof(f311,plain,(
% 0.22/0.50    spl1_39 | ~spl1_2 | ~spl1_3 | ~spl1_31),
% 0.22/0.50    inference(avatar_split_clause,[],[f225,f222,f73,f68,f308])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl1_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    spl1_31 <=> ! [X0] : (~v1_xboole_0(X0) | ~v1_relat_1(k6_relat_1(X0)) | v1_xboole_0(k6_relat_1(X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    v1_xboole_0(k6_relat_1(k1_xboole_0)) | (~spl1_2 | ~spl1_3 | ~spl1_31)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f70,f74,f223])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(k6_relat_1(X0))) ) | ~spl1_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f222])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f73])).
% 0.22/0.50  fof(f306,plain,(
% 0.22/0.50    spl1_38 | ~spl1_3 | ~spl1_9 | ~spl1_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f193,f171,f99,f73,f304])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl1_9 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    spl1_23 <=> ! [X1,X0] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | (~spl1_3 | ~spl1_9 | ~spl1_23)),
% 0.22/0.50    inference(forward_demodulation,[],[f190,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl1_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),k3_xboole_0(k2_relat_1(k6_relat_1(X0)),X1))) ) | (~spl1_3 | ~spl1_23)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f74,f172])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) ) | ~spl1_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f171])).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    spl1_36 | ~spl1_7 | ~spl1_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f182,f167,f91,f267])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) ) | (~spl1_7 | ~spl1_22)),
% 0.22/0.50    inference(superposition,[],[f168,f92])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    spl1_35 | ~spl1_7 | ~spl1_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f178,f167,f91,f243])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) ) | (~spl1_7 | ~spl1_22)),
% 0.22/0.50    inference(superposition,[],[f168,f92])).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    spl1_32 | ~spl1_3 | ~spl1_8 | ~spl1_9 | ~spl1_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f155,f136,f99,f95,f73,f228])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl1_8 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl1_17 <=> ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) ) | (~spl1_3 | ~spl1_8 | ~spl1_9 | ~spl1_17)),
% 0.22/0.50    inference(forward_demodulation,[],[f154,f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl1_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f95])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) ) | (~spl1_3 | ~spl1_9 | ~spl1_17)),
% 0.22/0.50    inference(forward_demodulation,[],[f151,f100])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) ) | (~spl1_3 | ~spl1_17)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f74,f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl1_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f136])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    spl1_31 | ~spl1_8 | ~spl1_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f131,f111,f95,f222])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl1_12 <=> ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(X0) | ~v1_relat_1(k6_relat_1(X0)) | v1_xboole_0(k6_relat_1(X0))) ) | (~spl1_8 | ~spl1_12)),
% 0.22/0.50    inference(superposition,[],[f112,f96])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) ) | ~spl1_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f111])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    spl1_28 | ~spl1_7 | ~spl1_11 | ~spl1_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f165,f144,f107,f91,f207])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    spl1_11 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl1_7 | ~spl1_11 | ~spl1_19)),
% 0.22/0.50    inference(forward_demodulation,[],[f164,f92])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) ) | (~spl1_11 | ~spl1_19)),
% 0.22/0.50    inference(superposition,[],[f145,f108])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl1_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f107])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    spl1_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f54,f171])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    spl1_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f57,f167])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    spl1_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f53,f144])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    spl1_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f52,f140])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl1_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f45,f136])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    spl1_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f55,f115])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl1_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f46,f111])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,axiom,(
% 0.22/0.50    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl1_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f48,f107])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.50    inference(rectify,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl1_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f47,f103])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.50    inference(rectify,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl1_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f44,f99])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,axiom,(
% 0.22/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl1_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f43,f95])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl1_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f42,f91])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl1_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f87])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl1_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f73])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,axiom,(
% 0.22/0.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    spl1_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f68])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ~spl1_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f36,f63])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,negated_conjecture,(
% 0.22/0.50    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.50    inference(negated_conjecture,[],[f24])).
% 0.22/0.50  fof(f24,conjecture,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (18326)------------------------------
% 0.22/0.50  % (18326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18326)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (18326)Memory used [KB]: 6652
% 0.22/0.50  % (18326)Time elapsed: 0.088 s
% 0.22/0.50  % (18326)------------------------------
% 0.22/0.50  % (18326)------------------------------
% 0.22/0.50  % (18320)Success in time 0.142 s
%------------------------------------------------------------------------------
