%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 196 expanded)
%              Number of leaves         :   30 (  99 expanded)
%              Depth                    :    6
%              Number of atoms          :  294 ( 524 expanded)
%              Number of equality atoms :   75 ( 138 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f538,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f43,f47,f51,f55,f59,f67,f76,f83,f91,f98,f120,f146,f165,f210,f227,f344,f476,f499,f531,f537])).

fof(f537,plain,
    ( spl2_1
    | ~ spl2_37
    | ~ spl2_84 ),
    inference(avatar_contradiction_clause,[],[f536])).

fof(f536,plain,
    ( $false
    | spl2_1
    | ~ spl2_37
    | ~ spl2_84 ),
    inference(subsumption_resolution,[],[f533,f28])).

fof(f28,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_1
  <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f533,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ spl2_37
    | ~ spl2_84 ),
    inference(superposition,[],[f225,f530])).

fof(f530,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))))
    | ~ spl2_84 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl2_84
  <=> k10_relat_1(sK0,k1_relat_1(sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).

fof(f225,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl2_37
  <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f531,plain,
    ( spl2_84
    | ~ spl2_9
    | ~ spl2_15
    | ~ spl2_80 ),
    inference(avatar_split_clause,[],[f526,f496,f95,f64,f528])).

fof(f64,plain,
    ( spl2_9
  <=> k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f95,plain,
    ( spl2_15
  <=> ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(X0,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f496,plain,
    ( spl2_80
  <=> ! [X1] : k10_relat_1(sK0,k10_relat_1(sK1,X1)) = k10_relat_1(sK0,k10_relat_1(sK1,k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f526,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))))
    | ~ spl2_9
    | ~ spl2_15
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f525,f66])).

fof(f66,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f525,plain,
    ( k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl2_15
    | ~ spl2_80 ),
    inference(superposition,[],[f497,f96])).

fof(f96,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(X0,k2_relat_1(sK1)))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f497,plain,
    ( ! [X1] : k10_relat_1(sK0,k10_relat_1(sK1,X1)) = k10_relat_1(sK0,k10_relat_1(sK1,k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X1)))
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f496])).

fof(f499,plain,
    ( spl2_80
    | ~ spl2_23
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f489,f474,f144,f496])).

fof(f144,plain,
    ( spl2_23
  <=> ! [X0] : k10_relat_1(k5_relat_1(sK0,sK1),X0) = k10_relat_1(sK0,k10_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f474,plain,
    ( spl2_76
  <=> ! [X0] : k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f489,plain,
    ( ! [X0] : k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(sK0,k10_relat_1(sK1,k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X0)))
    | ~ spl2_23
    | ~ spl2_76 ),
    inference(superposition,[],[f145,f475])).

fof(f475,plain,
    ( ! [X0] : k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X0))
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f474])).

fof(f145,plain,
    ( ! [X0] : k10_relat_1(k5_relat_1(sK0,sK1),X0) = k10_relat_1(sK0,k10_relat_1(sK1,X0))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f144])).

fof(f476,plain,
    ( spl2_76
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_58 ),
    inference(avatar_split_clause,[],[f472,f342,f144,f31,f474])).

fof(f31,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f342,plain,
    ( spl2_58
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(k5_relat_1(sK0,X2),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,X2)),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f472,plain,
    ( ! [X0] : k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X0))
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_58 ),
    inference(forward_demodulation,[],[f469,f145])).

fof(f469,plain,
    ( ! [X0] : k10_relat_1(k5_relat_1(sK0,sK1),X0) = k10_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X0))
    | ~ spl2_2
    | ~ spl2_58 ),
    inference(resolution,[],[f343,f33])).

fof(f33,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f343,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(k5_relat_1(sK0,X2),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,X2)),X3)) )
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f342])).

fof(f344,plain,
    ( spl2_58
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f335,f89,f36,f342])).

fof(f36,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f89,plain,
    ( spl2_14
  <=> ! [X3,X2,X4] :
        ( k10_relat_1(k5_relat_1(X2,X3),X4) = k10_relat_1(k5_relat_1(X2,X3),k3_xboole_0(k2_relat_1(k5_relat_1(X2,X3)),X4))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f335,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(k5_relat_1(sK0,X2),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,X2)),X3)) )
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(resolution,[],[f90,f38])).

fof(f38,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f90,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | k10_relat_1(k5_relat_1(X2,X3),X4) = k10_relat_1(k5_relat_1(X2,X3),k3_xboole_0(k2_relat_1(k5_relat_1(X2,X3)),X4)) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f227,plain,
    ( spl2_37
    | ~ spl2_23
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f221,f207,f144,f223])).

fof(f207,plain,
    ( spl2_34
  <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f221,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))))
    | ~ spl2_23
    | ~ spl2_34 ),
    inference(superposition,[],[f145,f209])).

fof(f209,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f207])).

fof(f210,plain,
    ( spl2_34
    | ~ spl2_2
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f203,f163,f31,f207])).

fof(f163,plain,
    ( spl2_27
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(sK0,X1)) = k10_relat_1(k5_relat_1(sK0,X1),k2_relat_1(k5_relat_1(sK0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f203,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_27 ),
    inference(resolution,[],[f164,f33])).

fof(f164,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(sK0,X1)) = k10_relat_1(k5_relat_1(sK0,X1),k2_relat_1(k5_relat_1(sK0,X1))) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f163])).

fof(f165,plain,
    ( spl2_27
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f156,f74,f36,f163])).

fof(f74,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f156,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(sK0,X1)) = k10_relat_1(k5_relat_1(sK0,X1),k2_relat_1(k5_relat_1(sK0,X1))) )
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(resolution,[],[f75,f38])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1))) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f146,plain,
    ( spl2_23
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f140,f118,f31,f144])).

fof(f118,plain,
    ( spl2_18
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(sK0,k10_relat_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f140,plain,
    ( ! [X0] : k10_relat_1(k5_relat_1(sK0,sK1),X0) = k10_relat_1(sK0,k10_relat_1(sK1,X0))
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(resolution,[],[f119,f33])).

fof(f119,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(sK0,k10_relat_1(X2,X3)) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f111,f53,f36,f118])).

fof(f53,plain,
    ( spl2_7
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f111,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(sK0,k10_relat_1(X2,X3)) )
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f54,f38])).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f98,plain,
    ( spl2_15
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f93,f81,f45,f95])).

fof(f45,plain,
    ( spl2_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f81,plain,
    ( spl2_12
  <=> ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f93,plain,
    ( ! [X1] : k10_relat_1(sK1,X1) = k10_relat_1(sK1,k3_xboole_0(X1,k2_relat_1(sK1)))
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(superposition,[],[f82,f46])).

fof(f46,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f82,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f91,plain,
    ( spl2_14
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f79,f57,f49,f89])).

fof(f49,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f57,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f79,plain,
    ( ! [X4,X2,X3] :
        ( k10_relat_1(k5_relat_1(X2,X3),X4) = k10_relat_1(k5_relat_1(X2,X3),k3_xboole_0(k2_relat_1(k5_relat_1(X2,X3)),X4))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(resolution,[],[f50,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f83,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f77,f49,f31,f81])).

fof(f77,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f50,f33])).

fof(f76,plain,
    ( spl2_11
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f62,f57,f41,f74])).

fof(f41,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(resolution,[],[f42,f58])).

fof(f42,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f67,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f60,f41,f31,f64])).

fof(f60,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f42,f33])).

fof(f59,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f55,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f51,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f47,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f43,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f39,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f34,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f31])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f19,f26])).

fof(f19,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (18378)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (18379)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.44  % (18380)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.44  % (18377)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.44  % (18374)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.44  % (18376)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.45  % (18373)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.45  % (18375)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.46  % (18377)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f538,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f29,f34,f39,f43,f47,f51,f55,f59,f67,f76,f83,f91,f98,f120,f146,f165,f210,f227,f344,f476,f499,f531,f537])).
% 0.20/0.46  fof(f537,plain,(
% 0.20/0.46    spl2_1 | ~spl2_37 | ~spl2_84),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f536])).
% 0.20/0.46  fof(f536,plain,(
% 0.20/0.46    $false | (spl2_1 | ~spl2_37 | ~spl2_84)),
% 0.20/0.46    inference(subsumption_resolution,[],[f533,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) | spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    spl2_1 <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f533,plain,(
% 0.20/0.46    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) | (~spl2_37 | ~spl2_84)),
% 0.20/0.46    inference(superposition,[],[f225,f530])).
% 0.20/0.46  fof(f530,plain,(
% 0.20/0.46    k10_relat_1(sK0,k1_relat_1(sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) | ~spl2_84),
% 0.20/0.46    inference(avatar_component_clause,[],[f528])).
% 0.20/0.46  fof(f528,plain,(
% 0.20/0.46    spl2_84 <=> k10_relat_1(sK0,k1_relat_1(sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).
% 0.20/0.46  fof(f225,plain,(
% 0.20/0.46    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) | ~spl2_37),
% 0.20/0.46    inference(avatar_component_clause,[],[f223])).
% 0.20/0.46  fof(f223,plain,(
% 0.20/0.46    spl2_37 <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.20/0.46  fof(f531,plain,(
% 0.20/0.46    spl2_84 | ~spl2_9 | ~spl2_15 | ~spl2_80),
% 0.20/0.46    inference(avatar_split_clause,[],[f526,f496,f95,f64,f528])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    spl2_9 <=> k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    spl2_15 <=> ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(X0,k2_relat_1(sK1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.46  fof(f496,plain,(
% 0.20/0.46    spl2_80 <=> ! [X1] : k10_relat_1(sK0,k10_relat_1(sK1,X1)) = k10_relat_1(sK0,k10_relat_1(sK1,k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 0.20/0.46  fof(f526,plain,(
% 0.20/0.46    k10_relat_1(sK0,k1_relat_1(sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) | (~spl2_9 | ~spl2_15 | ~spl2_80)),
% 0.20/0.46    inference(forward_demodulation,[],[f525,f66])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) | ~spl2_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f64])).
% 0.20/0.46  fof(f525,plain,(
% 0.20/0.46    k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(sK1))) | (~spl2_15 | ~spl2_80)),
% 0.20/0.46    inference(superposition,[],[f497,f96])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(X0,k2_relat_1(sK1)))) ) | ~spl2_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f95])).
% 0.20/0.46  fof(f497,plain,(
% 0.20/0.46    ( ! [X1] : (k10_relat_1(sK0,k10_relat_1(sK1,X1)) = k10_relat_1(sK0,k10_relat_1(sK1,k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X1)))) ) | ~spl2_80),
% 0.20/0.46    inference(avatar_component_clause,[],[f496])).
% 0.20/0.46  fof(f499,plain,(
% 0.20/0.46    spl2_80 | ~spl2_23 | ~spl2_76),
% 0.20/0.46    inference(avatar_split_clause,[],[f489,f474,f144,f496])).
% 0.20/0.46  fof(f144,plain,(
% 0.20/0.46    spl2_23 <=> ! [X0] : k10_relat_1(k5_relat_1(sK0,sK1),X0) = k10_relat_1(sK0,k10_relat_1(sK1,X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.20/0.46  fof(f474,plain,(
% 0.20/0.46    spl2_76 <=> ! [X0] : k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 0.20/0.46  fof(f489,plain,(
% 0.20/0.46    ( ! [X0] : (k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(sK0,k10_relat_1(sK1,k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X0)))) ) | (~spl2_23 | ~spl2_76)),
% 0.20/0.46    inference(superposition,[],[f145,f475])).
% 0.20/0.46  fof(f475,plain,(
% 0.20/0.46    ( ! [X0] : (k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X0))) ) | ~spl2_76),
% 0.20/0.46    inference(avatar_component_clause,[],[f474])).
% 0.20/0.46  fof(f145,plain,(
% 0.20/0.46    ( ! [X0] : (k10_relat_1(k5_relat_1(sK0,sK1),X0) = k10_relat_1(sK0,k10_relat_1(sK1,X0))) ) | ~spl2_23),
% 0.20/0.46    inference(avatar_component_clause,[],[f144])).
% 0.20/0.46  fof(f476,plain,(
% 0.20/0.46    spl2_76 | ~spl2_2 | ~spl2_23 | ~spl2_58),
% 0.20/0.46    inference(avatar_split_clause,[],[f472,f342,f144,f31,f474])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    spl2_2 <=> v1_relat_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f342,plain,(
% 0.20/0.46    spl2_58 <=> ! [X3,X2] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(k5_relat_1(sK0,X2),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,X2)),X3)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 0.20/0.46  fof(f472,plain,(
% 0.20/0.46    ( ! [X0] : (k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X0))) ) | (~spl2_2 | ~spl2_23 | ~spl2_58)),
% 0.20/0.46    inference(forward_demodulation,[],[f469,f145])).
% 0.20/0.46  fof(f469,plain,(
% 0.20/0.46    ( ! [X0] : (k10_relat_1(k5_relat_1(sK0,sK1),X0) = k10_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,sK1)),X0))) ) | (~spl2_2 | ~spl2_58)),
% 0.20/0.46    inference(resolution,[],[f343,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f31])).
% 0.20/0.46  fof(f343,plain,(
% 0.20/0.46    ( ! [X2,X3] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(k5_relat_1(sK0,X2),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,X2)),X3))) ) | ~spl2_58),
% 0.20/0.46    inference(avatar_component_clause,[],[f342])).
% 0.20/0.46  fof(f344,plain,(
% 0.20/0.46    spl2_58 | ~spl2_3 | ~spl2_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f335,f89,f36,f342])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    spl2_3 <=> v1_relat_1(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    spl2_14 <=> ! [X3,X2,X4] : (k10_relat_1(k5_relat_1(X2,X3),X4) = k10_relat_1(k5_relat_1(X2,X3),k3_xboole_0(k2_relat_1(k5_relat_1(X2,X3)),X4)) | ~v1_relat_1(X3) | ~v1_relat_1(X2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.46  fof(f335,plain,(
% 0.20/0.46    ( ! [X2,X3] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(k5_relat_1(sK0,X2),k3_xboole_0(k2_relat_1(k5_relat_1(sK0,X2)),X3))) ) | (~spl2_3 | ~spl2_14)),
% 0.20/0.46    inference(resolution,[],[f90,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    v1_relat_1(sK0) | ~spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f36])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k10_relat_1(k5_relat_1(X2,X3),X4) = k10_relat_1(k5_relat_1(X2,X3),k3_xboole_0(k2_relat_1(k5_relat_1(X2,X3)),X4))) ) | ~spl2_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f89])).
% 0.20/0.46  fof(f227,plain,(
% 0.20/0.46    spl2_37 | ~spl2_23 | ~spl2_34),
% 0.20/0.46    inference(avatar_split_clause,[],[f221,f207,f144,f223])).
% 0.20/0.46  fof(f207,plain,(
% 0.20/0.46    spl2_34 <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.46  fof(f221,plain,(
% 0.20/0.46    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) | (~spl2_23 | ~spl2_34)),
% 0.20/0.46    inference(superposition,[],[f145,f209])).
% 0.20/0.46  fof(f209,plain,(
% 0.20/0.46    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1))) | ~spl2_34),
% 0.20/0.46    inference(avatar_component_clause,[],[f207])).
% 0.20/0.46  fof(f210,plain,(
% 0.20/0.46    spl2_34 | ~spl2_2 | ~spl2_27),
% 0.20/0.46    inference(avatar_split_clause,[],[f203,f163,f31,f207])).
% 0.20/0.46  fof(f163,plain,(
% 0.20/0.46    spl2_27 <=> ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(sK0,X1)) = k10_relat_1(k5_relat_1(sK0,X1),k2_relat_1(k5_relat_1(sK0,X1))))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.20/0.46  fof(f203,plain,(
% 0.20/0.46    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1))) | (~spl2_2 | ~spl2_27)),
% 0.20/0.46    inference(resolution,[],[f164,f33])).
% 0.20/0.46  fof(f164,plain,(
% 0.20/0.46    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(sK0,X1)) = k10_relat_1(k5_relat_1(sK0,X1),k2_relat_1(k5_relat_1(sK0,X1)))) ) | ~spl2_27),
% 0.20/0.46    inference(avatar_component_clause,[],[f163])).
% 0.20/0.46  fof(f165,plain,(
% 0.20/0.46    spl2_27 | ~spl2_3 | ~spl2_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f156,f74,f36,f163])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    spl2_11 <=> ! [X1,X0] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.46  fof(f156,plain,(
% 0.20/0.46    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(sK0,X1)) = k10_relat_1(k5_relat_1(sK0,X1),k2_relat_1(k5_relat_1(sK0,X1)))) ) | (~spl2_3 | ~spl2_11)),
% 0.20/0.46    inference(resolution,[],[f75,f38])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1)))) ) | ~spl2_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f74])).
% 0.20/0.46  fof(f146,plain,(
% 0.20/0.46    spl2_23 | ~spl2_2 | ~spl2_18),
% 0.20/0.46    inference(avatar_split_clause,[],[f140,f118,f31,f144])).
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    spl2_18 <=> ! [X3,X2] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(sK0,k10_relat_1(X2,X3)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.46  fof(f140,plain,(
% 0.20/0.46    ( ! [X0] : (k10_relat_1(k5_relat_1(sK0,sK1),X0) = k10_relat_1(sK0,k10_relat_1(sK1,X0))) ) | (~spl2_2 | ~spl2_18)),
% 0.20/0.46    inference(resolution,[],[f119,f33])).
% 0.20/0.46  fof(f119,plain,(
% 0.20/0.46    ( ! [X2,X3] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(sK0,k10_relat_1(X2,X3))) ) | ~spl2_18),
% 0.20/0.46    inference(avatar_component_clause,[],[f118])).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    spl2_18 | ~spl2_3 | ~spl2_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f111,f53,f36,f118])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    spl2_7 <=> ! [X1,X0,X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    ( ! [X2,X3] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(sK0,k10_relat_1(X2,X3))) ) | (~spl2_3 | ~spl2_7)),
% 0.20/0.46    inference(resolution,[],[f54,f38])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) ) | ~spl2_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f53])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    spl2_15 | ~spl2_5 | ~spl2_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f93,f81,f45,f95])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    spl2_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    spl2_12 <=> ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    ( ! [X1] : (k10_relat_1(sK1,X1) = k10_relat_1(sK1,k3_xboole_0(X1,k2_relat_1(sK1)))) ) | (~spl2_5 | ~spl2_12)),
% 0.20/0.46    inference(superposition,[],[f82,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f45])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))) ) | ~spl2_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f81])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    spl2_14 | ~spl2_6 | ~spl2_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f79,f57,f49,f89])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    spl2_6 <=> ! [X1,X0] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    spl2_8 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    ( ! [X4,X2,X3] : (k10_relat_1(k5_relat_1(X2,X3),X4) = k10_relat_1(k5_relat_1(X2,X3),k3_xboole_0(k2_relat_1(k5_relat_1(X2,X3)),X4)) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) ) | (~spl2_6 | ~spl2_8)),
% 0.20/0.46    inference(resolution,[],[f50,f58])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f57])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) ) | ~spl2_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f49])).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    spl2_12 | ~spl2_2 | ~spl2_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f77,f49,f31,f81])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))) ) | (~spl2_2 | ~spl2_6)),
% 0.20/0.46    inference(resolution,[],[f50,f33])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    spl2_11 | ~spl2_4 | ~spl2_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f62,f57,f41,f74])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    spl2_4 <=> ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | (~spl2_4 | ~spl2_8)),
% 0.20/0.46    inference(resolution,[],[f42,f58])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) ) | ~spl2_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f41])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl2_9 | ~spl2_2 | ~spl2_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f60,f41,f31,f64])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) | (~spl2_2 | ~spl2_4)),
% 0.20/0.47    inference(resolution,[],[f42,f33])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl2_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f24,f57])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl2_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f23,f53])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    spl2_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f49])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    spl2_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f21,f45])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl2_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f41])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl2_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f17,f36])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    v1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    (k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f15,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X1] : (k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f6])).
% 0.20/0.47  fof(f6,conjecture,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f31])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ~spl2_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f26])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (18377)------------------------------
% 0.20/0.47  % (18377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (18377)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (18377)Memory used [KB]: 10874
% 0.20/0.47  % (18377)Time elapsed: 0.045 s
% 0.20/0.47  % (18377)------------------------------
% 0.20/0.47  % (18377)------------------------------
% 0.20/0.47  % (18371)Success in time 0.112 s
%------------------------------------------------------------------------------
