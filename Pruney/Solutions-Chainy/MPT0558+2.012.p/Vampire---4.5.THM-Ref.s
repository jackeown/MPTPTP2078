%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 193 expanded)
%              Number of leaves         :   31 (  96 expanded)
%              Depth                    :    6
%              Number of atoms          :  317 ( 544 expanded)
%              Number of equality atoms :   73 ( 125 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f532,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f47,f51,f55,f59,f63,f67,f80,f84,f89,f104,f115,f141,f160,f189,f209,f254,f388,f500,f518,f531])).

fof(f531,plain,
    ( spl2_1
    | ~ spl2_43
    | ~ spl2_86 ),
    inference(avatar_contradiction_clause,[],[f530])).

fof(f530,plain,
    ( $false
    | spl2_1
    | ~ spl2_43
    | ~ spl2_86 ),
    inference(subsumption_resolution,[],[f526,f32])).

fof(f32,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_1
  <=> k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f526,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))
    | ~ spl2_43
    | ~ spl2_86 ),
    inference(superposition,[],[f253,f517])).

fof(f517,plain,
    ( k9_relat_1(sK1,k2_relat_1(sK0)) = k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_86 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl2_86
  <=> k9_relat_1(sK1,k2_relat_1(sK0)) = k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).

fof(f253,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl2_43
  <=> k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f518,plain,
    ( spl2_86
    | ~ spl2_11
    | ~ spl2_32
    | ~ spl2_83 ),
    inference(avatar_split_clause,[],[f513,f498,f186,f77,f515])).

fof(f77,plain,
    ( spl2_11
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f186,plain,
    ( spl2_32
  <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f498,plain,
    ( spl2_83
  <=> ! [X0] : k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k9_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).

fof(f513,plain,
    ( k9_relat_1(sK1,k2_relat_1(sK0)) = k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_11
    | ~ spl2_32
    | ~ spl2_83 ),
    inference(forward_demodulation,[],[f510,f79])).

fof(f79,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f510,plain,
    ( k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1))) = k9_relat_1(sK1,k9_relat_1(sK0,k1_relat_1(sK0)))
    | ~ spl2_32
    | ~ spl2_83 ),
    inference(superposition,[],[f499,f188])).

fof(f188,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f186])).

fof(f499,plain,
    ( ! [X0] : k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k9_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),X0))
    | ~ spl2_83 ),
    inference(avatar_component_clause,[],[f498])).

fof(f500,plain,
    ( spl2_83
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_67 ),
    inference(avatar_split_clause,[],[f496,f386,f139,f35,f498])).

fof(f35,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f139,plain,
    ( spl2_23
  <=> ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f386,plain,
    ( spl2_67
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(k5_relat_1(sK0,X2),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,X2)),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f496,plain,
    ( ! [X0] : k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k9_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),X0))
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_67 ),
    inference(forward_demodulation,[],[f493,f140])).

fof(f140,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f139])).

fof(f493,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),X0))
    | ~ spl2_2
    | ~ spl2_67 ),
    inference(resolution,[],[f387,f37])).

fof(f37,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f387,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(k5_relat_1(sK0,X2),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,X2)),X3)) )
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f386])).

fof(f388,plain,
    ( spl2_67
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f379,f102,f40,f386])).

fof(f40,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f102,plain,
    ( spl2_16
  <=> ! [X3,X2,X4] :
        ( k9_relat_1(k5_relat_1(X2,X3),X4) = k9_relat_1(k5_relat_1(X2,X3),k3_xboole_0(k1_relat_1(k5_relat_1(X2,X3)),X4))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f379,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(k5_relat_1(sK0,X2),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,X2)),X3)) )
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(resolution,[],[f103,f42])).

fof(f42,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f103,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | k9_relat_1(k5_relat_1(X2,X3),X4) = k9_relat_1(k5_relat_1(X2,X3),k3_xboole_0(k1_relat_1(k5_relat_1(X2,X3)),X4)) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f102])).

fof(f254,plain,
    ( spl2_43
    | ~ spl2_2
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f247,f207,f35,f251])).

fof(f207,plain,
    ( spl2_36
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k5_relat_1(sK0,X1)) = k9_relat_1(k5_relat_1(sK0,X1),k1_relat_1(k5_relat_1(sK0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f247,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_36 ),
    inference(resolution,[],[f208,f37])).

fof(f208,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k5_relat_1(sK0,X1)) = k9_relat_1(k5_relat_1(sK0,X1),k1_relat_1(k5_relat_1(sK0,X1))) )
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f207])).

fof(f209,plain,
    ( spl2_36
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f200,f82,f40,f207])).

fof(f82,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(k5_relat_1(X0,X1),k1_relat_1(k5_relat_1(X0,X1)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f200,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k5_relat_1(sK0,X1)) = k9_relat_1(k5_relat_1(sK0,X1),k1_relat_1(k5_relat_1(sK0,X1))) )
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(resolution,[],[f83,f42])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(k5_relat_1(X0,X1),k1_relat_1(k5_relat_1(X0,X1))) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f189,plain,
    ( spl2_32
    | ~ spl2_2
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f182,f158,f35,f186])).

fof(f158,plain,
    ( spl2_27
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(sK0,X1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,X1)),k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f182,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl2_2
    | ~ spl2_27 ),
    inference(resolution,[],[f159,f37])).

fof(f159,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(sK0,X1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,X1)),k1_relat_1(sK0)) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f158])).

fof(f160,plain,
    ( spl2_27
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f151,f87,f40,f158])).

fof(f87,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(k5_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f151,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(sK0,X1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,X1)),k1_relat_1(sK0)) )
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(resolution,[],[f88,f42])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | k1_relat_1(k5_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(k5_relat_1(X1,X0)),k1_relat_1(X1)) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f87])).

fof(f141,plain,
    ( spl2_23
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f135,f113,f35,f139])).

fof(f113,plain,
    ( spl2_18
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f135,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(resolution,[],[f114,f37])).

fof(f114,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f106,f57,f40,f113])).

fof(f57,plain,
    ( spl2_7
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f106,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)) )
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f104,plain,
    ( spl2_16
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f92,f65,f53,f102])).

fof(f53,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f65,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f92,plain,
    ( ! [X4,X2,X3] :
        ( k9_relat_1(k5_relat_1(X2,X3),X4) = k9_relat_1(k5_relat_1(X2,X3),k3_xboole_0(k1_relat_1(k5_relat_1(X2,X3)),X4))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(resolution,[],[f54,f66])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f89,plain,
    ( spl2_13
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f85,f61,f49,f87])).

fof(f49,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f61,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(k5_relat_1(X1,X0)),k1_relat_1(X1)) )
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(resolution,[],[f50,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f84,plain,
    ( spl2_12
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f70,f65,f45,f82])).

fof(f45,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(k5_relat_1(X0,X1),k1_relat_1(k5_relat_1(X0,X1)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(resolution,[],[f46,f66])).

fof(f46,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f80,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f69,f45,f40,f77])).

fof(f69,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f46,f42])).

fof(f67,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f63,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f59,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f26,f57])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(f55,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(f51,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f47,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f40])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
        & v1_relat_1(X1) )
   => ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f38,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f35])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f22,f30])).

fof(f22,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:08:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (23551)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (23548)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.41  % (23549)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.41  % (23550)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (23549)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f532,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f33,f38,f43,f47,f51,f55,f59,f63,f67,f80,f84,f89,f104,f115,f141,f160,f189,f209,f254,f388,f500,f518,f531])).
% 0.20/0.42  fof(f531,plain,(
% 0.20/0.42    spl2_1 | ~spl2_43 | ~spl2_86),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f530])).
% 0.20/0.42  fof(f530,plain,(
% 0.20/0.42    $false | (spl2_1 | ~spl2_43 | ~spl2_86)),
% 0.20/0.42    inference(subsumption_resolution,[],[f526,f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) | spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f30])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    spl2_1 <=> k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f526,plain,(
% 0.20/0.42    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) | (~spl2_43 | ~spl2_86)),
% 0.20/0.42    inference(superposition,[],[f253,f517])).
% 0.20/0.42  fof(f517,plain,(
% 0.20/0.42    k9_relat_1(sK1,k2_relat_1(sK0)) = k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl2_86),
% 0.20/0.42    inference(avatar_component_clause,[],[f515])).
% 0.20/0.42  fof(f515,plain,(
% 0.20/0.42    spl2_86 <=> k9_relat_1(sK1,k2_relat_1(sK0)) = k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).
% 0.20/0.42  fof(f253,plain,(
% 0.20/0.42    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl2_43),
% 0.20/0.42    inference(avatar_component_clause,[],[f251])).
% 0.20/0.42  fof(f251,plain,(
% 0.20/0.42    spl2_43 <=> k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.20/0.42  fof(f518,plain,(
% 0.20/0.42    spl2_86 | ~spl2_11 | ~spl2_32 | ~spl2_83),
% 0.20/0.42    inference(avatar_split_clause,[],[f513,f498,f186,f77,f515])).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    spl2_11 <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.42  fof(f186,plain,(
% 0.20/0.42    spl2_32 <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.20/0.42  fof(f498,plain,(
% 0.20/0.42    spl2_83 <=> ! [X0] : k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k9_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).
% 0.20/0.42  fof(f513,plain,(
% 0.20/0.42    k9_relat_1(sK1,k2_relat_1(sK0)) = k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1))) | (~spl2_11 | ~spl2_32 | ~spl2_83)),
% 0.20/0.42    inference(forward_demodulation,[],[f510,f79])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl2_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f77])).
% 0.20/0.42  fof(f510,plain,(
% 0.20/0.42    k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1))) = k9_relat_1(sK1,k9_relat_1(sK0,k1_relat_1(sK0))) | (~spl2_32 | ~spl2_83)),
% 0.20/0.42    inference(superposition,[],[f499,f188])).
% 0.20/0.42  fof(f188,plain,(
% 0.20/0.42    k1_relat_1(k5_relat_1(sK0,sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~spl2_32),
% 0.20/0.42    inference(avatar_component_clause,[],[f186])).
% 0.20/0.42  fof(f499,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k9_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),X0))) ) | ~spl2_83),
% 0.20/0.42    inference(avatar_component_clause,[],[f498])).
% 0.20/0.42  fof(f500,plain,(
% 0.20/0.42    spl2_83 | ~spl2_2 | ~spl2_23 | ~spl2_67),
% 0.20/0.42    inference(avatar_split_clause,[],[f496,f386,f139,f35,f498])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    spl2_2 <=> v1_relat_1(sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f139,plain,(
% 0.20/0.42    spl2_23 <=> ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.20/0.42  fof(f386,plain,(
% 0.20/0.42    spl2_67 <=> ! [X3,X2] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(k5_relat_1(sK0,X2),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,X2)),X3)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 0.20/0.42  fof(f496,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k9_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),X0))) ) | (~spl2_2 | ~spl2_23 | ~spl2_67)),
% 0.20/0.42    inference(forward_demodulation,[],[f493,f140])).
% 0.20/0.42  fof(f140,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))) ) | ~spl2_23),
% 0.20/0.42    inference(avatar_component_clause,[],[f139])).
% 0.20/0.42  fof(f493,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(k5_relat_1(sK0,sK1),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),X0))) ) | (~spl2_2 | ~spl2_67)),
% 0.20/0.42    inference(resolution,[],[f387,f37])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f35])).
% 0.20/0.42  fof(f387,plain,(
% 0.20/0.42    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(k5_relat_1(sK0,X2),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,X2)),X3))) ) | ~spl2_67),
% 0.20/0.42    inference(avatar_component_clause,[],[f386])).
% 0.20/0.42  fof(f388,plain,(
% 0.20/0.42    spl2_67 | ~spl2_3 | ~spl2_16),
% 0.20/0.42    inference(avatar_split_clause,[],[f379,f102,f40,f386])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    spl2_3 <=> v1_relat_1(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.42  fof(f102,plain,(
% 0.20/0.42    spl2_16 <=> ! [X3,X2,X4] : (k9_relat_1(k5_relat_1(X2,X3),X4) = k9_relat_1(k5_relat_1(X2,X3),k3_xboole_0(k1_relat_1(k5_relat_1(X2,X3)),X4)) | ~v1_relat_1(X3) | ~v1_relat_1(X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.42  fof(f379,plain,(
% 0.20/0.42    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(k5_relat_1(sK0,X2),k3_xboole_0(k1_relat_1(k5_relat_1(sK0,X2)),X3))) ) | (~spl2_3 | ~spl2_16)),
% 0.20/0.42    inference(resolution,[],[f103,f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    v1_relat_1(sK0) | ~spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f40])).
% 0.20/0.42  fof(f103,plain,(
% 0.20/0.42    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k9_relat_1(k5_relat_1(X2,X3),X4) = k9_relat_1(k5_relat_1(X2,X3),k3_xboole_0(k1_relat_1(k5_relat_1(X2,X3)),X4))) ) | ~spl2_16),
% 0.20/0.42    inference(avatar_component_clause,[],[f102])).
% 0.20/0.42  fof(f254,plain,(
% 0.20/0.42    spl2_43 | ~spl2_2 | ~spl2_36),
% 0.20/0.42    inference(avatar_split_clause,[],[f247,f207,f35,f251])).
% 0.20/0.42  fof(f207,plain,(
% 0.20/0.42    spl2_36 <=> ! [X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(sK0,X1)) = k9_relat_1(k5_relat_1(sK0,X1),k1_relat_1(k5_relat_1(sK0,X1))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.20/0.42  fof(f247,plain,(
% 0.20/0.42    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(k5_relat_1(sK0,sK1))) | (~spl2_2 | ~spl2_36)),
% 0.20/0.42    inference(resolution,[],[f208,f37])).
% 0.20/0.42  fof(f208,plain,(
% 0.20/0.42    ( ! [X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(sK0,X1)) = k9_relat_1(k5_relat_1(sK0,X1),k1_relat_1(k5_relat_1(sK0,X1)))) ) | ~spl2_36),
% 0.20/0.42    inference(avatar_component_clause,[],[f207])).
% 0.20/0.42  fof(f209,plain,(
% 0.20/0.42    spl2_36 | ~spl2_3 | ~spl2_12),
% 0.20/0.42    inference(avatar_split_clause,[],[f200,f82,f40,f207])).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    spl2_12 <=> ! [X1,X0] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(k5_relat_1(X0,X1),k1_relat_1(k5_relat_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.42  fof(f200,plain,(
% 0.20/0.42    ( ! [X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(sK0,X1)) = k9_relat_1(k5_relat_1(sK0,X1),k1_relat_1(k5_relat_1(sK0,X1)))) ) | (~spl2_3 | ~spl2_12)),
% 0.20/0.42    inference(resolution,[],[f83,f42])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(k5_relat_1(X0,X1),k1_relat_1(k5_relat_1(X0,X1)))) ) | ~spl2_12),
% 0.20/0.42    inference(avatar_component_clause,[],[f82])).
% 0.20/0.42  fof(f189,plain,(
% 0.20/0.42    spl2_32 | ~spl2_2 | ~spl2_27),
% 0.20/0.42    inference(avatar_split_clause,[],[f182,f158,f35,f186])).
% 0.20/0.42  fof(f158,plain,(
% 0.20/0.42    spl2_27 <=> ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(sK0,X1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,X1)),k1_relat_1(sK0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.20/0.42  fof(f182,plain,(
% 0.20/0.42    k1_relat_1(k5_relat_1(sK0,sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | (~spl2_2 | ~spl2_27)),
% 0.20/0.42    inference(resolution,[],[f159,f37])).
% 0.20/0.42  fof(f159,plain,(
% 0.20/0.42    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(sK0,X1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,X1)),k1_relat_1(sK0))) ) | ~spl2_27),
% 0.20/0.42    inference(avatar_component_clause,[],[f158])).
% 0.20/0.42  fof(f160,plain,(
% 0.20/0.42    spl2_27 | ~spl2_3 | ~spl2_13),
% 0.20/0.42    inference(avatar_split_clause,[],[f151,f87,f40,f158])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    spl2_13 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(k5_relat_1(X1,X0)),k1_relat_1(X1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.42  fof(f151,plain,(
% 0.20/0.42    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(sK0,X1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,X1)),k1_relat_1(sK0))) ) | (~spl2_3 | ~spl2_13)),
% 0.20/0.42    inference(resolution,[],[f88,f42])).
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(k5_relat_1(X1,X0)),k1_relat_1(X1))) ) | ~spl2_13),
% 0.20/0.42    inference(avatar_component_clause,[],[f87])).
% 0.20/0.42  fof(f141,plain,(
% 0.20/0.42    spl2_23 | ~spl2_2 | ~spl2_18),
% 0.20/0.42    inference(avatar_split_clause,[],[f135,f113,f35,f139])).
% 0.20/0.42  fof(f113,plain,(
% 0.20/0.42    spl2_18 <=> ! [X3,X2] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.42  fof(f135,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))) ) | (~spl2_2 | ~spl2_18)),
% 0.20/0.42    inference(resolution,[],[f114,f37])).
% 0.20/0.42  fof(f114,plain,(
% 0.20/0.42    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3))) ) | ~spl2_18),
% 0.20/0.42    inference(avatar_component_clause,[],[f113])).
% 0.20/0.42  fof(f115,plain,(
% 0.20/0.42    spl2_18 | ~spl2_3 | ~spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f106,f57,f40,f113])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    spl2_7 <=> ! [X1,X0,X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.42  fof(f106,plain,(
% 0.20/0.42    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3))) ) | (~spl2_3 | ~spl2_7)),
% 0.20/0.42    inference(resolution,[],[f58,f42])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) ) | ~spl2_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f57])).
% 0.20/0.42  fof(f104,plain,(
% 0.20/0.42    spl2_16 | ~spl2_6 | ~spl2_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f92,f65,f53,f102])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl2_6 <=> ! [X1,X0] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    spl2_9 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.42  fof(f92,plain,(
% 0.20/0.42    ( ! [X4,X2,X3] : (k9_relat_1(k5_relat_1(X2,X3),X4) = k9_relat_1(k5_relat_1(X2,X3),k3_xboole_0(k1_relat_1(k5_relat_1(X2,X3)),X4)) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) ) | (~spl2_6 | ~spl2_9)),
% 0.20/0.42    inference(resolution,[],[f54,f66])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f65])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) ) | ~spl2_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f53])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    spl2_13 | ~spl2_5 | ~spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f85,f61,f49,f87])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl2_5 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl2_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(k5_relat_1(X1,X0)),k1_relat_1(X1))) ) | (~spl2_5 | ~spl2_8)),
% 0.20/0.42    inference(resolution,[],[f50,f62])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl2_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f61])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f49])).
% 0.20/0.42  fof(f84,plain,(
% 0.20/0.42    spl2_12 | ~spl2_4 | ~spl2_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f70,f65,f45,f82])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl2_4 <=> ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(k5_relat_1(X0,X1),k1_relat_1(k5_relat_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | (~spl2_4 | ~spl2_9)),
% 0.20/0.42    inference(resolution,[],[f46,f66])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) ) | ~spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f45])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    spl2_11 | ~spl2_3 | ~spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f69,f45,f40,f77])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | (~spl2_3 | ~spl2_4)),
% 0.20/0.42    inference(resolution,[],[f46,f42])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    spl2_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f28,f65])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f61])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f57])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f53])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    spl2_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f49])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f45])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl2_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f40])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    v1_relat_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) => (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.42    inference(negated_conjecture,[],[f7])).
% 0.20/0.42  fof(f7,conjecture,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f21,f35])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    v1_relat_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ~spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f30])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (23549)------------------------------
% 0.20/0.42  % (23549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (23549)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (23549)Memory used [KB]: 10874
% 0.20/0.42  % (23549)Time elapsed: 0.015 s
% 0.20/0.42  % (23549)------------------------------
% 0.20/0.42  % (23549)------------------------------
% 0.20/0.42  % (23543)Success in time 0.071 s
%------------------------------------------------------------------------------
