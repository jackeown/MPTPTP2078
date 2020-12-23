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
% DateTime   : Thu Dec  3 12:54:06 EST 2020

% Result     : Theorem 5.28s
% Output     : Refutation 5.28s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 382 expanded)
%              Number of leaves         :   60 ( 178 expanded)
%              Depth                    :    7
%              Number of atoms          :  599 ( 994 expanded)
%              Number of equality atoms :   96 ( 163 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14805,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f94,f102,f106,f111,f115,f120,f124,f128,f132,f136,f173,f214,f248,f252,f310,f328,f542,f684,f891,f1057,f1067,f1108,f1182,f1221,f1245,f1932,f8159,f8509,f8540,f8747,f9626,f9680,f9838,f10016,f12033,f14483,f14595,f14655,f14750])).

fof(f14750,plain,
    ( spl2_7
    | ~ spl2_13
    | ~ spl2_299 ),
    inference(avatar_contradiction_clause,[],[f14749])).

fof(f14749,plain,
    ( $false
    | spl2_7
    | ~ spl2_13
    | ~ spl2_299 ),
    inference(subsumption_resolution,[],[f110,f14741])).

fof(f14741,plain,
    ( ! [X12] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12)
    | ~ spl2_13
    | ~ spl2_299 ),
    inference(trivial_inequality_removal,[],[f14674])).

fof(f14674,plain,
    ( ! [X12] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12) )
    | ~ spl2_13
    | ~ spl2_299 ),
    inference(superposition,[],[f135,f14654])).

fof(f14654,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
    | ~ spl2_299 ),
    inference(avatar_component_clause,[],[f14653])).

fof(f14653,plain,
    ( spl2_299
  <=> ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_299])])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k6_subset_1(X0,X1)
        | r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f110,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_7
  <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f14655,plain,
    ( spl2_299
    | ~ spl2_8
    | ~ spl2_298 ),
    inference(avatar_split_clause,[],[f14596,f14593,f113,f14653])).

fof(f113,plain,
    ( spl2_8
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f14593,plain,
    ( spl2_298
  <=> ! [X8] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_298])])).

fof(f14596,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
    | ~ spl2_8
    | ~ spl2_298 ),
    inference(resolution,[],[f14594,f114])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f14594,plain,
    ( ! [X8] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_xboole_0)
    | ~ spl2_298 ),
    inference(avatar_component_clause,[],[f14593])).

fof(f14595,plain,
    ( spl2_298
    | ~ spl2_87
    | ~ spl2_222
    | ~ spl2_229
    | ~ spl2_297 ),
    inference(avatar_split_clause,[],[f14591,f14481,f10014,f9835,f1219,f14593])).

fof(f1219,plain,
    ( spl2_87
  <=> ! [X3,X2] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f9835,plain,
    ( spl2_222
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_222])])).

fof(f10014,plain,
    ( spl2_229
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_229])])).

fof(f14481,plain,
    ( spl2_297
  <=> ! [X2] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_297])])).

fof(f14591,plain,
    ( ! [X8] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_xboole_0)
    | ~ spl2_87
    | ~ spl2_222
    | ~ spl2_229
    | ~ spl2_297 ),
    inference(forward_demodulation,[],[f14590,f9837])).

fof(f9837,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl2_222 ),
    inference(avatar_component_clause,[],[f9835])).

fof(f14590,plain,
    ( ! [X8] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k10_relat_1(sK1,k1_xboole_0))
    | ~ spl2_87
    | ~ spl2_229
    | ~ spl2_297 ),
    inference(subsumption_resolution,[],[f14572,f1220])).

fof(f1220,plain,
    ( ! [X2,X3] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1))
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f1219])).

fof(f14572,plain,
    ( ! [X8] :
        ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k10_relat_1(sK1,k1_xboole_0))
        | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_relat_1(sK1)) )
    | ~ spl2_229
    | ~ spl2_297 ),
    inference(superposition,[],[f10015,f14482])).

fof(f14482,plain,
    ( ! [X2] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))
    | ~ spl2_297 ),
    inference(avatar_component_clause,[],[f14481])).

fof(f10015,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
        | ~ r1_tarski(X0,k1_relat_1(sK1)) )
    | ~ spl2_229 ),
    inference(avatar_component_clause,[],[f10014])).

fof(f14483,plain,
    ( spl2_297
    | ~ spl2_73
    | ~ spl2_262 ),
    inference(avatar_split_clause,[],[f13925,f12031,f889,f14481])).

fof(f889,plain,
    ( spl2_73
  <=> ! [X1] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).

fof(f12031,plain,
    ( spl2_262
  <=> ! [X1,X0] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_262])])).

fof(f13925,plain,
    ( ! [X2] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))
    | ~ spl2_73
    | ~ spl2_262 ),
    inference(superposition,[],[f12032,f890])).

fof(f890,plain,
    ( ! [X1] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X1)
    | ~ spl2_73 ),
    inference(avatar_component_clause,[],[f889])).

fof(f12032,plain,
    ( ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ spl2_262 ),
    inference(avatar_component_clause,[],[f12031])).

fof(f12033,plain,
    ( spl2_262
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_218 ),
    inference(avatar_split_clause,[],[f9661,f8745,f91,f86,f81,f12031])).

fof(f81,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f86,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f91,plain,
    ( spl2_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f8745,plain,
    ( spl2_218
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ v2_funct_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_218])])).

fof(f9661,plain,
    ( ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_218 ),
    inference(subsumption_resolution,[],[f9660,f83])).

fof(f83,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f9660,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_218 ),
    inference(subsumption_resolution,[],[f9659,f88])).

fof(f88,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f9659,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_3
    | ~ spl2_218 ),
    inference(resolution,[],[f8746,f93])).

fof(f93,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f8746,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_funct_1(X2)
        | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl2_218 ),
    inference(avatar_component_clause,[],[f8745])).

fof(f10016,plain,
    ( spl2_229
    | ~ spl2_1
    | ~ spl2_110 ),
    inference(avatar_split_clause,[],[f5875,f1930,f81,f10014])).

fof(f1930,plain,
    ( spl2_110
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_110])])).

fof(f5875,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) )
    | ~ spl2_1
    | ~ spl2_110 ),
    inference(resolution,[],[f1931,f83])).

fof(f1931,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) )
    | ~ spl2_110 ),
    inference(avatar_component_clause,[],[f1930])).

fof(f9838,plain,
    ( spl2_222
    | ~ spl2_79
    | ~ spl2_80
    | ~ spl2_220 ),
    inference(avatar_split_clause,[],[f9756,f9678,f1065,f1055,f9835])).

fof(f1055,plain,
    ( spl2_79
  <=> ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).

fof(f1065,plain,
    ( spl2_80
  <=> ! [X5] : r1_tarski(X5,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f9678,plain,
    ( spl2_220
  <=> ! [X3,X2] :
        ( k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X3))
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_220])])).

fof(f9756,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl2_79
    | ~ spl2_80
    | ~ spl2_220 ),
    inference(forward_demodulation,[],[f9681,f1056])).

fof(f1056,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0)
    | ~ spl2_79 ),
    inference(avatar_component_clause,[],[f1055])).

fof(f9681,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,X0))
    | ~ spl2_80
    | ~ spl2_220 ),
    inference(resolution,[],[f9679,f1066])).

fof(f1066,plain,
    ( ! [X5] : r1_tarski(X5,X5)
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f1065])).

fof(f9679,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X3)) )
    | ~ spl2_220 ),
    inference(avatar_component_clause,[],[f9678])).

fof(f9680,plain,
    ( spl2_220
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_118
    | ~ spl2_205 ),
    inference(avatar_split_clause,[],[f8495,f8157,f2079,f130,f86,f81,f9678])).

fof(f130,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k6_subset_1(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f2079,plain,
    ( spl2_118
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_118])])).

fof(f8157,plain,
    ( spl2_205
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_205])])).

fof(f8495,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X3))
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_118
    | ~ spl2_205 ),
    inference(forward_demodulation,[],[f2083,f8484])).

fof(f8484,plain,
    ( ! [X0,X1] : k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_205 ),
    inference(subsumption_resolution,[],[f8483,f83])).

fof(f8483,plain,
    ( ! [X0,X1] :
        ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_205 ),
    inference(resolution,[],[f8158,f88])).

fof(f8158,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl2_205 ),
    inference(avatar_component_clause,[],[f8157])).

fof(f2083,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3)) )
    | ~ spl2_12
    | ~ spl2_118 ),
    inference(resolution,[],[f2080,f131])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k6_subset_1(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f2080,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_118 ),
    inference(avatar_component_clause,[],[f2079])).

fof(f9626,plain,
    ( spl2_118
    | ~ spl2_1
    | ~ spl2_90 ),
    inference(avatar_split_clause,[],[f5460,f1243,f81,f2079])).

fof(f1243,plain,
    ( spl2_90
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).

fof(f5460,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) )
    | ~ spl2_1
    | ~ spl2_90 ),
    inference(resolution,[],[f1244,f83])).

fof(f1244,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
    | ~ spl2_90 ),
    inference(avatar_component_clause,[],[f1243])).

fof(f8747,plain,(
    spl2_218 ),
    inference(avatar_split_clause,[],[f71,f8745])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f8540,plain,
    ( spl2_70
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f4415,f540,f86,f81,f860])).

fof(f860,plain,
    ( spl2_70
  <=> ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f540,plain,
    ( spl2_51
  <=> ! [X1,X0] :
        ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f4415,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_51 ),
    inference(subsumption_resolution,[],[f4414,f83])).

fof(f4414,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_51 ),
    inference(resolution,[],[f541,f88])).

fof(f541,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f540])).

fof(f8509,plain,
    ( spl2_29
    | ~ spl2_1
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f8491,f246,f212,f81,f256])).

fof(f256,plain,
    ( spl2_29
  <=> ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f212,plain,
    ( spl2_23
  <=> ! [X0] :
        ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f246,plain,
    ( spl2_27
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f8491,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(backward_demodulation,[],[f3822,f3321])).

fof(f3321,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(resolution,[],[f83,f213])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f212])).

fof(f3822,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_27 ),
    inference(resolution,[],[f247,f83])).

fof(f247,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f246])).

fof(f8159,plain,(
    spl2_205 ),
    inference(avatar_split_clause,[],[f70,f8157])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f1932,plain,(
    spl2_110 ),
    inference(avatar_split_clause,[],[f61,f1930])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f1245,plain,(
    spl2_90 ),
    inference(avatar_split_clause,[],[f67,f1243])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f1221,plain,
    ( spl2_87
    | ~ spl2_28
    | ~ spl2_85 ),
    inference(avatar_split_clause,[],[f1188,f1180,f250,f1219])).

fof(f250,plain,
    ( spl2_28
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k6_subset_1(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f1180,plain,
    ( spl2_85
  <=> ! [X16,X17] : r1_tarski(k10_relat_1(sK1,X16),k2_xboole_0(X17,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).

fof(f1188,plain,
    ( ! [X2,X3] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1))
    | ~ spl2_28
    | ~ spl2_85 ),
    inference(resolution,[],[f1181,f251])).

fof(f251,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | r1_tarski(k6_subset_1(X0,X1),X2) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f250])).

fof(f1181,plain,
    ( ! [X17,X16] : r1_tarski(k10_relat_1(sK1,X16),k2_xboole_0(X17,k1_relat_1(sK1)))
    | ~ spl2_85 ),
    inference(avatar_component_clause,[],[f1180])).

fof(f1182,plain,
    ( spl2_85
    | ~ spl2_36
    | ~ spl2_82 ),
    inference(avatar_split_clause,[],[f1120,f1106,f326,f1180])).

fof(f326,plain,
    ( spl2_36
  <=> ! [X3,X2] :
        ( ~ r1_tarski(k1_relat_1(sK1),X3)
        | r1_tarski(k10_relat_1(sK1,X2),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f1106,plain,
    ( spl2_82
  <=> ! [X7,X8] : r1_tarski(X7,k2_xboole_0(X8,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).

fof(f1120,plain,
    ( ! [X17,X16] : r1_tarski(k10_relat_1(sK1,X16),k2_xboole_0(X17,k1_relat_1(sK1)))
    | ~ spl2_36
    | ~ spl2_82 ),
    inference(resolution,[],[f1107,f327])).

fof(f327,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k1_relat_1(sK1),X3)
        | r1_tarski(k10_relat_1(sK1,X2),X3) )
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f326])).

fof(f1107,plain,
    ( ! [X8,X7] : r1_tarski(X7,k2_xboole_0(X8,X7))
    | ~ spl2_82 ),
    inference(avatar_component_clause,[],[f1106])).

fof(f1108,plain,
    ( spl2_82
    | ~ spl2_17
    | ~ spl2_80 ),
    inference(avatar_split_clause,[],[f1075,f1065,f171,f1106])).

fof(f171,plain,
    ( spl2_17
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(k2_xboole_0(X1,X0),X2)
        | r1_tarski(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f1075,plain,
    ( ! [X8,X7] : r1_tarski(X7,k2_xboole_0(X8,X7))
    | ~ spl2_17
    | ~ spl2_80 ),
    inference(resolution,[],[f1066,f172])).

fof(f172,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X1,X0),X2)
        | r1_tarski(X0,X2) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f171])).

fof(f1067,plain,
    ( spl2_80
    | ~ spl2_13
    | ~ spl2_79 ),
    inference(avatar_split_clause,[],[f1062,f1055,f134,f1065])).

fof(f1062,plain,
    ( ! [X5] : r1_tarski(X5,X5)
    | ~ spl2_13
    | ~ spl2_79 ),
    inference(trivial_inequality_removal,[],[f1060])).

fof(f1060,plain,
    ( ! [X5] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(X5,X5) )
    | ~ spl2_13
    | ~ spl2_79 ),
    inference(superposition,[],[f135,f1056])).

fof(f1057,plain,
    ( spl2_79
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_63 ),
    inference(avatar_split_clause,[],[f1034,f682,f104,f100,f1055])).

fof(f100,plain,
    ( spl2_5
  <=> ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f104,plain,
    ( spl2_6
  <=> ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f682,plain,
    ( spl2_63
  <=> ! [X1,X0] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f1034,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0)
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_63 ),
    inference(forward_demodulation,[],[f1014,f101])).

fof(f101,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1014,plain,
    ( ! [X0] : k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,X0)) = k6_subset_1(X0,X0)
    | ~ spl2_6
    | ~ spl2_63 ),
    inference(superposition,[],[f683,f105])).

fof(f105,plain,
    ( ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f683,plain,
    ( ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f682])).

fof(f891,plain,
    ( spl2_73
    | ~ spl2_12
    | ~ spl2_70 ),
    inference(avatar_split_clause,[],[f864,f860,f130,f889])).

fof(f864,plain,
    ( ! [X1] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X1)
    | ~ spl2_12
    | ~ spl2_70 ),
    inference(resolution,[],[f861,f131])).

fof(f861,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_70 ),
    inference(avatar_component_clause,[],[f860])).

fof(f684,plain,(
    spl2_63 ),
    inference(avatar_split_clause,[],[f75,f682])).

fof(f75,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f55,f72,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f58,f56,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f542,plain,(
    spl2_51 ),
    inference(avatar_split_clause,[],[f63,f540])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f328,plain,
    ( spl2_36
    | ~ spl2_11
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f316,f308,f126,f326])).

fof(f126,plain,
    ( spl2_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f308,plain,
    ( spl2_34
  <=> ! [X1] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f316,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k1_relat_1(sK1),X3)
        | r1_tarski(k10_relat_1(sK1,X2),X3) )
    | ~ spl2_11
    | ~ spl2_34 ),
    inference(superposition,[],[f127,f309])).

fof(f309,plain,
    ( ! [X1] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X1),k1_relat_1(sK1))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f308])).

fof(f127,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f310,plain,
    ( spl2_34
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f260,f256,f122,f308])).

fof(f122,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f260,plain,
    ( ! [X1] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X1),k1_relat_1(sK1))
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(resolution,[],[f257,f123])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f257,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f256])).

fof(f252,plain,(
    spl2_28 ),
    inference(avatar_split_clause,[],[f79,f250])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f68,f56])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f248,plain,(
    spl2_27 ),
    inference(avatar_split_clause,[],[f60,f246])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f214,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f53,f212])).

fof(f53,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f173,plain,
    ( spl2_17
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f154,f126,f118,f171])).

fof(f118,plain,
    ( spl2_9
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X1,X0),X2)
        | r1_tarski(X0,X2) )
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(superposition,[],[f127,f119])).

fof(f119,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f136,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f78,f134])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f56])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f132,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f77,f130])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f56])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f128,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f69,f126])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f124,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f62,f122])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f120,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f57,f118])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f115,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f54,f113])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f111,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f49,f108])).

fof(f49,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f43])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f106,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f74,f104])).

fof(f74,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f102,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f73,f100])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f94,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f48,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f47,f86])).

fof(f47,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f46,f81])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:14:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (14125)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (14126)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (14122)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (14118)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (14119)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (14132)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (14123)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (14133)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (14131)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (14120)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (14121)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (14127)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (14130)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (14134)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (14135)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (14124)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.51  % (14117)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.51  % (14129)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 4.71/1.01  % (14121)Time limit reached!
% 4.71/1.01  % (14121)------------------------------
% 4.71/1.01  % (14121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.71/1.01  % (14121)Termination reason: Time limit
% 4.71/1.01  % (14121)Termination phase: Saturation
% 4.71/1.01  
% 4.71/1.01  % (14121)Memory used [KB]: 12409
% 4.71/1.01  % (14121)Time elapsed: 0.600 s
% 4.71/1.01  % (14121)------------------------------
% 4.71/1.01  % (14121)------------------------------
% 5.28/1.03  % (14124)Refutation found. Thanks to Tanya!
% 5.28/1.03  % SZS status Theorem for theBenchmark
% 5.28/1.03  % SZS output start Proof for theBenchmark
% 5.28/1.03  fof(f14805,plain,(
% 5.28/1.03    $false),
% 5.28/1.03    inference(avatar_sat_refutation,[],[f84,f89,f94,f102,f106,f111,f115,f120,f124,f128,f132,f136,f173,f214,f248,f252,f310,f328,f542,f684,f891,f1057,f1067,f1108,f1182,f1221,f1245,f1932,f8159,f8509,f8540,f8747,f9626,f9680,f9838,f10016,f12033,f14483,f14595,f14655,f14750])).
% 5.28/1.03  fof(f14750,plain,(
% 5.28/1.03    spl2_7 | ~spl2_13 | ~spl2_299),
% 5.28/1.03    inference(avatar_contradiction_clause,[],[f14749])).
% 5.28/1.03  fof(f14749,plain,(
% 5.28/1.03    $false | (spl2_7 | ~spl2_13 | ~spl2_299)),
% 5.28/1.03    inference(subsumption_resolution,[],[f110,f14741])).
% 5.28/1.03  fof(f14741,plain,(
% 5.28/1.03    ( ! [X12] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12)) ) | (~spl2_13 | ~spl2_299)),
% 5.28/1.03    inference(trivial_inequality_removal,[],[f14674])).
% 5.28/1.03  fof(f14674,plain,(
% 5.28/1.03    ( ! [X12] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12)) ) | (~spl2_13 | ~spl2_299)),
% 5.28/1.03    inference(superposition,[],[f135,f14654])).
% 5.28/1.03  fof(f14654,plain,(
% 5.28/1.03    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ) | ~spl2_299),
% 5.28/1.03    inference(avatar_component_clause,[],[f14653])).
% 5.28/1.03  fof(f14653,plain,(
% 5.28/1.03    spl2_299 <=> ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_299])])).
% 5.28/1.03  fof(f135,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) ) | ~spl2_13),
% 5.28/1.03    inference(avatar_component_clause,[],[f134])).
% 5.28/1.03  fof(f134,plain,(
% 5.28/1.03    spl2_13 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 5.28/1.03  fof(f110,plain,(
% 5.28/1.03    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | spl2_7),
% 5.28/1.03    inference(avatar_component_clause,[],[f108])).
% 5.28/1.03  fof(f108,plain,(
% 5.28/1.03    spl2_7 <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 5.28/1.03  fof(f14655,plain,(
% 5.28/1.03    spl2_299 | ~spl2_8 | ~spl2_298),
% 5.28/1.03    inference(avatar_split_clause,[],[f14596,f14593,f113,f14653])).
% 5.28/1.03  fof(f113,plain,(
% 5.28/1.03    spl2_8 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 5.28/1.03  fof(f14593,plain,(
% 5.28/1.03    spl2_298 <=> ! [X8] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_xboole_0)),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_298])])).
% 5.28/1.03  fof(f14596,plain,(
% 5.28/1.03    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ) | (~spl2_8 | ~spl2_298)),
% 5.28/1.03    inference(resolution,[],[f14594,f114])).
% 5.28/1.03  fof(f114,plain,(
% 5.28/1.03    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl2_8),
% 5.28/1.03    inference(avatar_component_clause,[],[f113])).
% 5.28/1.03  fof(f14594,plain,(
% 5.28/1.03    ( ! [X8] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_xboole_0)) ) | ~spl2_298),
% 5.28/1.03    inference(avatar_component_clause,[],[f14593])).
% 5.28/1.03  fof(f14595,plain,(
% 5.28/1.03    spl2_298 | ~spl2_87 | ~spl2_222 | ~spl2_229 | ~spl2_297),
% 5.28/1.03    inference(avatar_split_clause,[],[f14591,f14481,f10014,f9835,f1219,f14593])).
% 5.28/1.03  fof(f1219,plain,(
% 5.28/1.03    spl2_87 <=> ! [X3,X2] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 5.28/1.03  fof(f9835,plain,(
% 5.28/1.03    spl2_222 <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_222])])).
% 5.28/1.03  fof(f10014,plain,(
% 5.28/1.03    spl2_229 <=> ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_229])])).
% 5.28/1.03  fof(f14481,plain,(
% 5.28/1.03    spl2_297 <=> ! [X2] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_297])])).
% 5.28/1.03  fof(f14591,plain,(
% 5.28/1.03    ( ! [X8] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_xboole_0)) ) | (~spl2_87 | ~spl2_222 | ~spl2_229 | ~spl2_297)),
% 5.28/1.03    inference(forward_demodulation,[],[f14590,f9837])).
% 5.28/1.03  fof(f9837,plain,(
% 5.28/1.03    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | ~spl2_222),
% 5.28/1.03    inference(avatar_component_clause,[],[f9835])).
% 5.28/1.03  fof(f14590,plain,(
% 5.28/1.03    ( ! [X8] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k10_relat_1(sK1,k1_xboole_0))) ) | (~spl2_87 | ~spl2_229 | ~spl2_297)),
% 5.28/1.03    inference(subsumption_resolution,[],[f14572,f1220])).
% 5.28/1.03  fof(f1220,plain,(
% 5.28/1.03    ( ! [X2,X3] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1))) ) | ~spl2_87),
% 5.28/1.03    inference(avatar_component_clause,[],[f1219])).
% 5.28/1.03  fof(f14572,plain,(
% 5.28/1.03    ( ! [X8] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k10_relat_1(sK1,k1_xboole_0)) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X8)),X8),k1_relat_1(sK1))) ) | (~spl2_229 | ~spl2_297)),
% 5.28/1.03    inference(superposition,[],[f10015,f14482])).
% 5.28/1.03  fof(f14482,plain,(
% 5.28/1.03    ( ! [X2] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))) ) | ~spl2_297),
% 5.28/1.03    inference(avatar_component_clause,[],[f14481])).
% 5.28/1.03  fof(f10015,plain,(
% 5.28/1.03    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~r1_tarski(X0,k1_relat_1(sK1))) ) | ~spl2_229),
% 5.28/1.03    inference(avatar_component_clause,[],[f10014])).
% 5.28/1.03  fof(f14483,plain,(
% 5.28/1.03    spl2_297 | ~spl2_73 | ~spl2_262),
% 5.28/1.03    inference(avatar_split_clause,[],[f13925,f12031,f889,f14481])).
% 5.28/1.03  fof(f889,plain,(
% 5.28/1.03    spl2_73 <=> ! [X1] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X1)),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).
% 5.28/1.03  fof(f12031,plain,(
% 5.28/1.03    spl2_262 <=> ! [X1,X0] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_262])])).
% 5.28/1.03  fof(f13925,plain,(
% 5.28/1.03    ( ! [X2] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))) ) | (~spl2_73 | ~spl2_262)),
% 5.28/1.03    inference(superposition,[],[f12032,f890])).
% 5.28/1.03  fof(f890,plain,(
% 5.28/1.03    ( ! [X1] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X1)) ) | ~spl2_73),
% 5.28/1.03    inference(avatar_component_clause,[],[f889])).
% 5.28/1.03  fof(f12032,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | ~spl2_262),
% 5.28/1.03    inference(avatar_component_clause,[],[f12031])).
% 5.28/1.03  fof(f12033,plain,(
% 5.28/1.03    spl2_262 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_218),
% 5.28/1.03    inference(avatar_split_clause,[],[f9661,f8745,f91,f86,f81,f12031])).
% 5.28/1.03  fof(f81,plain,(
% 5.28/1.03    spl2_1 <=> v1_relat_1(sK1)),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 5.28/1.03  fof(f86,plain,(
% 5.28/1.03    spl2_2 <=> v1_funct_1(sK1)),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 5.28/1.03  fof(f91,plain,(
% 5.28/1.03    spl2_3 <=> v2_funct_1(sK1)),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 5.28/1.03  fof(f8745,plain,(
% 5.28/1.03    spl2_218 <=> ! [X1,X0,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_218])])).
% 5.28/1.03  fof(f9661,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_218)),
% 5.28/1.03    inference(subsumption_resolution,[],[f9660,f83])).
% 5.28/1.03  fof(f83,plain,(
% 5.28/1.03    v1_relat_1(sK1) | ~spl2_1),
% 5.28/1.03    inference(avatar_component_clause,[],[f81])).
% 5.28/1.03  fof(f9660,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_3 | ~spl2_218)),
% 5.28/1.03    inference(subsumption_resolution,[],[f9659,f88])).
% 5.28/1.03  fof(f88,plain,(
% 5.28/1.03    v1_funct_1(sK1) | ~spl2_2),
% 5.28/1.03    inference(avatar_component_clause,[],[f86])).
% 5.28/1.03  fof(f9659,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl2_3 | ~spl2_218)),
% 5.28/1.03    inference(resolution,[],[f8746,f93])).
% 5.28/1.03  fof(f93,plain,(
% 5.28/1.03    v2_funct_1(sK1) | ~spl2_3),
% 5.28/1.03    inference(avatar_component_clause,[],[f91])).
% 5.28/1.03  fof(f8746,plain,(
% 5.28/1.03    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl2_218),
% 5.28/1.03    inference(avatar_component_clause,[],[f8745])).
% 5.28/1.03  fof(f10016,plain,(
% 5.28/1.03    spl2_229 | ~spl2_1 | ~spl2_110),
% 5.28/1.03    inference(avatar_split_clause,[],[f5875,f1930,f81,f10014])).
% 5.28/1.03  fof(f1930,plain,(
% 5.28/1.03    spl2_110 <=> ! [X1,X0] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_110])])).
% 5.28/1.03  fof(f5875,plain,(
% 5.28/1.03    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | (~spl2_1 | ~spl2_110)),
% 5.28/1.03    inference(resolution,[],[f1931,f83])).
% 5.28/1.03  fof(f1931,plain,(
% 5.28/1.03    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) ) | ~spl2_110),
% 5.28/1.03    inference(avatar_component_clause,[],[f1930])).
% 5.28/1.03  fof(f9838,plain,(
% 5.28/1.03    spl2_222 | ~spl2_79 | ~spl2_80 | ~spl2_220),
% 5.28/1.03    inference(avatar_split_clause,[],[f9756,f9678,f1065,f1055,f9835])).
% 5.28/1.03  fof(f1055,plain,(
% 5.28/1.03    spl2_79 <=> ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0)),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).
% 5.28/1.03  fof(f1065,plain,(
% 5.28/1.03    spl2_80 <=> ! [X5] : r1_tarski(X5,X5)),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 5.28/1.03  fof(f9678,plain,(
% 5.28/1.03    spl2_220 <=> ! [X3,X2] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X3)) | ~r1_tarski(X2,X3))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_220])])).
% 5.28/1.03  fof(f9756,plain,(
% 5.28/1.03    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | (~spl2_79 | ~spl2_80 | ~spl2_220)),
% 5.28/1.03    inference(forward_demodulation,[],[f9681,f1056])).
% 5.28/1.03  fof(f1056,plain,(
% 5.28/1.03    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) ) | ~spl2_79),
% 5.28/1.03    inference(avatar_component_clause,[],[f1055])).
% 5.28/1.03  fof(f9681,plain,(
% 5.28/1.03    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,X0))) ) | (~spl2_80 | ~spl2_220)),
% 5.28/1.03    inference(resolution,[],[f9679,f1066])).
% 5.28/1.03  fof(f1066,plain,(
% 5.28/1.03    ( ! [X5] : (r1_tarski(X5,X5)) ) | ~spl2_80),
% 5.28/1.03    inference(avatar_component_clause,[],[f1065])).
% 5.28/1.03  fof(f9679,plain,(
% 5.28/1.03    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X3))) ) | ~spl2_220),
% 5.28/1.03    inference(avatar_component_clause,[],[f9678])).
% 5.28/1.03  fof(f9680,plain,(
% 5.28/1.03    spl2_220 | ~spl2_1 | ~spl2_2 | ~spl2_12 | ~spl2_118 | ~spl2_205),
% 5.28/1.03    inference(avatar_split_clause,[],[f8495,f8157,f2079,f130,f86,f81,f9678])).
% 5.28/1.03  fof(f130,plain,(
% 5.28/1.03    spl2_12 <=> ! [X1,X0] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 5.28/1.03  fof(f2079,plain,(
% 5.28/1.03    spl2_118 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_118])])).
% 5.28/1.03  fof(f8157,plain,(
% 5.28/1.03    spl2_205 <=> ! [X1,X0,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_205])])).
% 5.28/1.03  fof(f8495,plain,(
% 5.28/1.03    ( ! [X2,X3] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X3)) | ~r1_tarski(X2,X3)) ) | (~spl2_1 | ~spl2_2 | ~spl2_12 | ~spl2_118 | ~spl2_205)),
% 5.28/1.03    inference(forward_demodulation,[],[f2083,f8484])).
% 5.28/1.03  fof(f8484,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_205)),
% 5.28/1.03    inference(subsumption_resolution,[],[f8483,f83])).
% 5.28/1.03  fof(f8483,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1)) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_205)),
% 5.28/1.03    inference(resolution,[],[f8158,f88])).
% 5.28/1.03  fof(f8158,plain,(
% 5.28/1.03    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) ) | ~spl2_205),
% 5.28/1.03    inference(avatar_component_clause,[],[f8157])).
% 5.28/1.03  fof(f2083,plain,(
% 5.28/1.03    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3))) ) | (~spl2_12 | ~spl2_118)),
% 5.28/1.03    inference(resolution,[],[f2080,f131])).
% 5.28/1.03  fof(f131,plain,(
% 5.28/1.03    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) ) | ~spl2_12),
% 5.28/1.03    inference(avatar_component_clause,[],[f130])).
% 5.28/1.03  fof(f2080,plain,(
% 5.28/1.03    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_118),
% 5.28/1.03    inference(avatar_component_clause,[],[f2079])).
% 5.28/1.03  fof(f9626,plain,(
% 5.28/1.03    spl2_118 | ~spl2_1 | ~spl2_90),
% 5.28/1.03    inference(avatar_split_clause,[],[f5460,f1243,f81,f2079])).
% 5.28/1.03  fof(f1243,plain,(
% 5.28/1.03    spl2_90 <=> ! [X1,X0,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).
% 5.28/1.03  fof(f5460,plain,(
% 5.28/1.03    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_90)),
% 5.28/1.03    inference(resolution,[],[f1244,f83])).
% 5.28/1.03  fof(f1244,plain,(
% 5.28/1.03    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) | ~spl2_90),
% 5.28/1.03    inference(avatar_component_clause,[],[f1243])).
% 5.28/1.03  fof(f8747,plain,(
% 5.28/1.03    spl2_218),
% 5.28/1.03    inference(avatar_split_clause,[],[f71,f8745])).
% 5.28/1.03  fof(f71,plain,(
% 5.28/1.03    ( ! [X2,X0,X1] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f42])).
% 5.28/1.03  fof(f42,plain,(
% 5.28/1.03    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 5.28/1.03    inference(flattening,[],[f41])).
% 5.28/1.03  fof(f41,plain,(
% 5.28/1.03    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 5.28/1.03    inference(ennf_transformation,[],[f18])).
% 5.28/1.03  fof(f18,axiom,(
% 5.28/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 5.28/1.03  fof(f8540,plain,(
% 5.28/1.03    spl2_70 | ~spl2_1 | ~spl2_2 | ~spl2_51),
% 5.28/1.03    inference(avatar_split_clause,[],[f4415,f540,f86,f81,f860])).
% 5.28/1.03  fof(f860,plain,(
% 5.28/1.03    spl2_70 <=> ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 5.28/1.03  fof(f540,plain,(
% 5.28/1.03    spl2_51 <=> ! [X1,X0] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 5.28/1.03  fof(f4415,plain,(
% 5.28/1.03    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_51)),
% 5.28/1.03    inference(subsumption_resolution,[],[f4414,f83])).
% 5.28/1.03  fof(f4414,plain,(
% 5.28/1.03    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_51)),
% 5.28/1.03    inference(resolution,[],[f541,f88])).
% 5.28/1.03  fof(f541,plain,(
% 5.28/1.03    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl2_51),
% 5.28/1.03    inference(avatar_component_clause,[],[f540])).
% 5.28/1.03  fof(f8509,plain,(
% 5.28/1.03    spl2_29 | ~spl2_1 | ~spl2_23 | ~spl2_27),
% 5.28/1.03    inference(avatar_split_clause,[],[f8491,f246,f212,f81,f256])).
% 5.28/1.03  fof(f256,plain,(
% 5.28/1.03    spl2_29 <=> ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 5.28/1.03  fof(f212,plain,(
% 5.28/1.03    spl2_23 <=> ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 5.28/1.03  fof(f246,plain,(
% 5.28/1.03    spl2_27 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 5.28/1.03  fof(f8491,plain,(
% 5.28/1.03    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | (~spl2_1 | ~spl2_23 | ~spl2_27)),
% 5.28/1.03    inference(backward_demodulation,[],[f3822,f3321])).
% 5.28/1.03  fof(f3321,plain,(
% 5.28/1.03    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) | (~spl2_1 | ~spl2_23)),
% 5.28/1.03    inference(resolution,[],[f83,f213])).
% 5.28/1.03  fof(f213,plain,(
% 5.28/1.03    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) ) | ~spl2_23),
% 5.28/1.03    inference(avatar_component_clause,[],[f212])).
% 5.28/1.03  fof(f3822,plain,(
% 5.28/1.03    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k2_relat_1(sK1)))) ) | (~spl2_1 | ~spl2_27)),
% 5.28/1.03    inference(resolution,[],[f247,f83])).
% 5.28/1.03  fof(f247,plain,(
% 5.28/1.03    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))) ) | ~spl2_27),
% 5.28/1.03    inference(avatar_component_clause,[],[f246])).
% 5.28/1.03  fof(f8159,plain,(
% 5.28/1.03    spl2_205),
% 5.28/1.03    inference(avatar_split_clause,[],[f70,f8157])).
% 5.28/1.03  fof(f70,plain,(
% 5.28/1.03    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f40])).
% 5.28/1.03  fof(f40,plain,(
% 5.28/1.03    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 5.28/1.03    inference(flattening,[],[f39])).
% 5.28/1.03  fof(f39,plain,(
% 5.28/1.03    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 5.28/1.03    inference(ennf_transformation,[],[f19])).
% 5.28/1.03  fof(f19,axiom,(
% 5.28/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 5.28/1.03  fof(f1932,plain,(
% 5.28/1.03    spl2_110),
% 5.28/1.03    inference(avatar_split_clause,[],[f61,f1930])).
% 5.28/1.03  fof(f61,plain,(
% 5.28/1.03    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f30])).
% 5.28/1.03  fof(f30,plain,(
% 5.28/1.03    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 5.28/1.03    inference(flattening,[],[f29])).
% 5.28/1.03  fof(f29,plain,(
% 5.28/1.03    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 5.28/1.03    inference(ennf_transformation,[],[f21])).
% 5.28/1.03  fof(f21,axiom,(
% 5.28/1.03    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 5.28/1.03  fof(f1245,plain,(
% 5.28/1.03    spl2_90),
% 5.28/1.03    inference(avatar_split_clause,[],[f67,f1243])).
% 5.28/1.03  fof(f67,plain,(
% 5.28/1.03    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f36])).
% 5.28/1.03  fof(f36,plain,(
% 5.28/1.03    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 5.28/1.03    inference(flattening,[],[f35])).
% 5.28/1.03  fof(f35,plain,(
% 5.28/1.03    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 5.28/1.03    inference(ennf_transformation,[],[f17])).
% 5.28/1.03  fof(f17,axiom,(
% 5.28/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 5.28/1.03  fof(f1221,plain,(
% 5.28/1.03    spl2_87 | ~spl2_28 | ~spl2_85),
% 5.28/1.03    inference(avatar_split_clause,[],[f1188,f1180,f250,f1219])).
% 5.28/1.03  fof(f250,plain,(
% 5.28/1.03    spl2_28 <=> ! [X1,X0,X2] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 5.28/1.03  fof(f1180,plain,(
% 5.28/1.03    spl2_85 <=> ! [X16,X17] : r1_tarski(k10_relat_1(sK1,X16),k2_xboole_0(X17,k1_relat_1(sK1)))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).
% 5.28/1.03  fof(f1188,plain,(
% 5.28/1.03    ( ! [X2,X3] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1))) ) | (~spl2_28 | ~spl2_85)),
% 5.28/1.03    inference(resolution,[],[f1181,f251])).
% 5.28/1.03  fof(f251,plain,(
% 5.28/1.03    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k6_subset_1(X0,X1),X2)) ) | ~spl2_28),
% 5.28/1.03    inference(avatar_component_clause,[],[f250])).
% 5.28/1.03  fof(f1181,plain,(
% 5.28/1.03    ( ! [X17,X16] : (r1_tarski(k10_relat_1(sK1,X16),k2_xboole_0(X17,k1_relat_1(sK1)))) ) | ~spl2_85),
% 5.28/1.03    inference(avatar_component_clause,[],[f1180])).
% 5.28/1.03  fof(f1182,plain,(
% 5.28/1.03    spl2_85 | ~spl2_36 | ~spl2_82),
% 5.28/1.03    inference(avatar_split_clause,[],[f1120,f1106,f326,f1180])).
% 5.28/1.03  fof(f326,plain,(
% 5.28/1.03    spl2_36 <=> ! [X3,X2] : (~r1_tarski(k1_relat_1(sK1),X3) | r1_tarski(k10_relat_1(sK1,X2),X3))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 5.28/1.03  fof(f1106,plain,(
% 5.28/1.03    spl2_82 <=> ! [X7,X8] : r1_tarski(X7,k2_xboole_0(X8,X7))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).
% 5.28/1.03  fof(f1120,plain,(
% 5.28/1.03    ( ! [X17,X16] : (r1_tarski(k10_relat_1(sK1,X16),k2_xboole_0(X17,k1_relat_1(sK1)))) ) | (~spl2_36 | ~spl2_82)),
% 5.28/1.03    inference(resolution,[],[f1107,f327])).
% 5.28/1.03  fof(f327,plain,(
% 5.28/1.03    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(sK1),X3) | r1_tarski(k10_relat_1(sK1,X2),X3)) ) | ~spl2_36),
% 5.28/1.03    inference(avatar_component_clause,[],[f326])).
% 5.28/1.03  fof(f1107,plain,(
% 5.28/1.03    ( ! [X8,X7] : (r1_tarski(X7,k2_xboole_0(X8,X7))) ) | ~spl2_82),
% 5.28/1.03    inference(avatar_component_clause,[],[f1106])).
% 5.28/1.03  fof(f1108,plain,(
% 5.28/1.03    spl2_82 | ~spl2_17 | ~spl2_80),
% 5.28/1.03    inference(avatar_split_clause,[],[f1075,f1065,f171,f1106])).
% 5.28/1.03  fof(f171,plain,(
% 5.28/1.03    spl2_17 <=> ! [X1,X0,X2] : (~r1_tarski(k2_xboole_0(X1,X0),X2) | r1_tarski(X0,X2))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 5.28/1.03  fof(f1075,plain,(
% 5.28/1.03    ( ! [X8,X7] : (r1_tarski(X7,k2_xboole_0(X8,X7))) ) | (~spl2_17 | ~spl2_80)),
% 5.28/1.03    inference(resolution,[],[f1066,f172])).
% 5.28/1.03  fof(f172,plain,(
% 5.28/1.03    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X1,X0),X2) | r1_tarski(X0,X2)) ) | ~spl2_17),
% 5.28/1.03    inference(avatar_component_clause,[],[f171])).
% 5.28/1.03  fof(f1067,plain,(
% 5.28/1.03    spl2_80 | ~spl2_13 | ~spl2_79),
% 5.28/1.03    inference(avatar_split_clause,[],[f1062,f1055,f134,f1065])).
% 5.28/1.03  fof(f1062,plain,(
% 5.28/1.03    ( ! [X5] : (r1_tarski(X5,X5)) ) | (~spl2_13 | ~spl2_79)),
% 5.28/1.03    inference(trivial_inequality_removal,[],[f1060])).
% 5.28/1.03  fof(f1060,plain,(
% 5.28/1.03    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X5,X5)) ) | (~spl2_13 | ~spl2_79)),
% 5.28/1.03    inference(superposition,[],[f135,f1056])).
% 5.28/1.03  fof(f1057,plain,(
% 5.28/1.03    spl2_79 | ~spl2_5 | ~spl2_6 | ~spl2_63),
% 5.28/1.03    inference(avatar_split_clause,[],[f1034,f682,f104,f100,f1055])).
% 5.28/1.03  fof(f100,plain,(
% 5.28/1.03    spl2_5 <=> ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 5.28/1.03  fof(f104,plain,(
% 5.28/1.03    spl2_6 <=> ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 5.28/1.03  fof(f682,plain,(
% 5.28/1.03    spl2_63 <=> ! [X1,X0] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 5.28/1.03  fof(f1034,plain,(
% 5.28/1.03    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) ) | (~spl2_5 | ~spl2_6 | ~spl2_63)),
% 5.28/1.03    inference(forward_demodulation,[],[f1014,f101])).
% 5.28/1.03  fof(f101,plain,(
% 5.28/1.03    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) ) | ~spl2_5),
% 5.28/1.03    inference(avatar_component_clause,[],[f100])).
% 5.28/1.03  fof(f1014,plain,(
% 5.28/1.03    ( ! [X0] : (k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,X0)) = k6_subset_1(X0,X0)) ) | (~spl2_6 | ~spl2_63)),
% 5.28/1.03    inference(superposition,[],[f683,f105])).
% 5.28/1.03  fof(f105,plain,(
% 5.28/1.03    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) ) | ~spl2_6),
% 5.28/1.03    inference(avatar_component_clause,[],[f104])).
% 5.28/1.03  fof(f683,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) ) | ~spl2_63),
% 5.28/1.03    inference(avatar_component_clause,[],[f682])).
% 5.28/1.03  fof(f891,plain,(
% 5.28/1.03    spl2_73 | ~spl2_12 | ~spl2_70),
% 5.28/1.03    inference(avatar_split_clause,[],[f864,f860,f130,f889])).
% 5.28/1.03  fof(f864,plain,(
% 5.28/1.03    ( ! [X1] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X1)) ) | (~spl2_12 | ~spl2_70)),
% 5.28/1.03    inference(resolution,[],[f861,f131])).
% 5.28/1.03  fof(f861,plain,(
% 5.28/1.03    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | ~spl2_70),
% 5.28/1.03    inference(avatar_component_clause,[],[f860])).
% 5.28/1.03  fof(f684,plain,(
% 5.28/1.03    spl2_63),
% 5.28/1.03    inference(avatar_split_clause,[],[f75,f682])).
% 5.28/1.03  fof(f75,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) )),
% 5.28/1.03    inference(definition_unfolding,[],[f55,f72,f72])).
% 5.28/1.03  fof(f72,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 5.28/1.03    inference(definition_unfolding,[],[f58,f56,f56])).
% 5.28/1.03  fof(f56,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f13])).
% 5.28/1.03  fof(f13,axiom,(
% 5.28/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 5.28/1.03  fof(f58,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.28/1.03    inference(cnf_transformation,[],[f11])).
% 5.28/1.03  fof(f11,axiom,(
% 5.28/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.28/1.03  fof(f55,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f2])).
% 5.28/1.03  fof(f2,axiom,(
% 5.28/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.28/1.03  fof(f542,plain,(
% 5.28/1.03    spl2_51),
% 5.28/1.03    inference(avatar_split_clause,[],[f63,f540])).
% 5.28/1.03  fof(f63,plain,(
% 5.28/1.03    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f33])).
% 5.28/1.03  fof(f33,plain,(
% 5.28/1.03    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 5.28/1.03    inference(flattening,[],[f32])).
% 5.28/1.03  fof(f32,plain,(
% 5.28/1.03    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 5.28/1.03    inference(ennf_transformation,[],[f20])).
% 5.28/1.03  fof(f20,axiom,(
% 5.28/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 5.28/1.03  fof(f328,plain,(
% 5.28/1.03    spl2_36 | ~spl2_11 | ~spl2_34),
% 5.28/1.03    inference(avatar_split_clause,[],[f316,f308,f126,f326])).
% 5.28/1.03  fof(f126,plain,(
% 5.28/1.03    spl2_11 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 5.28/1.03  fof(f308,plain,(
% 5.28/1.03    spl2_34 <=> ! [X1] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X1),k1_relat_1(sK1))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 5.28/1.03  fof(f316,plain,(
% 5.28/1.03    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(sK1),X3) | r1_tarski(k10_relat_1(sK1,X2),X3)) ) | (~spl2_11 | ~spl2_34)),
% 5.28/1.03    inference(superposition,[],[f127,f309])).
% 5.28/1.03  fof(f309,plain,(
% 5.28/1.03    ( ! [X1] : (k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X1),k1_relat_1(sK1))) ) | ~spl2_34),
% 5.28/1.03    inference(avatar_component_clause,[],[f308])).
% 5.28/1.03  fof(f127,plain,(
% 5.28/1.03    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl2_11),
% 5.28/1.03    inference(avatar_component_clause,[],[f126])).
% 5.28/1.03  fof(f310,plain,(
% 5.28/1.03    spl2_34 | ~spl2_10 | ~spl2_29),
% 5.28/1.03    inference(avatar_split_clause,[],[f260,f256,f122,f308])).
% 5.28/1.03  fof(f122,plain,(
% 5.28/1.03    spl2_10 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 5.28/1.03  fof(f260,plain,(
% 5.28/1.03    ( ! [X1] : (k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X1),k1_relat_1(sK1))) ) | (~spl2_10 | ~spl2_29)),
% 5.28/1.03    inference(resolution,[],[f257,f123])).
% 5.28/1.03  fof(f123,plain,(
% 5.28/1.03    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl2_10),
% 5.28/1.03    inference(avatar_component_clause,[],[f122])).
% 5.28/1.03  fof(f257,plain,(
% 5.28/1.03    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl2_29),
% 5.28/1.03    inference(avatar_component_clause,[],[f256])).
% 5.28/1.03  fof(f252,plain,(
% 5.28/1.03    spl2_28),
% 5.28/1.03    inference(avatar_split_clause,[],[f79,f250])).
% 5.28/1.03  fof(f79,plain,(
% 5.28/1.03    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 5.28/1.03    inference(definition_unfolding,[],[f68,f56])).
% 5.28/1.03  fof(f68,plain,(
% 5.28/1.03    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 5.28/1.03    inference(cnf_transformation,[],[f37])).
% 5.28/1.03  fof(f37,plain,(
% 5.28/1.03    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 5.28/1.03    inference(ennf_transformation,[],[f10])).
% 5.28/1.03  fof(f10,axiom,(
% 5.28/1.03    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 5.28/1.03  fof(f248,plain,(
% 5.28/1.03    spl2_27),
% 5.28/1.03    inference(avatar_split_clause,[],[f60,f246])).
% 5.28/1.03  fof(f60,plain,(
% 5.28/1.03    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f28])).
% 5.28/1.03  fof(f28,plain,(
% 5.28/1.03    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 5.28/1.03    inference(ennf_transformation,[],[f15])).
% 5.28/1.03  fof(f15,axiom,(
% 5.28/1.03    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 5.28/1.03  fof(f214,plain,(
% 5.28/1.03    spl2_23),
% 5.28/1.03    inference(avatar_split_clause,[],[f53,f212])).
% 5.28/1.03  fof(f53,plain,(
% 5.28/1.03    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f26])).
% 5.28/1.03  fof(f26,plain,(
% 5.28/1.03    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 5.28/1.03    inference(ennf_transformation,[],[f14])).
% 5.28/1.03  fof(f14,axiom,(
% 5.28/1.03    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 5.28/1.03  fof(f173,plain,(
% 5.28/1.03    spl2_17 | ~spl2_9 | ~spl2_11),
% 5.28/1.03    inference(avatar_split_clause,[],[f154,f126,f118,f171])).
% 5.28/1.03  fof(f118,plain,(
% 5.28/1.03    spl2_9 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.28/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 5.28/1.03  fof(f154,plain,(
% 5.28/1.03    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X1,X0),X2) | r1_tarski(X0,X2)) ) | (~spl2_9 | ~spl2_11)),
% 5.28/1.03    inference(superposition,[],[f127,f119])).
% 5.28/1.03  fof(f119,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_9),
% 5.28/1.03    inference(avatar_component_clause,[],[f118])).
% 5.28/1.03  fof(f136,plain,(
% 5.28/1.03    spl2_13),
% 5.28/1.03    inference(avatar_split_clause,[],[f78,f134])).
% 5.28/1.03  fof(f78,plain,(
% 5.28/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 5.28/1.03    inference(definition_unfolding,[],[f64,f56])).
% 5.28/1.03  fof(f64,plain,(
% 5.28/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 5.28/1.03    inference(cnf_transformation,[],[f45])).
% 5.28/1.03  fof(f45,plain,(
% 5.28/1.03    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 5.28/1.03    inference(nnf_transformation,[],[f3])).
% 5.28/1.03  fof(f3,axiom,(
% 5.28/1.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 5.28/1.03  fof(f132,plain,(
% 5.28/1.03    spl2_12),
% 5.28/1.03    inference(avatar_split_clause,[],[f77,f130])).
% 5.28/1.03  fof(f77,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 5.28/1.03    inference(definition_unfolding,[],[f65,f56])).
% 5.28/1.03  fof(f65,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f45])).
% 5.28/1.03  fof(f128,plain,(
% 5.28/1.03    spl2_11),
% 5.28/1.03    inference(avatar_split_clause,[],[f69,f126])).
% 5.28/1.03  fof(f69,plain,(
% 5.28/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f38])).
% 5.28/1.03  fof(f38,plain,(
% 5.28/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 5.28/1.03    inference(ennf_transformation,[],[f4])).
% 5.28/1.03  fof(f4,axiom,(
% 5.28/1.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 5.28/1.03  fof(f124,plain,(
% 5.28/1.03    spl2_10),
% 5.28/1.03    inference(avatar_split_clause,[],[f62,f122])).
% 5.28/1.03  fof(f62,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f31])).
% 5.28/1.03  fof(f31,plain,(
% 5.28/1.03    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 5.28/1.03    inference(ennf_transformation,[],[f5])).
% 5.28/1.03  fof(f5,axiom,(
% 5.28/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 5.28/1.03  fof(f120,plain,(
% 5.28/1.03    spl2_9),
% 5.28/1.03    inference(avatar_split_clause,[],[f57,f118])).
% 5.28/1.03  fof(f57,plain,(
% 5.28/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f1])).
% 5.28/1.03  fof(f1,axiom,(
% 5.28/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.28/1.03  fof(f115,plain,(
% 5.28/1.03    spl2_8),
% 5.28/1.03    inference(avatar_split_clause,[],[f54,f113])).
% 5.28/1.03  fof(f54,plain,(
% 5.28/1.03    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f27])).
% 5.28/1.03  fof(f27,plain,(
% 5.28/1.03    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 5.28/1.03    inference(ennf_transformation,[],[f9])).
% 5.28/1.03  fof(f9,axiom,(
% 5.28/1.03    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 5.28/1.03  fof(f111,plain,(
% 5.28/1.03    ~spl2_7),
% 5.28/1.03    inference(avatar_split_clause,[],[f49,f108])).
% 5.28/1.03  fof(f49,plain,(
% 5.28/1.03    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 5.28/1.03    inference(cnf_transformation,[],[f44])).
% 5.28/1.03  fof(f44,plain,(
% 5.28/1.03    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 5.28/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f43])).
% 5.28/1.03  fof(f43,plain,(
% 5.28/1.03    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 5.28/1.03    introduced(choice_axiom,[])).
% 5.28/1.03  fof(f25,plain,(
% 5.28/1.03    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 5.28/1.03    inference(flattening,[],[f24])).
% 5.28/1.03  fof(f24,plain,(
% 5.28/1.03    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 5.28/1.03    inference(ennf_transformation,[],[f23])).
% 5.28/1.03  fof(f23,negated_conjecture,(
% 5.28/1.03    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 5.28/1.03    inference(negated_conjecture,[],[f22])).
% 5.28/1.03  fof(f22,conjecture,(
% 5.28/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 5.28/1.03  fof(f106,plain,(
% 5.28/1.03    spl2_6),
% 5.28/1.03    inference(avatar_split_clause,[],[f74,f104])).
% 5.28/1.03  fof(f74,plain,(
% 5.28/1.03    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 5.28/1.03    inference(definition_unfolding,[],[f52,f56])).
% 5.28/1.03  fof(f52,plain,(
% 5.28/1.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.28/1.03    inference(cnf_transformation,[],[f8])).
% 5.28/1.03  fof(f8,axiom,(
% 5.28/1.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 5.28/1.03  fof(f102,plain,(
% 5.28/1.03    spl2_5),
% 5.28/1.03    inference(avatar_split_clause,[],[f73,f100])).
% 5.28/1.03  fof(f73,plain,(
% 5.28/1.03    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 5.28/1.03    inference(definition_unfolding,[],[f51,f56])).
% 5.28/1.03  fof(f51,plain,(
% 5.28/1.03    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 5.28/1.03    inference(cnf_transformation,[],[f12])).
% 5.28/1.03  fof(f12,axiom,(
% 5.28/1.03    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 5.28/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 5.28/1.03  fof(f94,plain,(
% 5.28/1.03    spl2_3),
% 5.28/1.03    inference(avatar_split_clause,[],[f48,f91])).
% 5.28/1.03  fof(f48,plain,(
% 5.28/1.03    v2_funct_1(sK1)),
% 5.28/1.03    inference(cnf_transformation,[],[f44])).
% 5.28/1.03  fof(f89,plain,(
% 5.28/1.03    spl2_2),
% 5.28/1.03    inference(avatar_split_clause,[],[f47,f86])).
% 5.28/1.03  fof(f47,plain,(
% 5.28/1.03    v1_funct_1(sK1)),
% 5.28/1.03    inference(cnf_transformation,[],[f44])).
% 5.28/1.03  fof(f84,plain,(
% 5.28/1.03    spl2_1),
% 5.28/1.03    inference(avatar_split_clause,[],[f46,f81])).
% 5.28/1.03  fof(f46,plain,(
% 5.28/1.03    v1_relat_1(sK1)),
% 5.28/1.03    inference(cnf_transformation,[],[f44])).
% 5.28/1.03  % SZS output end Proof for theBenchmark
% 5.28/1.03  % (14124)------------------------------
% 5.28/1.03  % (14124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.28/1.03  % (14124)Termination reason: Refutation
% 5.28/1.03  
% 5.28/1.03  % (14124)Memory used [KB]: 14200
% 5.28/1.03  % (14124)Time elapsed: 0.606 s
% 5.28/1.03  % (14124)------------------------------
% 5.28/1.03  % (14124)------------------------------
% 5.28/1.03  % (14114)Success in time 0.678 s
%------------------------------------------------------------------------------
