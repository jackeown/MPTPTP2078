%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 324 expanded)
%              Number of leaves         :   57 ( 150 expanded)
%              Depth                    :    9
%              Number of atoms          :  562 ( 870 expanded)
%              Number of equality atoms :  152 ( 247 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f85,f87,f92,f101,f105,f109,f113,f117,f123,f127,f135,f143,f151,f163,f167,f175,f191,f202,f206,f235,f252,f268,f278,f286,f317,f361,f374,f504,f739,f748,f879,f925,f992,f1000,f1030,f1071,f1090,f1135])).

fof(f1135,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_74
    | spl3_82 ),
    inference(avatar_contradiction_clause,[],[f1134])).

fof(f1134,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_74
    | spl3_82 ),
    inference(subsumption_resolution,[],[f990,f1124])).

fof(f1124,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_74 ),
    inference(unit_resulting_resolution,[],[f75,f104,f83,f878])).

fof(f878,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != k10_relat_1(X1,X2)
        | ~ r1_tarski(k3_xboole_0(k2_relat_1(X1),X2),k2_relat_1(X1))
        | k1_xboole_0 = k3_xboole_0(k2_relat_1(X1),X2)
        | ~ v1_relat_1(X1) )
    | ~ spl3_74 ),
    inference(avatar_component_clause,[],[f877])).

fof(f877,plain,
    ( spl3_74
  <=> ! [X1,X2] :
        ( k1_xboole_0 != k10_relat_1(X1,X2)
        | ~ r1_tarski(k3_xboole_0(k2_relat_1(X1),X2),k2_relat_1(X1))
        | k1_xboole_0 = k3_xboole_0(k2_relat_1(X1),X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f83,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_3
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f104,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f75,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f990,plain,
    ( k1_xboole_0 != k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | spl3_82 ),
    inference(avatar_component_clause,[],[f989])).

fof(f989,plain,
    ( spl3_82
  <=> k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f1090,plain,
    ( ~ spl3_76
    | ~ spl3_83 ),
    inference(avatar_contradiction_clause,[],[f1072])).

fof(f1072,plain,
    ( $false
    | ~ spl3_76
    | ~ spl3_83 ),
    inference(unit_resulting_resolution,[],[f924,f1070])).

fof(f1070,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl3_83 ),
    inference(avatar_component_clause,[],[f1068])).

fof(f1068,plain,
    ( spl3_83
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f924,plain,
    ( ! [X6] : k1_xboole_0 != k1_tarski(X6)
    | ~ spl3_76 ),
    inference(avatar_component_clause,[],[f923])).

fof(f923,plain,
    ( spl3_76
  <=> ! [X6] : k1_xboole_0 != k1_tarski(X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f1071,plain,
    ( spl3_83
    | ~ spl3_37
    | ~ spl3_82 ),
    inference(avatar_split_clause,[],[f1034,f989,f349,f1068])).

fof(f349,plain,
    ( spl3_37
  <=> k1_tarski(sK0) = k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f1034,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl3_37
    | ~ spl3_82 ),
    inference(forward_demodulation,[],[f350,f991])).

fof(f991,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ spl3_82 ),
    inference(avatar_component_clause,[],[f989])).

fof(f350,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f349])).

fof(f1030,plain,
    ( spl3_3
    | ~ spl3_31
    | ~ spl3_40
    | ~ spl3_82 ),
    inference(avatar_contradiction_clause,[],[f1029])).

fof(f1029,plain,
    ( $false
    | spl3_3
    | ~ spl3_31
    | ~ spl3_40
    | ~ spl3_82 ),
    inference(subsumption_resolution,[],[f84,f1028])).

fof(f1028,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ spl3_31
    | ~ spl3_40
    | ~ spl3_82 ),
    inference(forward_demodulation,[],[f1010,f285])).

fof(f285,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl3_31
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f1010,plain,
    ( k10_relat_1(sK1,k1_tarski(sK0)) = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl3_40
    | ~ spl3_82 ),
    inference(superposition,[],[f373,f991])).

fof(f373,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl3_40
  <=> ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f84,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f1000,plain,
    ( ~ spl3_2
    | ~ spl3_25
    | spl3_37 ),
    inference(avatar_split_clause,[],[f356,f349,f200,f78])).

fof(f78,plain,
    ( spl3_2
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f200,plain,
    ( spl3_25
  <=> ! [X1,X0] :
        ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f356,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl3_25
    | spl3_37 ),
    inference(trivial_inequality_removal,[],[f354])).

fof(f354,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl3_25
    | spl3_37 ),
    inference(superposition,[],[f351,f201])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f200])).

fof(f351,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | spl3_37 ),
    inference(avatar_component_clause,[],[f349])).

fof(f992,plain,
    ( spl3_82
    | spl3_2
    | ~ spl3_68 ),
    inference(avatar_split_clause,[],[f749,f746,f78,f989])).

fof(f746,plain,
    ( spl3_68
  <=> ! [X3,X2] :
        ( k1_xboole_0 = k3_xboole_0(X2,k1_tarski(X3))
        | r2_hidden(X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f749,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | spl3_2
    | ~ spl3_68 ),
    inference(unit_resulting_resolution,[],[f79,f747])).

fof(f747,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k3_xboole_0(X2,k1_tarski(X3))
        | r2_hidden(X3,X2) )
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f746])).

fof(f79,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f925,plain,
    ( spl3_76
    | ~ spl3_11
    | ~ spl3_26
    | ~ spl3_34
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f398,f359,f315,f204,f121,f923])).

fof(f121,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f204,plain,
    ( spl3_26
  <=> ! [X1,X0] :
        ( r2_hidden(X1,X0)
        | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f315,plain,
    ( spl3_34
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f359,plain,
    ( spl3_38
  <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f398,plain,
    ( ! [X6] : k1_xboole_0 != k1_tarski(X6)
    | ~ spl3_11
    | ~ spl3_26
    | ~ spl3_34
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f324,f397])).

fof(f397,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_34
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f396,f316])).

fof(f316,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f315])).

fof(f396,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1))
    | ~ spl3_11
    | ~ spl3_38 ),
    inference(unit_resulting_resolution,[],[f360,f122])).

fof(f122,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f360,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f359])).

fof(f324,plain,
    ( ! [X6] :
        ( k1_xboole_0 != k1_tarski(X6)
        | r2_hidden(X6,k1_xboole_0) )
    | ~ spl3_26
    | ~ spl3_34 ),
    inference(superposition,[],[f205,f316])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))
        | r2_hidden(X1,X0) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f204])).

fof(f879,plain,
    ( spl3_74
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f281,f276,f250,f877])).

fof(f250,plain,
    ( spl3_28
  <=> ! [X1,X0] :
        ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f276,plain,
    ( spl3_30
  <=> ! [X1,X0] :
        ( k1_xboole_0 != k10_relat_1(X1,X0)
        | ~ r1_tarski(X0,k2_relat_1(X1))
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f281,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != k10_relat_1(X1,X2)
        | ~ r1_tarski(k3_xboole_0(k2_relat_1(X1),X2),k2_relat_1(X1))
        | k1_xboole_0 = k3_xboole_0(k2_relat_1(X1),X2)
        | ~ v1_relat_1(X1) )
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != k10_relat_1(X1,X2)
        | ~ r1_tarski(k3_xboole_0(k2_relat_1(X1),X2),k2_relat_1(X1))
        | k1_xboole_0 = k3_xboole_0(k2_relat_1(X1),X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(superposition,[],[f277,f251])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
        | ~ v1_relat_1(X1) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f250])).

fof(f277,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k10_relat_1(X1,X0)
        | ~ r1_tarski(X0,k2_relat_1(X1))
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X1) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f276])).

fof(f748,plain,
    ( spl3_68
    | ~ spl3_7
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_49
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f740,f737,f502,f161,f149,f103,f746])).

fof(f149,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f161,plain,
    ( spl3_19
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f502,plain,
    ( spl3_49
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f737,plain,
    ( spl3_66
  <=> ! [X3,X2] :
        ( k3_xboole_0(X2,k1_tarski(X3)) = k4_xboole_0(X2,X2)
        | r2_hidden(X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f740,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k3_xboole_0(X2,k1_tarski(X3))
        | r2_hidden(X3,X2) )
    | ~ spl3_7
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_49
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f738,f509])).

fof(f509,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_7
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f508,f193])).

fof(f193,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)
    | ~ spl3_7
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f104,f150])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f508,plain,
    ( ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0)
    | ~ spl3_19
    | ~ spl3_49 ),
    inference(superposition,[],[f162,f503])).

fof(f503,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f502])).

fof(f162,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f161])).

fof(f738,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X2,k1_tarski(X3)) = k4_xboole_0(X2,X2)
        | r2_hidden(X3,X2) )
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f737])).

fof(f739,plain,
    ( spl3_66
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f228,f173,f165,f737])).

fof(f165,plain,
    ( spl3_20
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f173,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f228,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X2,k1_tarski(X3)) = k4_xboole_0(X2,X2)
        | r2_hidden(X3,X2) )
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(superposition,[],[f166,f174])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f173])).

fof(f166,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f165])).

fof(f504,plain,
    ( spl3_49
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f183,f133,f103,f502])).

fof(f133,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f183,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f104,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f374,plain,
    ( spl3_40
    | ~ spl3_1
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f270,f250,f73,f372])).

fof(f270,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))
    | ~ spl3_1
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f75,f251])).

fof(f361,plain,
    ( spl3_38
    | ~ spl3_16
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f318,f315,f141,f359])).

fof(f141,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f318,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl3_16
    | ~ spl3_34 ),
    inference(unit_resulting_resolution,[],[f316,f142])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f141])).

fof(f317,plain,
    ( spl3_34
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f269,f265,f233,f99,f89,f315])).

fof(f89,plain,
    ( spl3_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f99,plain,
    ( spl3_6
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f233,plain,
    ( spl3_27
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f265,plain,
    ( spl3_29
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f269,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f261,f267])).

fof(f267,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f265])).

fof(f261,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f255,f91])).

fof(f91,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f255,plain,
    ( ! [X0] :
        ( k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(k1_xboole_0),X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_6
    | ~ spl3_27 ),
    inference(superposition,[],[f234,f100])).

fof(f100,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f233])).

fof(f286,plain,
    ( spl3_31
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f155,f115,f73,f283])).

fof(f115,plain,
    ( spl3_10
  <=> ! [X0] :
        ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f155,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f75,f116])).

fof(f116,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f278,plain,(
    spl3_30 ),
    inference(avatar_split_clause,[],[f62,f276])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(f268,plain,
    ( spl3_29
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f217,f188,f125,f265])).

fof(f125,plain,
    ( spl3_12
  <=> ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f188,plain,
    ( spl3_23
  <=> k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f217,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(superposition,[],[f126,f190])).

fof(f190,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f188])).

fof(f126,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f252,plain,(
    spl3_28 ),
    inference(avatar_split_clause,[],[f61,f250])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f235,plain,(
    spl3_27 ),
    inference(avatar_split_clause,[],[f60,f233])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f206,plain,(
    spl3_26 ),
    inference(avatar_split_clause,[],[f65,f204])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f202,plain,(
    spl3_25 ),
    inference(avatar_split_clause,[],[f64,f200])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(f191,plain,
    ( spl3_23
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f152,f111,f73,f188])).

fof(f111,plain,
    ( spl3_9
  <=> ! [X0] :
        ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f152,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f75,f112])).

fof(f112,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f175,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f71,f173])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f167,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f55,f165])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f163,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f54,f161])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f151,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f69,f149])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f143,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f67,f141])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f135,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f63,f133])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f127,plain,
    ( spl3_12
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f118,f107,f73,f125])).

fof(f107,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f118,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f75,f108])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f123,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f57,f121])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f117,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f52,f115])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f113,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f51,f111])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f109,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f58,f107])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f105,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f53,f103])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f101,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f50,f99])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

fof(f92,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f48,f89])).

fof(f48,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f87,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f86,f82,f78])).

fof(f86,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f47,f84])).

fof(f47,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f38])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
        | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
      & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
        | r2_hidden(sK0,k2_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f85,plain,
    ( spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f46,f82,f78])).

fof(f46,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f45,f73])).

fof(f45,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:54:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (30028)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (30033)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (30025)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (30030)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (30034)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (30024)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (30022)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (30026)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (30031)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (30023)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (30032)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (30037)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (30025)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f1136,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f76,f85,f87,f92,f101,f105,f109,f113,f117,f123,f127,f135,f143,f151,f163,f167,f175,f191,f202,f206,f235,f252,f268,f278,f286,f317,f361,f374,f504,f739,f748,f879,f925,f992,f1000,f1030,f1071,f1090,f1135])).
% 0.22/0.50  fof(f1135,plain,(
% 0.22/0.50    ~spl3_1 | ~spl3_3 | ~spl3_7 | ~spl3_74 | spl3_82),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f1134])).
% 0.22/0.50  fof(f1134,plain,(
% 0.22/0.50    $false | (~spl3_1 | ~spl3_3 | ~spl3_7 | ~spl3_74 | spl3_82)),
% 0.22/0.50    inference(subsumption_resolution,[],[f990,f1124])).
% 0.22/0.50  fof(f1124,plain,(
% 0.22/0.50    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | (~spl3_1 | ~spl3_3 | ~spl3_7 | ~spl3_74)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f75,f104,f83,f878])).
% 0.22/0.50  fof(f878,plain,(
% 0.22/0.50    ( ! [X2,X1] : (k1_xboole_0 != k10_relat_1(X1,X2) | ~r1_tarski(k3_xboole_0(k2_relat_1(X1),X2),k2_relat_1(X1)) | k1_xboole_0 = k3_xboole_0(k2_relat_1(X1),X2) | ~v1_relat_1(X1)) ) | ~spl3_74),
% 0.22/0.50    inference(avatar_component_clause,[],[f877])).
% 0.22/0.50  fof(f877,plain,(
% 0.22/0.50    spl3_74 <=> ! [X1,X2] : (k1_xboole_0 != k10_relat_1(X1,X2) | ~r1_tarski(k3_xboole_0(k2_relat_1(X1),X2),k2_relat_1(X1)) | k1_xboole_0 = k3_xboole_0(k2_relat_1(X1),X2) | ~v1_relat_1(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    spl3_3 <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl3_7 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    v1_relat_1(sK1) | ~spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl3_1 <=> v1_relat_1(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f990,plain,(
% 0.22/0.50    k1_xboole_0 != k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | spl3_82),
% 0.22/0.50    inference(avatar_component_clause,[],[f989])).
% 0.22/0.50  fof(f989,plain,(
% 0.22/0.50    spl3_82 <=> k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 0.22/0.50  fof(f1090,plain,(
% 0.22/0.50    ~spl3_76 | ~spl3_83),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f1072])).
% 0.22/0.50  fof(f1072,plain,(
% 0.22/0.50    $false | (~spl3_76 | ~spl3_83)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f924,f1070])).
% 0.22/0.50  fof(f1070,plain,(
% 0.22/0.50    k1_xboole_0 = k1_tarski(sK0) | ~spl3_83),
% 0.22/0.50    inference(avatar_component_clause,[],[f1068])).
% 0.22/0.50  fof(f1068,plain,(
% 0.22/0.50    spl3_83 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 0.22/0.50  fof(f924,plain,(
% 0.22/0.50    ( ! [X6] : (k1_xboole_0 != k1_tarski(X6)) ) | ~spl3_76),
% 0.22/0.50    inference(avatar_component_clause,[],[f923])).
% 0.22/0.50  fof(f923,plain,(
% 0.22/0.50    spl3_76 <=> ! [X6] : k1_xboole_0 != k1_tarski(X6)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 0.22/0.50  fof(f1071,plain,(
% 0.22/0.50    spl3_83 | ~spl3_37 | ~spl3_82),
% 0.22/0.50    inference(avatar_split_clause,[],[f1034,f989,f349,f1068])).
% 0.22/0.50  fof(f349,plain,(
% 0.22/0.50    spl3_37 <=> k1_tarski(sK0) = k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.50  fof(f1034,plain,(
% 0.22/0.50    k1_xboole_0 = k1_tarski(sK0) | (~spl3_37 | ~spl3_82)),
% 0.22/0.50    inference(forward_demodulation,[],[f350,f991])).
% 0.22/0.50  fof(f991,plain,(
% 0.22/0.50    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~spl3_82),
% 0.22/0.50    inference(avatar_component_clause,[],[f989])).
% 0.22/0.50  fof(f350,plain,(
% 0.22/0.50    k1_tarski(sK0) = k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~spl3_37),
% 0.22/0.50    inference(avatar_component_clause,[],[f349])).
% 0.22/0.50  fof(f1030,plain,(
% 0.22/0.50    spl3_3 | ~spl3_31 | ~spl3_40 | ~spl3_82),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f1029])).
% 0.22/0.50  fof(f1029,plain,(
% 0.22/0.50    $false | (spl3_3 | ~spl3_31 | ~spl3_40 | ~spl3_82)),
% 0.22/0.50    inference(subsumption_resolution,[],[f84,f1028])).
% 0.22/0.50  fof(f1028,plain,(
% 0.22/0.50    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | (~spl3_31 | ~spl3_40 | ~spl3_82)),
% 0.22/0.50    inference(forward_demodulation,[],[f1010,f285])).
% 0.22/0.50  fof(f285,plain,(
% 0.22/0.50    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | ~spl3_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f283])).
% 0.22/0.50  fof(f283,plain,(
% 0.22/0.50    spl3_31 <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.50  fof(f1010,plain,(
% 0.22/0.50    k10_relat_1(sK1,k1_tarski(sK0)) = k10_relat_1(sK1,k1_xboole_0) | (~spl3_40 | ~spl3_82)),
% 0.22/0.50    inference(superposition,[],[f373,f991])).
% 0.22/0.50  fof(f373,plain,(
% 0.22/0.50    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))) ) | ~spl3_40),
% 0.22/0.50    inference(avatar_component_clause,[],[f372])).
% 0.22/0.50  fof(f372,plain,(
% 0.22/0.50    spl3_40 <=> ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f82])).
% 0.22/0.50  fof(f1000,plain,(
% 0.22/0.50    ~spl3_2 | ~spl3_25 | spl3_37),
% 0.22/0.50    inference(avatar_split_clause,[],[f356,f349,f200,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl3_2 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    spl3_25 <=> ! [X1,X0] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.50  fof(f356,plain,(
% 0.22/0.50    ~r2_hidden(sK0,k2_relat_1(sK1)) | (~spl3_25 | spl3_37)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f354])).
% 0.22/0.50  fof(f354,plain,(
% 0.22/0.50    k1_tarski(sK0) != k1_tarski(sK0) | ~r2_hidden(sK0,k2_relat_1(sK1)) | (~spl3_25 | spl3_37)),
% 0.22/0.50    inference(superposition,[],[f351,f201])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) ) | ~spl3_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f200])).
% 0.22/0.50  fof(f351,plain,(
% 0.22/0.50    k1_tarski(sK0) != k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | spl3_37),
% 0.22/0.50    inference(avatar_component_clause,[],[f349])).
% 0.22/0.50  fof(f992,plain,(
% 0.22/0.50    spl3_82 | spl3_2 | ~spl3_68),
% 0.22/0.50    inference(avatar_split_clause,[],[f749,f746,f78,f989])).
% 0.22/0.50  fof(f746,plain,(
% 0.22/0.50    spl3_68 <=> ! [X3,X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_tarski(X3)) | r2_hidden(X3,X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 0.22/0.50  fof(f749,plain,(
% 0.22/0.50    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | (spl3_2 | ~spl3_68)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f79,f747])).
% 0.22/0.50  fof(f747,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X2,k1_tarski(X3)) | r2_hidden(X3,X2)) ) | ~spl3_68),
% 0.22/0.50    inference(avatar_component_clause,[],[f746])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f925,plain,(
% 0.22/0.50    spl3_76 | ~spl3_11 | ~spl3_26 | ~spl3_34 | ~spl3_38),
% 0.22/0.50    inference(avatar_split_clause,[],[f398,f359,f315,f204,f121,f923])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl3_11 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    spl3_26 <=> ! [X1,X0] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.50  fof(f315,plain,(
% 0.22/0.50    spl3_34 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.50  fof(f359,plain,(
% 0.22/0.50    spl3_38 <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.22/0.50  fof(f398,plain,(
% 0.22/0.50    ( ! [X6] : (k1_xboole_0 != k1_tarski(X6)) ) | (~spl3_11 | ~spl3_26 | ~spl3_34 | ~spl3_38)),
% 0.22/0.50    inference(subsumption_resolution,[],[f324,f397])).
% 0.22/0.50  fof(f397,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_11 | ~spl3_34 | ~spl3_38)),
% 0.22/0.50    inference(forward_demodulation,[],[f396,f316])).
% 0.22/0.50  fof(f316,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl3_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f315])).
% 0.22/0.50  fof(f396,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1))) ) | (~spl3_11 | ~spl3_38)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f360,f122])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl3_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f121])).
% 0.22/0.50  fof(f360,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | ~spl3_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f359])).
% 0.22/0.50  fof(f324,plain,(
% 0.22/0.50    ( ! [X6] : (k1_xboole_0 != k1_tarski(X6) | r2_hidden(X6,k1_xboole_0)) ) | (~spl3_26 | ~spl3_34)),
% 0.22/0.50    inference(superposition,[],[f205,f316])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) | r2_hidden(X1,X0)) ) | ~spl3_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f204])).
% 0.22/0.50  fof(f879,plain,(
% 0.22/0.50    spl3_74 | ~spl3_28 | ~spl3_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f281,f276,f250,f877])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    spl3_28 <=> ! [X1,X0] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    spl3_30 <=> ! [X1,X0] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.50  fof(f281,plain,(
% 0.22/0.50    ( ! [X2,X1] : (k1_xboole_0 != k10_relat_1(X1,X2) | ~r1_tarski(k3_xboole_0(k2_relat_1(X1),X2),k2_relat_1(X1)) | k1_xboole_0 = k3_xboole_0(k2_relat_1(X1),X2) | ~v1_relat_1(X1)) ) | (~spl3_28 | ~spl3_30)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f280])).
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    ( ! [X2,X1] : (k1_xboole_0 != k10_relat_1(X1,X2) | ~r1_tarski(k3_xboole_0(k2_relat_1(X1),X2),k2_relat_1(X1)) | k1_xboole_0 = k3_xboole_0(k2_relat_1(X1),X2) | ~v1_relat_1(X1) | ~v1_relat_1(X1)) ) | (~spl3_28 | ~spl3_30)),
% 0.22/0.50    inference(superposition,[],[f277,f251])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) ) | ~spl3_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f250])).
% 0.22/0.50  fof(f277,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) ) | ~spl3_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f276])).
% 0.22/0.50  fof(f748,plain,(
% 0.22/0.50    spl3_68 | ~spl3_7 | ~spl3_18 | ~spl3_19 | ~spl3_49 | ~spl3_66),
% 0.22/0.50    inference(avatar_split_clause,[],[f740,f737,f502,f161,f149,f103,f746])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    spl3_18 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl3_19 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.50  fof(f502,plain,(
% 0.22/0.50    spl3_49 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.22/0.50  fof(f737,plain,(
% 0.22/0.50    spl3_66 <=> ! [X3,X2] : (k3_xboole_0(X2,k1_tarski(X3)) = k4_xboole_0(X2,X2) | r2_hidden(X3,X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.22/0.50  fof(f740,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X2,k1_tarski(X3)) | r2_hidden(X3,X2)) ) | (~spl3_7 | ~spl3_18 | ~spl3_19 | ~spl3_49 | ~spl3_66)),
% 0.22/0.50    inference(forward_demodulation,[],[f738,f509])).
% 0.22/0.50  fof(f509,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl3_7 | ~spl3_18 | ~spl3_19 | ~spl3_49)),
% 0.22/0.50    inference(forward_demodulation,[],[f508,f193])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) ) | (~spl3_7 | ~spl3_18)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f104,f150])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) ) | ~spl3_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f149])).
% 0.22/0.50  fof(f508,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0)) ) | (~spl3_19 | ~spl3_49)),
% 0.22/0.50    inference(superposition,[],[f162,f503])).
% 0.22/0.50  fof(f503,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) ) | ~spl3_49),
% 0.22/0.50    inference(avatar_component_clause,[],[f502])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl3_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f161])).
% 0.22/0.50  fof(f738,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k3_xboole_0(X2,k1_tarski(X3)) = k4_xboole_0(X2,X2) | r2_hidden(X3,X2)) ) | ~spl3_66),
% 0.22/0.50    inference(avatar_component_clause,[],[f737])).
% 0.22/0.50  fof(f739,plain,(
% 0.22/0.50    spl3_66 | ~spl3_20 | ~spl3_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f228,f173,f165,f737])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    spl3_20 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    spl3_22 <=> ! [X1,X0] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k3_xboole_0(X2,k1_tarski(X3)) = k4_xboole_0(X2,X2) | r2_hidden(X3,X2)) ) | (~spl3_20 | ~spl3_22)),
% 0.22/0.50    inference(superposition,[],[f166,f174])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) ) | ~spl3_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f173])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f165])).
% 0.22/0.50  fof(f504,plain,(
% 0.22/0.50    spl3_49 | ~spl3_7 | ~spl3_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f183,f133,f103,f502])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl3_14 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) ) | (~spl3_7 | ~spl3_14)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f104,f134])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl3_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f374,plain,(
% 0.22/0.50    spl3_40 | ~spl3_1 | ~spl3_28),
% 0.22/0.50    inference(avatar_split_clause,[],[f270,f250,f73,f372])).
% 0.22/0.50  fof(f270,plain,(
% 0.22/0.50    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))) ) | (~spl3_1 | ~spl3_28)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f75,f251])).
% 0.22/0.50  fof(f361,plain,(
% 0.22/0.50    spl3_38 | ~spl3_16 | ~spl3_34),
% 0.22/0.50    inference(avatar_split_clause,[],[f318,f315,f141,f359])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    spl3_16 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.50  fof(f318,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | (~spl3_16 | ~spl3_34)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f316,f142])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl3_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f141])).
% 0.22/0.50  fof(f317,plain,(
% 0.22/0.50    spl3_34 | ~spl3_4 | ~spl3_6 | ~spl3_27 | ~spl3_29),
% 0.22/0.50    inference(avatar_split_clause,[],[f269,f265,f233,f99,f89,f315])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl3_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl3_6 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    spl3_27 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.50  fof(f265,plain,(
% 0.22/0.50    spl3_29 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl3_4 | ~spl3_6 | ~spl3_27 | ~spl3_29)),
% 0.22/0.50    inference(subsumption_resolution,[],[f261,f267])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    v1_relat_1(k1_xboole_0) | ~spl3_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f265])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl3_4 | ~spl3_6 | ~spl3_27)),
% 0.22/0.50    inference(forward_demodulation,[],[f255,f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f89])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl3_6 | ~spl3_27)),
% 0.22/0.50    inference(superposition,[],[f234,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl3_27),
% 0.22/0.50    inference(avatar_component_clause,[],[f233])).
% 0.22/0.50  fof(f286,plain,(
% 0.22/0.50    spl3_31 | ~spl3_1 | ~spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f155,f115,f73,f283])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    spl3_10 <=> ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | (~spl3_1 | ~spl3_10)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f75,f116])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f115])).
% 0.22/0.50  fof(f278,plain,(
% 0.22/0.50    spl3_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f62,f276])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).
% 0.22/0.50  fof(f268,plain,(
% 0.22/0.50    spl3_29 | ~spl3_12 | ~spl3_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f217,f188,f125,f265])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    spl3_12 <=> ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    spl3_23 <=> k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    v1_relat_1(k1_xboole_0) | (~spl3_12 | ~spl3_23)),
% 0.22/0.50    inference(superposition,[],[f126,f190])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) | ~spl3_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f188])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f125])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    spl3_28),
% 0.22/0.50    inference(avatar_split_clause,[],[f61,f250])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    spl3_27),
% 0.22/0.50    inference(avatar_split_clause,[],[f60,f233])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    spl3_26),
% 0.22/0.50    inference(avatar_split_clause,[],[f65,f204])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    spl3_25),
% 0.22/0.50    inference(avatar_split_clause,[],[f64,f200])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    spl3_23 | ~spl3_1 | ~spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f152,f111,f73,f188])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl3_9 <=> ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) | (~spl3_1 | ~spl3_9)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f75,f112])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f111])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    spl3_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f71,f173])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    spl3_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f55,f165])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl3_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f54,f161])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    spl3_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f69,f149])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    spl3_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f67,f141])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    spl3_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f63,f133])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    spl3_12 | ~spl3_1 | ~spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f118,f107,f73,f125])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    spl3_8 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | (~spl3_1 | ~spl3_8)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f75,f108])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f107])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f57,f121])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f52,f115])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f51,f111])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f58,f107])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f53,f103])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f50,f99])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f48,f89])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,axiom,(
% 0.22/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ~spl3_2 | spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f86,f82,f78])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl3_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f47,f84])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    (k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.22/0.50    inference(negated_conjecture,[],[f20])).
% 0.22/0.50  fof(f20,conjecture,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    spl3_2 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f46,f82,f78])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f39])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f45,f73])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    v1_relat_1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f39])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (30025)------------------------------
% 0.22/0.50  % (30025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (30025)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (30025)Memory used [KB]: 6780
% 0.22/0.50  % (30025)Time elapsed: 0.036 s
% 0.22/0.50  % (30025)------------------------------
% 0.22/0.50  % (30025)------------------------------
% 0.22/0.51  % (30019)Success in time 0.144 s
%------------------------------------------------------------------------------
