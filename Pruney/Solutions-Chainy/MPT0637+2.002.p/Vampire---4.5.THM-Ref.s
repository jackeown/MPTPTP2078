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
% DateTime   : Thu Dec  3 12:52:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 266 expanded)
%              Number of leaves         :   43 ( 127 expanded)
%              Depth                    :    9
%              Number of atoms          :  484 ( 753 expanded)
%              Number of equality atoms :   79 ( 139 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f97,f101,f105,f117,f135,f139,f143,f151,f155,f184,f196,f239,f244,f254,f306,f320,f328,f340,f351,f465,f763,f950,f1012,f1144,f2982,f3177])).

fof(f3177,plain,
    ( ~ spl2_2
    | spl2_30
    | ~ spl2_86
    | ~ spl2_95
    | ~ spl2_136 ),
    inference(avatar_contradiction_clause,[],[f3176])).

fof(f3176,plain,
    ( $false
    | ~ spl2_2
    | spl2_30
    | ~ spl2_86
    | ~ spl2_95
    | ~ spl2_136 ),
    inference(subsumption_resolution,[],[f238,f3175])).

fof(f3175,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_2
    | ~ spl2_86
    | ~ spl2_95
    | ~ spl2_136 ),
    inference(forward_demodulation,[],[f3164,f1011])).

fof(f1011,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl2_86 ),
    inference(avatar_component_clause,[],[f1010])).

fof(f1010,plain,
    ( spl2_86
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).

fof(f3164,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_95
    | ~ spl2_136 ),
    inference(unit_resulting_resolution,[],[f72,f2981,f1143])).

fof(f1143,plain,
    ( ! [X2,X3] :
        ( k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3)
        | ~ r1_tarski(X3,X2)
        | ~ v1_relat_1(k6_relat_1(X3)) )
    | ~ spl2_95 ),
    inference(avatar_component_clause,[],[f1142])).

fof(f1142,plain,
    ( spl2_95
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X3,X2)
        | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3)
        | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).

fof(f2981,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_136 ),
    inference(avatar_component_clause,[],[f2980])).

fof(f2980,plain,
    ( spl2_136
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).

fof(f72,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_2
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f238,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_30 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl2_30
  <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f2982,plain,
    ( spl2_136
    | ~ spl2_2
    | ~ spl2_81 ),
    inference(avatar_split_clause,[],[f960,f948,f71,f2980])).

fof(f948,plain,
    ( spl2_81
  <=> ! [X7,X6] :
        ( r1_tarski(k3_xboole_0(X7,X6),X7)
        | ~ v1_relat_1(k6_relat_1(X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).

fof(f960,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_2
    | ~ spl2_81 ),
    inference(unit_resulting_resolution,[],[f72,f949])).

fof(f949,plain,
    ( ! [X6,X7] :
        ( r1_tarski(k3_xboole_0(X7,X6),X7)
        | ~ v1_relat_1(k6_relat_1(X7)) )
    | ~ spl2_81 ),
    inference(avatar_component_clause,[],[f948])).

fof(f1144,plain,
    ( spl2_95
    | ~ spl2_4
    | ~ spl2_20
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f334,f326,f153,f79,f1142])).

fof(f79,plain,
    ( spl2_4
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f153,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f326,plain,
    ( spl2_41
  <=> ! [X1,X0] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f334,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X3,X2)
        | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3)
        | ~ v1_relat_1(k6_relat_1(X3)) )
    | ~ spl2_4
    | ~ spl2_20
    | ~ spl2_41 ),
    inference(forward_demodulation,[],[f329,f80])).

fof(f80,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f329,plain,
    ( ! [X2,X3] :
        ( k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3)
        | ~ r1_tarski(k2_relat_1(k6_relat_1(X3)),X2)
        | ~ v1_relat_1(k6_relat_1(X3)) )
    | ~ spl2_20
    | ~ spl2_41 ),
    inference(superposition,[],[f327,f154])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f153])).

fof(f327,plain,
    ( ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f326])).

fof(f1012,plain,
    ( spl2_86
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f361,f349,f75,f71,f1010])).

fof(f75,plain,
    ( spl2_3
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f349,plain,
    ( spl2_43
  <=> ! [X1,X0] :
        ( k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f361,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_43 ),
    inference(forward_demodulation,[],[f352,f76])).

fof(f76,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f352,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))
    | ~ spl2_2
    | ~ spl2_43 ),
    inference(unit_resulting_resolution,[],[f72,f350])).

fof(f350,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f349])).

fof(f950,plain,
    ( spl2_81
    | ~ spl2_31
    | ~ spl2_41
    | ~ spl2_42
    | ~ spl2_53
    | ~ spl2_66 ),
    inference(avatar_split_clause,[],[f774,f761,f463,f338,f326,f252,f948])).

fof(f252,plain,
    ( spl2_31
  <=> ! [X1,X0] :
        ( r1_tarski(k8_relat_1(X1,X0),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f338,plain,
    ( spl2_42
  <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f463,plain,
    ( spl2_53
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ r1_tarski(X1,k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f761,plain,
    ( spl2_66
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k8_relat_1(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f774,plain,
    ( ! [X6,X7] :
        ( r1_tarski(k3_xboole_0(X7,X6),X7)
        | ~ v1_relat_1(k6_relat_1(X7)) )
    | ~ spl2_31
    | ~ spl2_41
    | ~ spl2_42
    | ~ spl2_53
    | ~ spl2_66 ),
    inference(subsumption_resolution,[],[f489,f771])).

fof(f771,plain,
    ( ! [X2,X3] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X3))
        | ~ v1_relat_1(k6_relat_1(X3)) )
    | ~ spl2_41
    | ~ spl2_66 ),
    inference(superposition,[],[f762,f327])).

fof(f762,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k8_relat_1(X1,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f761])).

fof(f489,plain,
    ( ! [X6,X7] :
        ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X6),X7))
        | r1_tarski(k3_xboole_0(X7,X6),X7)
        | ~ v1_relat_1(k6_relat_1(X7)) )
    | ~ spl2_31
    | ~ spl2_41
    | ~ spl2_42
    | ~ spl2_53 ),
    inference(forward_demodulation,[],[f488,f327])).

fof(f488,plain,
    ( ! [X6,X7] :
        ( r1_tarski(k3_xboole_0(X7,X6),X7)
        | ~ v1_relat_1(k6_relat_1(X7))
        | ~ v1_relat_1(k8_relat_1(X6,k6_relat_1(X7))) )
    | ~ spl2_31
    | ~ spl2_41
    | ~ spl2_42
    | ~ spl2_53 ),
    inference(forward_demodulation,[],[f487,f339])).

fof(f339,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f338])).

fof(f487,plain,
    ( ! [X6,X7] :
        ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7)),X7)
        | ~ v1_relat_1(k6_relat_1(X7))
        | ~ v1_relat_1(k8_relat_1(X6,k6_relat_1(X7))) )
    | ~ spl2_31
    | ~ spl2_41
    | ~ spl2_53 ),
    inference(forward_demodulation,[],[f476,f327])).

fof(f476,plain,
    ( ! [X6,X7] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X6,k6_relat_1(X7))),X7)
        | ~ v1_relat_1(k6_relat_1(X7))
        | ~ v1_relat_1(k8_relat_1(X6,k6_relat_1(X7))) )
    | ~ spl2_31
    | ~ spl2_53 ),
    inference(duplicate_literal_removal,[],[f471])).

fof(f471,plain,
    ( ! [X6,X7] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X6,k6_relat_1(X7))),X7)
        | ~ v1_relat_1(k6_relat_1(X7))
        | ~ v1_relat_1(k8_relat_1(X6,k6_relat_1(X7)))
        | ~ v1_relat_1(k6_relat_1(X7)) )
    | ~ spl2_31
    | ~ spl2_53 ),
    inference(resolution,[],[f464,f253])).

fof(f253,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k8_relat_1(X1,X0),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f252])).

fof(f464,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k6_relat_1(X0))
        | r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(X1) )
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f463])).

fof(f763,plain,
    ( spl2_66
    | ~ spl2_15
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f259,f252,f133,f761])).

fof(f133,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f259,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k8_relat_1(X1,X0)) )
    | ~ spl2_15
    | ~ spl2_31 ),
    inference(duplicate_literal_removal,[],[f256])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | v1_relat_1(k8_relat_1(X1,X0)) )
    | ~ spl2_15
    | ~ spl2_31 ),
    inference(resolution,[],[f253,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | v1_relat_1(X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f465,plain,
    ( spl2_53
    | ~ spl2_4
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f201,f182,f79,f463])).

fof(f182,plain,
    ( spl2_24
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ r1_tarski(X1,k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(X1) )
    | ~ spl2_4
    | ~ spl2_24 ),
    inference(superposition,[],[f183,f80])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f182])).

fof(f351,plain,
    ( spl2_43
    | ~ spl2_9
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f221,f194,f99,f349])).

fof(f99,plain,
    ( spl2_9
  <=> ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f194,plain,
    ( spl2_26
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_9
    | ~ spl2_26 ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_9
    | ~ spl2_26 ),
    inference(superposition,[],[f195,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f195,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f194])).

fof(f340,plain,
    ( spl2_42
    | ~ spl2_2
    | ~ spl2_17
    | ~ spl2_38
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f321,f318,f304,f141,f71,f338])).

fof(f141,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f304,plain,
    ( spl2_38
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f318,plain,
    ( spl2_40
  <=> ! [X1,X0] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f321,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_2
    | ~ spl2_17
    | ~ spl2_38
    | ~ spl2_40 ),
    inference(forward_demodulation,[],[f319,f307])).

fof(f307,plain,
    ( ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_2
    | ~ spl2_17
    | ~ spl2_38 ),
    inference(forward_demodulation,[],[f305,f161])).

fof(f161,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(unit_resulting_resolution,[],[f72,f142])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f141])).

fof(f305,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f304])).

fof(f319,plain,
    ( ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k3_xboole_0(X1,X0)
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f318])).

fof(f328,plain,
    ( spl2_41
    | ~ spl2_2
    | ~ spl2_17
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f307,f304,f141,f71,f326])).

fof(f320,plain,
    ( spl2_40
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f190,f149,f79,f71,f318])).

fof(f149,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f190,plain,
    ( ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k3_xboole_0(X1,X0)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f189,f80])).

fof(f189,plain,
    ( ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k3_xboole_0(k2_relat_1(k6_relat_1(X1)),X0)
    | ~ spl2_2
    | ~ spl2_19 ),
    inference(unit_resulting_resolution,[],[f72,f150])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f149])).

fof(f306,plain,
    ( spl2_38
    | ~ spl2_2
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f156,f137,f71,f304])).

fof(f137,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f156,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))
    | ~ spl2_2
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f72,f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f137])).

fof(f254,plain,
    ( spl2_31
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f160,f137,f115,f252])).

fof(f115,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k8_relat_1(X1,X0),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k8_relat_1(X1,X0),X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(superposition,[],[f116,f138])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f244,plain,
    ( ~ spl2_2
    | spl2_29 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl2_2
    | spl2_29 ),
    inference(unit_resulting_resolution,[],[f72,f234])).

fof(f234,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl2_29 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl2_29
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f239,plain,
    ( ~ spl2_29
    | ~ spl2_30
    | spl2_1
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f163,f141,f66,f236,f232])).

fof(f66,plain,
    ( spl2_1
  <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f163,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | spl2_1
    | ~ spl2_17 ),
    inference(superposition,[],[f68,f142])).

fof(f68,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f196,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f62,f194])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f184,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f49,f182])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f155,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f58,f153])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f151,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f55,f149])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f143,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f54,f141])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f139,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f53,f137])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f135,plain,
    ( spl2_15
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f129,f103,f95,f133])).

fof(f95,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f103,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(resolution,[],[f104,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f117,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f56,f115])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f105,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f50,f103])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f101,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f46,f99])).

fof(f46,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f97,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f60,f95])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f81,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f44,f79])).

fof(f44,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f77,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f43,f75])).

fof(f43,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f41,f71])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f69,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f40,f66])).

fof(f40,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f37])).

fof(f37,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:36:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (12782)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (12781)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (12780)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (12792)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (12791)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (12777)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (12783)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (12785)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (12790)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (12789)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (12776)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (12787)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (12793)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (12778)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (12794)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (12788)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (12788)Refutation not found, incomplete strategy% (12788)------------------------------
% 0.22/0.50  % (12788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12788)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12788)Memory used [KB]: 10618
% 0.22/0.50  % (12788)Time elapsed: 0.083 s
% 0.22/0.50  % (12788)------------------------------
% 0.22/0.50  % (12788)------------------------------
% 0.22/0.50  % (12784)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (12786)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.57  % (12782)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f3182,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f97,f101,f105,f117,f135,f139,f143,f151,f155,f184,f196,f239,f244,f254,f306,f320,f328,f340,f351,f465,f763,f950,f1012,f1144,f2982,f3177])).
% 0.22/0.57  fof(f3177,plain,(
% 0.22/0.57    ~spl2_2 | spl2_30 | ~spl2_86 | ~spl2_95 | ~spl2_136),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f3176])).
% 0.22/0.57  fof(f3176,plain,(
% 0.22/0.57    $false | (~spl2_2 | spl2_30 | ~spl2_86 | ~spl2_95 | ~spl2_136)),
% 0.22/0.57    inference(subsumption_resolution,[],[f238,f3175])).
% 0.22/0.57  fof(f3175,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_2 | ~spl2_86 | ~spl2_95 | ~spl2_136)),
% 0.22/0.57    inference(forward_demodulation,[],[f3164,f1011])).
% 0.22/0.57  fof(f1011,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | ~spl2_86),
% 0.22/0.57    inference(avatar_component_clause,[],[f1010])).
% 0.22/0.57  fof(f1010,plain,(
% 0.22/0.57    spl2_86 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).
% 0.22/0.57  fof(f3164,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_95 | ~spl2_136)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f72,f2981,f1143])).
% 0.22/0.57  fof(f1143,plain,(
% 0.22/0.57    ( ! [X2,X3] : (k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3) | ~r1_tarski(X3,X2) | ~v1_relat_1(k6_relat_1(X3))) ) | ~spl2_95),
% 0.22/0.57    inference(avatar_component_clause,[],[f1142])).
% 0.22/0.57  fof(f1142,plain,(
% 0.22/0.57    spl2_95 <=> ! [X3,X2] : (~r1_tarski(X3,X2) | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3) | ~v1_relat_1(k6_relat_1(X3)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).
% 0.22/0.57  fof(f2981,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_136),
% 0.22/0.57    inference(avatar_component_clause,[],[f2980])).
% 0.22/0.57  fof(f2980,plain,(
% 0.22/0.57    spl2_136 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).
% 0.22/0.57  fof(f72,plain,(
% 0.22/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f71])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    spl2_2 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.57  fof(f238,plain,(
% 0.22/0.57    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_30),
% 0.22/0.57    inference(avatar_component_clause,[],[f236])).
% 0.22/0.57  fof(f236,plain,(
% 0.22/0.57    spl2_30 <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.57  fof(f2982,plain,(
% 0.22/0.57    spl2_136 | ~spl2_2 | ~spl2_81),
% 0.22/0.57    inference(avatar_split_clause,[],[f960,f948,f71,f2980])).
% 0.22/0.57  fof(f948,plain,(
% 0.22/0.57    spl2_81 <=> ! [X7,X6] : (r1_tarski(k3_xboole_0(X7,X6),X7) | ~v1_relat_1(k6_relat_1(X7)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).
% 0.22/0.57  fof(f960,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | (~spl2_2 | ~spl2_81)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f72,f949])).
% 0.22/0.57  fof(f949,plain,(
% 0.22/0.57    ( ! [X6,X7] : (r1_tarski(k3_xboole_0(X7,X6),X7) | ~v1_relat_1(k6_relat_1(X7))) ) | ~spl2_81),
% 0.22/0.57    inference(avatar_component_clause,[],[f948])).
% 0.22/0.57  fof(f1144,plain,(
% 0.22/0.57    spl2_95 | ~spl2_4 | ~spl2_20 | ~spl2_41),
% 0.22/0.57    inference(avatar_split_clause,[],[f334,f326,f153,f79,f1142])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    spl2_4 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.57  fof(f153,plain,(
% 0.22/0.57    spl2_20 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.57  fof(f326,plain,(
% 0.22/0.57    spl2_41 <=> ! [X1,X0] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.22/0.57  fof(f334,plain,(
% 0.22/0.57    ( ! [X2,X3] : (~r1_tarski(X3,X2) | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3) | ~v1_relat_1(k6_relat_1(X3))) ) | (~spl2_4 | ~spl2_20 | ~spl2_41)),
% 0.22/0.57    inference(forward_demodulation,[],[f329,f80])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f79])).
% 0.22/0.57  fof(f329,plain,(
% 0.22/0.57    ( ! [X2,X3] : (k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3) | ~r1_tarski(k2_relat_1(k6_relat_1(X3)),X2) | ~v1_relat_1(k6_relat_1(X3))) ) | (~spl2_20 | ~spl2_41)),
% 0.22/0.57    inference(superposition,[],[f327,f154])).
% 0.22/0.57  fof(f154,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_20),
% 0.22/0.57    inference(avatar_component_clause,[],[f153])).
% 0.22/0.57  fof(f327,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_41),
% 0.22/0.57    inference(avatar_component_clause,[],[f326])).
% 0.22/0.57  fof(f1012,plain,(
% 0.22/0.57    spl2_86 | ~spl2_2 | ~spl2_3 | ~spl2_43),
% 0.22/0.57    inference(avatar_split_clause,[],[f361,f349,f75,f71,f1010])).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    spl2_3 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.57  fof(f349,plain,(
% 0.22/0.57    spl2_43 <=> ! [X1,X0] : (k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | ~v1_relat_1(X0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.22/0.57  fof(f361,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_3 | ~spl2_43)),
% 0.22/0.57    inference(forward_demodulation,[],[f352,f76])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f75])).
% 0.22/0.57  fof(f352,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) ) | (~spl2_2 | ~spl2_43)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f72,f350])).
% 0.22/0.57  fof(f350,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | ~v1_relat_1(X0)) ) | ~spl2_43),
% 0.22/0.57    inference(avatar_component_clause,[],[f349])).
% 0.22/0.57  fof(f950,plain,(
% 0.22/0.57    spl2_81 | ~spl2_31 | ~spl2_41 | ~spl2_42 | ~spl2_53 | ~spl2_66),
% 0.22/0.57    inference(avatar_split_clause,[],[f774,f761,f463,f338,f326,f252,f948])).
% 0.22/0.57  fof(f252,plain,(
% 0.22/0.57    spl2_31 <=> ! [X1,X0] : (r1_tarski(k8_relat_1(X1,X0),X0) | ~v1_relat_1(X0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.22/0.57  fof(f338,plain,(
% 0.22/0.57    spl2_42 <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.22/0.57  fof(f463,plain,(
% 0.22/0.57    spl2_53 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X1),X0) | ~r1_tarski(X1,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.22/0.57  fof(f761,plain,(
% 0.22/0.57    spl2_66 <=> ! [X1,X0] : (~v1_relat_1(X0) | v1_relat_1(k8_relat_1(X1,X0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 0.22/0.57  fof(f774,plain,(
% 0.22/0.57    ( ! [X6,X7] : (r1_tarski(k3_xboole_0(X7,X6),X7) | ~v1_relat_1(k6_relat_1(X7))) ) | (~spl2_31 | ~spl2_41 | ~spl2_42 | ~spl2_53 | ~spl2_66)),
% 0.22/0.57    inference(subsumption_resolution,[],[f489,f771])).
% 0.22/0.57  fof(f771,plain,(
% 0.22/0.57    ( ! [X2,X3] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(k6_relat_1(X3))) ) | (~spl2_41 | ~spl2_66)),
% 0.22/0.57    inference(superposition,[],[f762,f327])).
% 0.22/0.57  fof(f762,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X1,X0)) | ~v1_relat_1(X0)) ) | ~spl2_66),
% 0.22/0.57    inference(avatar_component_clause,[],[f761])).
% 0.22/0.57  fof(f489,plain,(
% 0.22/0.57    ( ! [X6,X7] : (~v1_relat_1(k7_relat_1(k6_relat_1(X6),X7)) | r1_tarski(k3_xboole_0(X7,X6),X7) | ~v1_relat_1(k6_relat_1(X7))) ) | (~spl2_31 | ~spl2_41 | ~spl2_42 | ~spl2_53)),
% 0.22/0.57    inference(forward_demodulation,[],[f488,f327])).
% 0.22/0.57  fof(f488,plain,(
% 0.22/0.57    ( ! [X6,X7] : (r1_tarski(k3_xboole_0(X7,X6),X7) | ~v1_relat_1(k6_relat_1(X7)) | ~v1_relat_1(k8_relat_1(X6,k6_relat_1(X7)))) ) | (~spl2_31 | ~spl2_41 | ~spl2_42 | ~spl2_53)),
% 0.22/0.57    inference(forward_demodulation,[],[f487,f339])).
% 0.22/0.57  fof(f339,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_42),
% 0.22/0.57    inference(avatar_component_clause,[],[f338])).
% 0.22/0.57  fof(f487,plain,(
% 0.22/0.57    ( ! [X6,X7] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7)),X7) | ~v1_relat_1(k6_relat_1(X7)) | ~v1_relat_1(k8_relat_1(X6,k6_relat_1(X7)))) ) | (~spl2_31 | ~spl2_41 | ~spl2_53)),
% 0.22/0.57    inference(forward_demodulation,[],[f476,f327])).
% 0.22/0.57  fof(f476,plain,(
% 0.22/0.57    ( ! [X6,X7] : (r1_tarski(k2_relat_1(k8_relat_1(X6,k6_relat_1(X7))),X7) | ~v1_relat_1(k6_relat_1(X7)) | ~v1_relat_1(k8_relat_1(X6,k6_relat_1(X7)))) ) | (~spl2_31 | ~spl2_53)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f471])).
% 0.22/0.57  fof(f471,plain,(
% 0.22/0.57    ( ! [X6,X7] : (r1_tarski(k2_relat_1(k8_relat_1(X6,k6_relat_1(X7))),X7) | ~v1_relat_1(k6_relat_1(X7)) | ~v1_relat_1(k8_relat_1(X6,k6_relat_1(X7))) | ~v1_relat_1(k6_relat_1(X7))) ) | (~spl2_31 | ~spl2_53)),
% 0.22/0.57    inference(resolution,[],[f464,f253])).
% 0.22/0.57  fof(f253,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X1,X0),X0) | ~v1_relat_1(X0)) ) | ~spl2_31),
% 0.22/0.57    inference(avatar_component_clause,[],[f252])).
% 0.22/0.57  fof(f464,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k6_relat_1(X0)) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) ) | ~spl2_53),
% 0.22/0.57    inference(avatar_component_clause,[],[f463])).
% 0.22/0.57  fof(f763,plain,(
% 0.22/0.57    spl2_66 | ~spl2_15 | ~spl2_31),
% 0.22/0.57    inference(avatar_split_clause,[],[f259,f252,f133,f761])).
% 0.22/0.57  fof(f133,plain,(
% 0.22/0.57    spl2_15 <=> ! [X1,X0] : (v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.57  fof(f259,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k8_relat_1(X1,X0))) ) | (~spl2_15 | ~spl2_31)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f256])).
% 0.22/0.57  fof(f256,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k8_relat_1(X1,X0))) ) | (~spl2_15 | ~spl2_31)),
% 0.22/0.57    inference(resolution,[],[f253,f134])).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) ) | ~spl2_15),
% 0.22/0.57    inference(avatar_component_clause,[],[f133])).
% 0.22/0.57  fof(f465,plain,(
% 0.22/0.57    spl2_53 | ~spl2_4 | ~spl2_24),
% 0.22/0.57    inference(avatar_split_clause,[],[f201,f182,f79,f463])).
% 0.22/0.57  fof(f182,plain,(
% 0.22/0.57    spl2_24 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.57  fof(f201,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~r1_tarski(X1,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) ) | (~spl2_4 | ~spl2_24)),
% 0.22/0.57    inference(superposition,[],[f183,f80])).
% 0.22/0.57  fof(f183,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_24),
% 0.22/0.57    inference(avatar_component_clause,[],[f182])).
% 0.22/0.57  fof(f351,plain,(
% 0.22/0.57    spl2_43 | ~spl2_9 | ~spl2_26),
% 0.22/0.57    inference(avatar_split_clause,[],[f221,f194,f99,f349])).
% 0.22/0.57  fof(f99,plain,(
% 0.22/0.57    spl2_9 <=> ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.57  fof(f194,plain,(
% 0.22/0.57    spl2_26 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.57  fof(f221,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | ~v1_relat_1(X0)) ) | (~spl2_9 | ~spl2_26)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f217])).
% 0.22/0.57  fof(f217,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_9 | ~spl2_26)),
% 0.22/0.57    inference(superposition,[],[f195,f100])).
% 0.22/0.57  fof(f100,plain,(
% 0.22/0.57    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) ) | ~spl2_9),
% 0.22/0.57    inference(avatar_component_clause,[],[f99])).
% 0.22/0.57  fof(f195,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) ) | ~spl2_26),
% 0.22/0.57    inference(avatar_component_clause,[],[f194])).
% 0.22/0.57  fof(f340,plain,(
% 0.22/0.57    spl2_42 | ~spl2_2 | ~spl2_17 | ~spl2_38 | ~spl2_40),
% 0.22/0.57    inference(avatar_split_clause,[],[f321,f318,f304,f141,f71,f338])).
% 0.22/0.57  fof(f141,plain,(
% 0.22/0.57    spl2_17 <=> ! [X1,X0] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.57  fof(f304,plain,(
% 0.22/0.57    spl2_38 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.22/0.57  fof(f318,plain,(
% 0.22/0.57    spl2_40 <=> ! [X1,X0] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k3_xboole_0(X1,X0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.22/0.57  fof(f321,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_2 | ~spl2_17 | ~spl2_38 | ~spl2_40)),
% 0.22/0.57    inference(forward_demodulation,[],[f319,f307])).
% 0.22/0.57  fof(f307,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_2 | ~spl2_17 | ~spl2_38)),
% 0.22/0.57    inference(forward_demodulation,[],[f305,f161])).
% 0.22/0.57  fof(f161,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_2 | ~spl2_17)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f72,f142])).
% 0.22/0.57  fof(f142,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl2_17),
% 0.22/0.57    inference(avatar_component_clause,[],[f141])).
% 0.22/0.57  fof(f305,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_38),
% 0.22/0.57    inference(avatar_component_clause,[],[f304])).
% 0.22/0.57  fof(f319,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k3_xboole_0(X1,X0)) ) | ~spl2_40),
% 0.22/0.57    inference(avatar_component_clause,[],[f318])).
% 0.22/0.57  fof(f328,plain,(
% 0.22/0.57    spl2_41 | ~spl2_2 | ~spl2_17 | ~spl2_38),
% 0.22/0.57    inference(avatar_split_clause,[],[f307,f304,f141,f71,f326])).
% 0.22/0.57  fof(f320,plain,(
% 0.22/0.57    spl2_40 | ~spl2_2 | ~spl2_4 | ~spl2_19),
% 0.22/0.57    inference(avatar_split_clause,[],[f190,f149,f79,f71,f318])).
% 0.22/0.57  fof(f149,plain,(
% 0.22/0.57    spl2_19 <=> ! [X1,X0] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.57  fof(f190,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k3_xboole_0(X1,X0)) ) | (~spl2_2 | ~spl2_4 | ~spl2_19)),
% 0.22/0.57    inference(forward_demodulation,[],[f189,f80])).
% 0.22/0.57  fof(f189,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k3_xboole_0(k2_relat_1(k6_relat_1(X1)),X0)) ) | (~spl2_2 | ~spl2_19)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f72,f150])).
% 0.22/0.57  fof(f150,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_19),
% 0.22/0.57    inference(avatar_component_clause,[],[f149])).
% 0.22/0.57  fof(f306,plain,(
% 0.22/0.57    spl2_38 | ~spl2_2 | ~spl2_16),
% 0.22/0.57    inference(avatar_split_clause,[],[f156,f137,f71,f304])).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    spl2_16 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.57  fof(f156,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_16)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f72,f138])).
% 0.22/0.57  fof(f138,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) ) | ~spl2_16),
% 0.22/0.57    inference(avatar_component_clause,[],[f137])).
% 0.22/0.57  fof(f254,plain,(
% 0.22/0.57    spl2_31 | ~spl2_13 | ~spl2_16),
% 0.22/0.57    inference(avatar_split_clause,[],[f160,f137,f115,f252])).
% 0.22/0.57  fof(f115,plain,(
% 0.22/0.57    spl2_13 <=> ! [X1,X0] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.57  fof(f160,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X1,X0),X0) | ~v1_relat_1(X0)) ) | (~spl2_13 | ~spl2_16)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f158])).
% 0.22/0.57  fof(f158,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X1,X0),X0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_13 | ~spl2_16)),
% 0.22/0.57    inference(superposition,[],[f116,f138])).
% 0.22/0.57  fof(f116,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) ) | ~spl2_13),
% 0.22/0.57    inference(avatar_component_clause,[],[f115])).
% 0.22/0.57  fof(f244,plain,(
% 0.22/0.57    ~spl2_2 | spl2_29),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f240])).
% 0.22/0.57  fof(f240,plain,(
% 0.22/0.57    $false | (~spl2_2 | spl2_29)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f72,f234])).
% 0.22/0.57  fof(f234,plain,(
% 0.22/0.57    ~v1_relat_1(k6_relat_1(sK0)) | spl2_29),
% 0.22/0.57    inference(avatar_component_clause,[],[f232])).
% 0.22/0.57  fof(f232,plain,(
% 0.22/0.57    spl2_29 <=> v1_relat_1(k6_relat_1(sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.22/0.57  fof(f239,plain,(
% 0.22/0.57    ~spl2_29 | ~spl2_30 | spl2_1 | ~spl2_17),
% 0.22/0.57    inference(avatar_split_clause,[],[f163,f141,f66,f236,f232])).
% 0.22/0.57  fof(f66,plain,(
% 0.22/0.57    spl2_1 <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.57  fof(f163,plain,(
% 0.22/0.57    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | (spl2_1 | ~spl2_17)),
% 0.22/0.57    inference(superposition,[],[f68,f142])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) | spl2_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f66])).
% 0.22/0.57  fof(f196,plain,(
% 0.22/0.57    spl2_26),
% 0.22/0.57    inference(avatar_split_clause,[],[f62,f194])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.57  fof(f184,plain,(
% 0.22/0.57    spl2_24),
% 0.22/0.57    inference(avatar_split_clause,[],[f49,f182])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.57  fof(f155,plain,(
% 0.22/0.57    spl2_20),
% 0.22/0.57    inference(avatar_split_clause,[],[f58,f153])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(flattening,[],[f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.22/0.57  fof(f151,plain,(
% 0.22/0.57    spl2_19),
% 0.22/0.57    inference(avatar_split_clause,[],[f55,f149])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 0.22/0.57  fof(f143,plain,(
% 0.22/0.57    spl2_17),
% 0.22/0.57    inference(avatar_split_clause,[],[f54,f141])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.57  fof(f139,plain,(
% 0.22/0.57    spl2_16),
% 0.22/0.57    inference(avatar_split_clause,[],[f53,f137])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.57  fof(f135,plain,(
% 0.22/0.57    spl2_15 | ~spl2_8 | ~spl2_10),
% 0.22/0.57    inference(avatar_split_clause,[],[f129,f103,f95,f133])).
% 0.22/0.57  fof(f95,plain,(
% 0.22/0.57    spl2_8 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.57  fof(f103,plain,(
% 0.22/0.57    spl2_10 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.57  fof(f129,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1)) ) | (~spl2_8 | ~spl2_10)),
% 0.22/0.57    inference(resolution,[],[f104,f96])).
% 0.22/0.57  fof(f96,plain,(
% 0.22/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_8),
% 0.22/0.57    inference(avatar_component_clause,[],[f95])).
% 0.22/0.57  fof(f104,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_10),
% 0.22/0.57    inference(avatar_component_clause,[],[f103])).
% 0.22/0.57  fof(f117,plain,(
% 0.22/0.57    spl2_13),
% 0.22/0.57    inference(avatar_split_clause,[],[f56,f115])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 0.22/0.57  fof(f105,plain,(
% 0.22/0.57    spl2_10),
% 0.22/0.57    inference(avatar_split_clause,[],[f50,f103])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    spl2_9),
% 0.22/0.57    inference(avatar_split_clause,[],[f46,f99])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.22/0.57  fof(f97,plain,(
% 0.22/0.57    spl2_8),
% 0.22/0.57    inference(avatar_split_clause,[],[f60,f95])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.57    inference(nnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.57  fof(f81,plain,(
% 0.22/0.57    spl2_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f44,f79])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,axiom,(
% 0.22/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    spl2_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f43,f75])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    spl2_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f41,f71])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    ~spl2_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f40,f66])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.57    inference(cnf_transformation,[],[f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f22])).
% 0.22/0.57  fof(f22,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.57    inference(negated_conjecture,[],[f21])).
% 0.22/0.57  fof(f21,conjecture,(
% 0.22/0.57    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (12782)------------------------------
% 0.22/0.57  % (12782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (12782)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (12782)Memory used [KB]: 8699
% 0.22/0.57  % (12782)Time elapsed: 0.136 s
% 0.22/0.57  % (12782)------------------------------
% 0.22/0.57  % (12782)------------------------------
% 0.22/0.57  % (12775)Success in time 0.211 s
%------------------------------------------------------------------------------
