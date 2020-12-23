%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:33 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 466 expanded)
%              Number of leaves         :   54 ( 215 expanded)
%              Depth                    :   10
%              Number of atoms          :  635 (1237 expanded)
%              Number of equality atoms :  144 ( 305 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2097,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f89,f93,f97,f101,f109,f117,f123,f139,f144,f160,f164,f187,f249,f286,f332,f344,f445,f548,f587,f598,f621,f719,f949,f974,f986,f1044,f1073,f1114,f1159,f1227,f1428,f1437,f1779,f2053])).

fof(f2053,plain,
    ( ~ spl2_11
    | spl2_45
    | ~ spl2_69
    | ~ spl2_96
    | ~ spl2_107 ),
    inference(avatar_contradiction_clause,[],[f2052])).

fof(f2052,plain,
    ( $false
    | ~ spl2_11
    | spl2_45
    | ~ spl2_69
    | ~ spl2_96
    | ~ spl2_107 ),
    inference(subsumption_resolution,[],[f444,f2051])).

fof(f2051,plain,
    ( ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4)))
    | ~ spl2_11
    | ~ spl2_69
    | ~ spl2_96
    | ~ spl2_107 ),
    inference(forward_demodulation,[],[f2050,f973])).

fof(f973,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f972])).

fof(f972,plain,
    ( spl2_69
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f2050,plain,
    ( ! [X4,X3] : k6_relat_1(k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X4)
    | ~ spl2_11
    | ~ spl2_96
    | ~ spl2_107 ),
    inference(forward_demodulation,[],[f2049,f122])).

fof(f122,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl2_11
  <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f2049,plain,
    ( ! [X4,X3] : k6_relat_1(k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4),X4)
    | ~ spl2_11
    | ~ spl2_96
    | ~ spl2_107 ),
    inference(forward_demodulation,[],[f2048,f1778])).

fof(f1778,plain,
    ( ! [X59,X57,X58] : k7_relat_1(k7_relat_1(k6_relat_1(X57),X58),X59) = k7_relat_1(k6_relat_1(X57),k1_setfam_1(k4_enumset1(X58,X58,X58,X58,X58,X59)))
    | ~ spl2_107 ),
    inference(avatar_component_clause,[],[f1777])).

fof(f1777,plain,
    ( spl2_107
  <=> ! [X58,X57,X59] : k7_relat_1(k7_relat_1(k6_relat_1(X57),X58),X59) = k7_relat_1(k6_relat_1(X57),k1_setfam_1(k4_enumset1(X58,X58,X58,X58,X58,X59))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).

fof(f2048,plain,
    ( ! [X4,X3] : k6_relat_1(k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X3),k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4))),X4)
    | ~ spl2_11
    | ~ spl2_96
    | ~ spl2_107 ),
    inference(forward_demodulation,[],[f1967,f1436])).

fof(f1436,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3)
    | ~ spl2_96 ),
    inference(avatar_component_clause,[],[f1435])).

fof(f1435,plain,
    ( spl2_96
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).

fof(f1967,plain,
    ( ! [X4,X3] : k6_relat_1(k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4))),X3),X4)
    | ~ spl2_11
    | ~ spl2_107 ),
    inference(superposition,[],[f1778,f122])).

fof(f444,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_45 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl2_45
  <=> k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f1779,plain,
    ( spl2_107
    | ~ spl2_1
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f1531,f1225,f79,f1777])).

fof(f79,plain,
    ( spl2_1
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1225,plain,
    ( spl2_88
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f1531,plain,
    ( ! [X59,X57,X58] : k7_relat_1(k7_relat_1(k6_relat_1(X57),X58),X59) = k7_relat_1(k6_relat_1(X57),k1_setfam_1(k4_enumset1(X58,X58,X58,X58,X58,X59)))
    | ~ spl2_1
    | ~ spl2_88 ),
    inference(resolution,[],[f1226,f80])).

fof(f80,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f1226,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )
    | ~ spl2_88 ),
    inference(avatar_component_clause,[],[f1225])).

fof(f1437,plain,
    ( spl2_96
    | ~ spl2_77
    | ~ spl2_95 ),
    inference(avatar_split_clause,[],[f1432,f1426,f1112,f1435])).

fof(f1112,plain,
    ( spl2_77
  <=> ! [X49,X48] : k7_relat_1(k6_relat_1(X48),X49) = k4_relat_1(k7_relat_1(k6_relat_1(X49),X48)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f1426,plain,
    ( spl2_95
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X3),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).

fof(f1432,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3)
    | ~ spl2_77
    | ~ spl2_95 ),
    inference(superposition,[],[f1427,f1113])).

fof(f1113,plain,
    ( ! [X48,X49] : k7_relat_1(k6_relat_1(X48),X49) = k4_relat_1(k7_relat_1(k6_relat_1(X49),X48))
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f1112])).

fof(f1427,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2))
    | ~ spl2_95 ),
    inference(avatar_component_clause,[],[f1426])).

fof(f1428,plain,
    ( spl2_95
    | ~ spl2_70
    | ~ spl2_84 ),
    inference(avatar_split_clause,[],[f1420,f1157,f984,f1426])).

fof(f984,plain,
    ( spl2_70
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f1157,plain,
    ( spl2_84
  <=> ! [X46,X45,X47] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X46),X47),X45)) = k7_relat_1(k7_relat_1(k6_relat_1(X45),X47),X46) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).

fof(f1420,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2))
    | ~ spl2_70
    | ~ spl2_84 ),
    inference(superposition,[],[f1158,f985])).

fof(f985,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
    | ~ spl2_70 ),
    inference(avatar_component_clause,[],[f984])).

fof(f1158,plain,
    ( ! [X47,X45,X46] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X46),X47),X45)) = k7_relat_1(k7_relat_1(k6_relat_1(X45),X47),X46)
    | ~ spl2_84 ),
    inference(avatar_component_clause,[],[f1157])).

fof(f1227,plain,(
    spl2_88 ),
    inference(avatar_split_clause,[],[f77,f1225])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f68,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f1159,plain,
    ( spl2_84
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_20
    | ~ spl2_24
    | ~ spl2_27
    | ~ spl2_32
    | ~ spl2_65
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f1098,f1071,f717,f330,f284,f247,f185,f162,f158,f142,f95,f79,f1157])).

fof(f95,plain,
    ( spl2_5
  <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f142,plain,
    ( spl2_15
  <=> ! [X1,X0] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f158,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f162,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f185,plain,
    ( spl2_20
  <=> ! [X1,X0] : v1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f247,plain,
    ( spl2_24
  <=> ! [X1,X0] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f284,plain,
    ( spl2_27
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f330,plain,
    ( spl2_32
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f717,plain,
    ( spl2_65
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f1071,plain,
    ( spl2_76
  <=> ! [X49,X48] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X49),X48)) = k5_relat_1(k4_relat_1(X48),k6_relat_1(X49))
        | ~ v1_relat_1(X48) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f1098,plain,
    ( ! [X47,X45,X46] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X46),X47),X45)) = k7_relat_1(k7_relat_1(k6_relat_1(X45),X47),X46)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_20
    | ~ spl2_24
    | ~ spl2_27
    | ~ spl2_32
    | ~ spl2_65
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f1096,f806])).

fof(f806,plain,
    ( ! [X4,X2,X3] : k5_relat_1(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X4),X3)
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_27
    | ~ spl2_65 ),
    inference(backward_demodulation,[],[f223,f805])).

fof(f805,plain,
    ( ! [X109,X107,X108] : k8_relat_1(X107,k7_relat_1(k6_relat_1(X108),X109)) = k7_relat_1(k7_relat_1(k6_relat_1(X107),X108),X109)
    | ~ spl2_1
    | ~ spl2_27
    | ~ spl2_65 ),
    inference(forward_demodulation,[],[f758,f285])).

fof(f285,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f284])).

fof(f758,plain,
    ( ! [X109,X107,X108] : k7_relat_1(k8_relat_1(X107,k6_relat_1(X108)),X109) = k8_relat_1(X107,k7_relat_1(k6_relat_1(X108),X109))
    | ~ spl2_1
    | ~ spl2_65 ),
    inference(resolution,[],[f718,f80])).

fof(f718,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) )
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f717])).

fof(f223,plain,
    ( ! [X4,X2,X3] : k8_relat_1(X2,k7_relat_1(k6_relat_1(X4),X3)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X2))
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(backward_demodulation,[],[f182,f217])).

fof(f217,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1))
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(backward_demodulation,[],[f169,f214])).

fof(f214,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_18 ),
    inference(resolution,[],[f163,f80])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f162])).

fof(f169,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))
    | ~ spl2_1
    | ~ spl2_17 ),
    inference(resolution,[],[f159,f80])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f158])).

fof(f182,plain,
    ( ! [X4,X2,X3] : k8_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k5_relat_1(k8_relat_1(X4,k6_relat_1(X3)),k6_relat_1(X2))
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f170,f169])).

fof(f170,plain,
    ( ! [X4,X2,X3] : k8_relat_1(X2,k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))) = k5_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)),k6_relat_1(X2))
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(resolution,[],[f159,f143])).

fof(f143,plain,
    ( ! [X0,X1] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f1096,plain,
    ( ! [X47,X45,X46] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X46),X47),X45)) = k5_relat_1(k7_relat_1(k6_relat_1(X47),X46),k6_relat_1(X45))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_20
    | ~ spl2_24
    | ~ spl2_32
    | ~ spl2_76 ),
    inference(backward_demodulation,[],[f1092,f1095])).

fof(f1095,plain,
    ( ! [X48,X49] : k7_relat_1(k6_relat_1(X48),X49) = k4_relat_1(k7_relat_1(k6_relat_1(X49),X48))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_32
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f1094,f331])).

fof(f331,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f330])).

fof(f1094,plain,
    ( ! [X48,X49] : k4_relat_1(k5_relat_1(k6_relat_1(X48),k6_relat_1(X49))) = k7_relat_1(k6_relat_1(X48),X49)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_32
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f1093,f331])).

fof(f1093,plain,
    ( ! [X48,X49] : k4_relat_1(k5_relat_1(k6_relat_1(X48),k6_relat_1(X49))) = k5_relat_1(k6_relat_1(X49),k6_relat_1(X48))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f1083,f96])).

fof(f96,plain,
    ( ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f1083,plain,
    ( ! [X48,X49] : k4_relat_1(k5_relat_1(k6_relat_1(X48),k6_relat_1(X49))) = k5_relat_1(k4_relat_1(k6_relat_1(X49)),k6_relat_1(X48))
    | ~ spl2_1
    | ~ spl2_76 ),
    inference(resolution,[],[f1072,f80])).

fof(f1072,plain,
    ( ! [X48,X49] :
        ( ~ v1_relat_1(X48)
        | k4_relat_1(k5_relat_1(k6_relat_1(X49),X48)) = k5_relat_1(k4_relat_1(X48),k6_relat_1(X49)) )
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f1071])).

fof(f1092,plain,
    ( ! [X47,X45,X46] : k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X46),X47)),k6_relat_1(X45)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X46),X47),X45))
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_20
    | ~ spl2_24
    | ~ spl2_76 ),
    inference(forward_demodulation,[],[f1082,f235])).

fof(f235,plain,
    ( ! [X4,X2,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k5_relat_1(k6_relat_1(X4),k7_relat_1(k6_relat_1(X2),X3))
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f215,f217])).

fof(f215,plain,
    ( ! [X4,X2,X3] : k7_relat_1(k8_relat_1(X2,k6_relat_1(X3)),X4) = k5_relat_1(k6_relat_1(X4),k8_relat_1(X2,k6_relat_1(X3)))
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(resolution,[],[f163,f186])).

fof(f186,plain,
    ( ! [X0,X1] : v1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f185])).

fof(f1082,plain,
    ( ! [X47,X45,X46] : k4_relat_1(k5_relat_1(k6_relat_1(X45),k7_relat_1(k6_relat_1(X46),X47))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X46),X47)),k6_relat_1(X45))
    | ~ spl2_24
    | ~ spl2_76 ),
    inference(resolution,[],[f1072,f248])).

fof(f248,plain,
    ( ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f247])).

fof(f1114,plain,
    ( spl2_77
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_32
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f1095,f1071,f330,f95,f79,f1112])).

fof(f1073,plain,
    ( spl2_76
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_74 ),
    inference(avatar_split_clause,[],[f1059,f1042,f95,f79,f1071])).

fof(f1042,plain,
    ( spl2_74
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f1059,plain,
    ( ! [X48,X49] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X49),X48)) = k5_relat_1(k4_relat_1(X48),k6_relat_1(X49))
        | ~ v1_relat_1(X48) )
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_74 ),
    inference(forward_demodulation,[],[f1058,f96])).

fof(f1058,plain,
    ( ! [X48,X49] :
        ( ~ v1_relat_1(X48)
        | k4_relat_1(k5_relat_1(k6_relat_1(X49),X48)) = k5_relat_1(k4_relat_1(X48),k4_relat_1(k6_relat_1(X49))) )
    | ~ spl2_1
    | ~ spl2_74 ),
    inference(resolution,[],[f1043,f80])).

fof(f1043,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl2_74 ),
    inference(avatar_component_clause,[],[f1042])).

fof(f1044,plain,(
    spl2_74 ),
    inference(avatar_split_clause,[],[f53,f1042])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f986,plain,
    ( spl2_70
    | ~ spl2_59
    | ~ spl2_68 ),
    inference(avatar_split_clause,[],[f966,f947,f619,f984])).

fof(f619,plain,
    ( spl2_59
  <=> ! [X1,X2] : k7_relat_1(k6_relat_1(X2),X1) = k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f947,plain,
    ( spl2_68
  <=> ! [X108,X107,X109] : k8_relat_1(X107,k7_relat_1(k6_relat_1(X108),X109)) = k7_relat_1(k7_relat_1(k6_relat_1(X107),X108),X109) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f966,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
    | ~ spl2_59
    | ~ spl2_68 ),
    inference(superposition,[],[f948,f620])).

fof(f620,plain,
    ( ! [X2,X1] : k7_relat_1(k6_relat_1(X2),X1) = k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X1))
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f619])).

fof(f948,plain,
    ( ! [X109,X107,X108] : k8_relat_1(X107,k7_relat_1(k6_relat_1(X108),X109)) = k7_relat_1(k7_relat_1(k6_relat_1(X107),X108),X109)
    | ~ spl2_68 ),
    inference(avatar_component_clause,[],[f947])).

fof(f974,plain,
    ( spl2_69
    | ~ spl2_11
    | ~ spl2_27
    | ~ spl2_68 ),
    inference(avatar_split_clause,[],[f970,f947,f284,f121,f972])).

fof(f970,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)
    | ~ spl2_11
    | ~ spl2_27
    | ~ spl2_68 ),
    inference(forward_demodulation,[],[f965,f285])).

fof(f965,plain,
    ( ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)
    | ~ spl2_11
    | ~ spl2_68 ),
    inference(superposition,[],[f948,f122])).

fof(f949,plain,
    ( spl2_68
    | ~ spl2_1
    | ~ spl2_27
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f805,f717,f284,f79,f947])).

fof(f719,plain,(
    spl2_65 ),
    inference(avatar_split_clause,[],[f67,f717])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(f621,plain,
    ( spl2_59
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_24
    | ~ spl2_32
    | ~ spl2_58 ),
    inference(avatar_split_clause,[],[f613,f596,f330,f247,f107,f79,f619])).

fof(f107,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f596,plain,
    ( spl2_58
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k6_relat_1(X1))
        | ~ v1_relat_1(X0)
        | k8_relat_1(X1,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f613,plain,
    ( ! [X2,X1] : k7_relat_1(k6_relat_1(X2),X1) = k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X1))
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_24
    | ~ spl2_32
    | ~ spl2_58 ),
    inference(forward_demodulation,[],[f612,f331])).

fof(f612,plain,
    ( ! [X2,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k8_relat_1(X1,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_24
    | ~ spl2_32
    | ~ spl2_58 ),
    inference(subsumption_resolution,[],[f611,f248])).

fof(f611,plain,
    ( ! [X2,X1] :
        ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
        | k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k8_relat_1(X1,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) )
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_32
    | ~ spl2_58 ),
    inference(forward_demodulation,[],[f610,f331])).

fof(f610,plain,
    ( ! [X2,X1] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
        | k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k8_relat_1(X1,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) )
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_58 ),
    inference(subsumption_resolution,[],[f600,f80])).

fof(f600,plain,
    ( ! [X2,X1] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
        | k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k8_relat_1(X1,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_8
    | ~ spl2_58 ),
    inference(resolution,[],[f597,f108])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f597,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k6_relat_1(X1))
        | ~ v1_relat_1(X0)
        | k8_relat_1(X1,X0) = X0 )
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f596])).

fof(f598,plain,
    ( spl2_58
    | ~ spl2_34
    | ~ spl2_57 ),
    inference(avatar_split_clause,[],[f594,f585,f342,f596])).

fof(f342,plain,
    ( spl2_34
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f585,plain,
    ( spl2_57
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ r1_tarski(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f594,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k6_relat_1(X1))
        | ~ v1_relat_1(X0)
        | k8_relat_1(X1,X0) = X0 )
    | ~ spl2_34
    | ~ spl2_57 ),
    inference(duplicate_literal_removal,[],[f591])).

fof(f591,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k6_relat_1(X1))
        | ~ v1_relat_1(X0)
        | k8_relat_1(X1,X0) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_34
    | ~ spl2_57 ),
    inference(resolution,[],[f586,f343])).

fof(f343,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f342])).

fof(f586,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ r1_tarski(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) )
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f585])).

fof(f587,plain,
    ( spl2_57
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_52 ),
    inference(avatar_split_clause,[],[f574,f546,f91,f79,f585])).

fof(f91,plain,
    ( spl2_4
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f546,plain,
    ( spl2_52
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f574,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ r1_tarski(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) )
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_52 ),
    inference(subsumption_resolution,[],[f571,f80])).

fof(f571,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ r1_tarski(X1,k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(X1) )
    | ~ spl2_4
    | ~ spl2_52 ),
    inference(superposition,[],[f547,f92])).

fof(f92,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f547,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f546])).

fof(f548,plain,(
    spl2_52 ),
    inference(avatar_split_clause,[],[f55,f546])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f445,plain,
    ( ~ spl2_45
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f232,f162,f158,f79,f442])).

fof(f232,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(backward_demodulation,[],[f172,f217])).

fof(f172,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f76,f169])).

fof(f76,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f46,f75])).

fof(f46,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f44])).

fof(f44,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f344,plain,(
    spl2_34 ),
    inference(avatar_split_clause,[],[f63,f342])).

fof(f63,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f332,plain,
    ( spl2_32
    | ~ spl2_1
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f214,f162,f79,f330])).

fof(f286,plain,
    ( spl2_27
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f217,f162,f158,f79,f284])).

fof(f249,plain,
    ( spl2_24
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f225,f185,f162,f158,f79,f247])).

fof(f225,plain,
    ( ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(backward_demodulation,[],[f186,f217])).

fof(f187,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f173,f158,f142,f79,f185])).

fof(f173,plain,
    ( ! [X0,X1] : v1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f143,f169])).

fof(f164,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f60,f162])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f160,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f59,f158])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f144,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f140,f137,f79,f142])).

fof(f137,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k5_relat_1(k6_relat_1(X1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f140,plain,
    ( ! [X0,X1] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))
    | ~ spl2_1
    | ~ spl2_14 ),
    inference(resolution,[],[f138,f80])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k5_relat_1(k6_relat_1(X1),X0)) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f135,f115,f79,f137])).

fof(f115,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k5_relat_1(k6_relat_1(X1),X0)) )
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(resolution,[],[f116,f80])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | v1_relat_1(k5_relat_1(X0,X1)) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f123,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f119,f99,f87,f79,f121])).

fof(f87,plain,
    ( spl2_3
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f99,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f119,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f118,f88])).

fof(f88,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f118,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(resolution,[],[f100,f80])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,k1_relat_1(X0)) = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f117,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f64,f115])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f109,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f61,f107])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f101,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f52,f99])).

fof(f52,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    spl2_5 ),
    inference(avatar_split_clause,[],[f47,f95])).

fof(f47,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f93,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f51,f91])).

fof(f51,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f89,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f50,f87])).

fof(f50,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f48,f79])).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:06:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (19189)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.46  % (19193)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (19202)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (19194)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (19200)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (19199)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (19199)Refutation not found, incomplete strategy% (19199)------------------------------
% 0.22/0.49  % (19199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (19199)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (19199)Memory used [KB]: 10618
% 0.22/0.49  % (19199)Time elapsed: 0.073 s
% 0.22/0.49  % (19199)------------------------------
% 0.22/0.49  % (19199)------------------------------
% 0.22/0.49  % (19204)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (19197)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (19187)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (19192)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (19190)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (19201)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (19196)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (19191)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (19205)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (19203)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (19195)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.53  % (19188)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.75/0.59  % (19194)Refutation found. Thanks to Tanya!
% 1.75/0.59  % SZS status Theorem for theBenchmark
% 1.75/0.59  % SZS output start Proof for theBenchmark
% 1.75/0.59  fof(f2097,plain,(
% 1.75/0.59    $false),
% 1.75/0.59    inference(avatar_sat_refutation,[],[f81,f89,f93,f97,f101,f109,f117,f123,f139,f144,f160,f164,f187,f249,f286,f332,f344,f445,f548,f587,f598,f621,f719,f949,f974,f986,f1044,f1073,f1114,f1159,f1227,f1428,f1437,f1779,f2053])).
% 1.75/0.59  fof(f2053,plain,(
% 1.75/0.59    ~spl2_11 | spl2_45 | ~spl2_69 | ~spl2_96 | ~spl2_107),
% 1.75/0.59    inference(avatar_contradiction_clause,[],[f2052])).
% 1.75/0.59  fof(f2052,plain,(
% 1.75/0.59    $false | (~spl2_11 | spl2_45 | ~spl2_69 | ~spl2_96 | ~spl2_107)),
% 1.75/0.59    inference(subsumption_resolution,[],[f444,f2051])).
% 1.75/0.59  fof(f2051,plain,(
% 1.75/0.59    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4)))) ) | (~spl2_11 | ~spl2_69 | ~spl2_96 | ~spl2_107)),
% 1.75/0.59    inference(forward_demodulation,[],[f2050,f973])).
% 1.75/0.59  fof(f973,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) ) | ~spl2_69),
% 1.75/0.59    inference(avatar_component_clause,[],[f972])).
% 1.75/0.59  fof(f972,plain,(
% 1.75/0.59    spl2_69 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 1.75/0.59  fof(f2050,plain,(
% 1.75/0.59    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X4)) ) | (~spl2_11 | ~spl2_96 | ~spl2_107)),
% 1.75/0.59    inference(forward_demodulation,[],[f2049,f122])).
% 1.75/0.59  fof(f122,plain,(
% 1.75/0.59    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | ~spl2_11),
% 1.75/0.59    inference(avatar_component_clause,[],[f121])).
% 1.75/0.59  fof(f121,plain,(
% 1.75/0.59    spl2_11 <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.75/0.59  fof(f2049,plain,(
% 1.75/0.59    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4),X4)) ) | (~spl2_11 | ~spl2_96 | ~spl2_107)),
% 1.75/0.59    inference(forward_demodulation,[],[f2048,f1778])).
% 1.75/0.59  fof(f1778,plain,(
% 1.75/0.59    ( ! [X59,X57,X58] : (k7_relat_1(k7_relat_1(k6_relat_1(X57),X58),X59) = k7_relat_1(k6_relat_1(X57),k1_setfam_1(k4_enumset1(X58,X58,X58,X58,X58,X59)))) ) | ~spl2_107),
% 1.75/0.59    inference(avatar_component_clause,[],[f1777])).
% 1.75/0.59  fof(f1777,plain,(
% 1.75/0.59    spl2_107 <=> ! [X58,X57,X59] : k7_relat_1(k7_relat_1(k6_relat_1(X57),X58),X59) = k7_relat_1(k6_relat_1(X57),k1_setfam_1(k4_enumset1(X58,X58,X58,X58,X58,X59)))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).
% 1.75/0.59  fof(f2048,plain,(
% 1.75/0.59    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X3),k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4))),X4)) ) | (~spl2_11 | ~spl2_96 | ~spl2_107)),
% 1.75/0.59    inference(forward_demodulation,[],[f1967,f1436])).
% 1.75/0.59  fof(f1436,plain,(
% 1.75/0.59    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3)) ) | ~spl2_96),
% 1.75/0.59    inference(avatar_component_clause,[],[f1435])).
% 1.75/0.59  fof(f1435,plain,(
% 1.75/0.59    spl2_96 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).
% 1.75/0.59  fof(f1967,plain,(
% 1.75/0.59    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X3,X3,X3,X3,X3,X4))),X3),X4)) ) | (~spl2_11 | ~spl2_107)),
% 1.75/0.59    inference(superposition,[],[f1778,f122])).
% 1.75/0.59  fof(f444,plain,(
% 1.75/0.59    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_45),
% 1.75/0.59    inference(avatar_component_clause,[],[f442])).
% 1.75/0.59  fof(f442,plain,(
% 1.75/0.59    spl2_45 <=> k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 1.75/0.59  fof(f1779,plain,(
% 1.75/0.59    spl2_107 | ~spl2_1 | ~spl2_88),
% 1.75/0.59    inference(avatar_split_clause,[],[f1531,f1225,f79,f1777])).
% 1.75/0.59  fof(f79,plain,(
% 1.75/0.59    spl2_1 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.75/0.59  fof(f1225,plain,(
% 1.75/0.59    spl2_88 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X2))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 1.75/0.59  fof(f1531,plain,(
% 1.75/0.59    ( ! [X59,X57,X58] : (k7_relat_1(k7_relat_1(k6_relat_1(X57),X58),X59) = k7_relat_1(k6_relat_1(X57),k1_setfam_1(k4_enumset1(X58,X58,X58,X58,X58,X59)))) ) | (~spl2_1 | ~spl2_88)),
% 1.75/0.59    inference(resolution,[],[f1226,f80])).
% 1.75/0.59  fof(f80,plain,(
% 1.75/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_1),
% 1.75/0.59    inference(avatar_component_clause,[],[f79])).
% 1.75/0.59  fof(f1226,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))) ) | ~spl2_88),
% 1.75/0.59    inference(avatar_component_clause,[],[f1225])).
% 1.75/0.59  fof(f1437,plain,(
% 1.75/0.59    spl2_96 | ~spl2_77 | ~spl2_95),
% 1.75/0.59    inference(avatar_split_clause,[],[f1432,f1426,f1112,f1435])).
% 1.75/0.59  fof(f1112,plain,(
% 1.75/0.59    spl2_77 <=> ! [X49,X48] : k7_relat_1(k6_relat_1(X48),X49) = k4_relat_1(k7_relat_1(k6_relat_1(X49),X48))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 1.75/0.59  fof(f1426,plain,(
% 1.75/0.59    spl2_95 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X3),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).
% 1.75/0.59  fof(f1432,plain,(
% 1.75/0.59    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3)) ) | (~spl2_77 | ~spl2_95)),
% 1.75/0.59    inference(superposition,[],[f1427,f1113])).
% 1.75/0.59  fof(f1113,plain,(
% 1.75/0.59    ( ! [X48,X49] : (k7_relat_1(k6_relat_1(X48),X49) = k4_relat_1(k7_relat_1(k6_relat_1(X49),X48))) ) | ~spl2_77),
% 1.75/0.59    inference(avatar_component_clause,[],[f1112])).
% 1.75/0.59  fof(f1427,plain,(
% 1.75/0.59    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2))) ) | ~spl2_95),
% 1.75/0.59    inference(avatar_component_clause,[],[f1426])).
% 1.75/0.59  fof(f1428,plain,(
% 1.75/0.59    spl2_95 | ~spl2_70 | ~spl2_84),
% 1.75/0.59    inference(avatar_split_clause,[],[f1420,f1157,f984,f1426])).
% 1.75/0.59  fof(f984,plain,(
% 1.75/0.59    spl2_70 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 1.75/0.59  fof(f1157,plain,(
% 1.75/0.59    spl2_84 <=> ! [X46,X45,X47] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X46),X47),X45)) = k7_relat_1(k7_relat_1(k6_relat_1(X45),X47),X46)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).
% 1.75/0.59  fof(f1420,plain,(
% 1.75/0.59    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2))) ) | (~spl2_70 | ~spl2_84)),
% 1.75/0.59    inference(superposition,[],[f1158,f985])).
% 1.75/0.59  fof(f985,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) ) | ~spl2_70),
% 1.75/0.59    inference(avatar_component_clause,[],[f984])).
% 1.75/0.59  fof(f1158,plain,(
% 1.75/0.59    ( ! [X47,X45,X46] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X46),X47),X45)) = k7_relat_1(k7_relat_1(k6_relat_1(X45),X47),X46)) ) | ~spl2_84),
% 1.75/0.59    inference(avatar_component_clause,[],[f1157])).
% 1.75/0.59  fof(f1227,plain,(
% 1.75/0.59    spl2_88),
% 1.75/0.59    inference(avatar_split_clause,[],[f77,f1225])).
% 1.75/0.59  fof(f77,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 1.75/0.59    inference(definition_unfolding,[],[f68,f75])).
% 1.75/0.59  fof(f75,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.75/0.59    inference(definition_unfolding,[],[f56,f74])).
% 1.75/0.59  fof(f74,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.75/0.59    inference(definition_unfolding,[],[f57,f73])).
% 1.75/0.59  fof(f73,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.75/0.59    inference(definition_unfolding,[],[f66,f72])).
% 1.75/0.59  fof(f72,plain,(
% 1.75/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.75/0.59    inference(definition_unfolding,[],[f70,f71])).
% 1.75/0.59  fof(f71,plain,(
% 1.75/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f4])).
% 1.75/0.59  fof(f4,axiom,(
% 1.75/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.75/0.59  fof(f70,plain,(
% 1.75/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f3])).
% 1.75/0.59  fof(f3,axiom,(
% 1.75/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.75/0.59  fof(f66,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f2])).
% 1.75/0.59  fof(f2,axiom,(
% 1.75/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.75/0.59  fof(f57,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f1])).
% 1.75/0.59  fof(f1,axiom,(
% 1.75/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.75/0.59  fof(f56,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f5])).
% 1.75/0.59  fof(f5,axiom,(
% 1.75/0.59    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.75/0.59  fof(f68,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f41])).
% 1.75/0.59  fof(f41,plain,(
% 1.75/0.59    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.75/0.59    inference(ennf_transformation,[],[f7])).
% 1.75/0.59  fof(f7,axiom,(
% 1.75/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 1.75/0.59  fof(f1159,plain,(
% 1.75/0.59    spl2_84 | ~spl2_1 | ~spl2_5 | ~spl2_15 | ~spl2_17 | ~spl2_18 | ~spl2_20 | ~spl2_24 | ~spl2_27 | ~spl2_32 | ~spl2_65 | ~spl2_76),
% 1.75/0.59    inference(avatar_split_clause,[],[f1098,f1071,f717,f330,f284,f247,f185,f162,f158,f142,f95,f79,f1157])).
% 1.75/0.59  fof(f95,plain,(
% 1.75/0.59    spl2_5 <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.75/0.59  fof(f142,plain,(
% 1.75/0.59    spl2_15 <=> ! [X1,X0] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.75/0.59  fof(f158,plain,(
% 1.75/0.59    spl2_17 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.75/0.59  fof(f162,plain,(
% 1.75/0.59    spl2_18 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.75/0.59  fof(f185,plain,(
% 1.75/0.59    spl2_20 <=> ! [X1,X0] : v1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 1.75/0.59  fof(f247,plain,(
% 1.75/0.59    spl2_24 <=> ! [X1,X0] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.75/0.59  fof(f284,plain,(
% 1.75/0.59    spl2_27 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 1.75/0.59  fof(f330,plain,(
% 1.75/0.59    spl2_32 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 1.75/0.59  fof(f717,plain,(
% 1.75/0.59    spl2_65 <=> ! [X1,X0,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 1.75/0.59  fof(f1071,plain,(
% 1.75/0.59    spl2_76 <=> ! [X49,X48] : (k4_relat_1(k5_relat_1(k6_relat_1(X49),X48)) = k5_relat_1(k4_relat_1(X48),k6_relat_1(X49)) | ~v1_relat_1(X48))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 1.75/0.59  fof(f1098,plain,(
% 1.75/0.59    ( ! [X47,X45,X46] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X46),X47),X45)) = k7_relat_1(k7_relat_1(k6_relat_1(X45),X47),X46)) ) | (~spl2_1 | ~spl2_5 | ~spl2_15 | ~spl2_17 | ~spl2_18 | ~spl2_20 | ~spl2_24 | ~spl2_27 | ~spl2_32 | ~spl2_65 | ~spl2_76)),
% 1.75/0.59    inference(forward_demodulation,[],[f1096,f806])).
% 1.75/0.59  fof(f806,plain,(
% 1.75/0.59    ( ! [X4,X2,X3] : (k5_relat_1(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X4),X3)) ) | (~spl2_1 | ~spl2_15 | ~spl2_17 | ~spl2_18 | ~spl2_27 | ~spl2_65)),
% 1.75/0.59    inference(backward_demodulation,[],[f223,f805])).
% 1.75/0.59  fof(f805,plain,(
% 1.75/0.59    ( ! [X109,X107,X108] : (k8_relat_1(X107,k7_relat_1(k6_relat_1(X108),X109)) = k7_relat_1(k7_relat_1(k6_relat_1(X107),X108),X109)) ) | (~spl2_1 | ~spl2_27 | ~spl2_65)),
% 1.75/0.59    inference(forward_demodulation,[],[f758,f285])).
% 1.75/0.59  fof(f285,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1))) ) | ~spl2_27),
% 1.75/0.59    inference(avatar_component_clause,[],[f284])).
% 1.75/0.59  fof(f758,plain,(
% 1.75/0.59    ( ! [X109,X107,X108] : (k7_relat_1(k8_relat_1(X107,k6_relat_1(X108)),X109) = k8_relat_1(X107,k7_relat_1(k6_relat_1(X108),X109))) ) | (~spl2_1 | ~spl2_65)),
% 1.75/0.59    inference(resolution,[],[f718,f80])).
% 1.75/0.59  fof(f718,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))) ) | ~spl2_65),
% 1.75/0.59    inference(avatar_component_clause,[],[f717])).
% 1.75/0.59  fof(f223,plain,(
% 1.75/0.59    ( ! [X4,X2,X3] : (k8_relat_1(X2,k7_relat_1(k6_relat_1(X4),X3)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X2))) ) | (~spl2_1 | ~spl2_15 | ~spl2_17 | ~spl2_18)),
% 1.75/0.59    inference(backward_demodulation,[],[f182,f217])).
% 1.75/0.59  fof(f217,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_17 | ~spl2_18)),
% 1.75/0.59    inference(backward_demodulation,[],[f169,f214])).
% 1.75/0.59  fof(f214,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_18)),
% 1.75/0.59    inference(resolution,[],[f163,f80])).
% 1.75/0.59  fof(f163,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_18),
% 1.75/0.59    inference(avatar_component_clause,[],[f162])).
% 1.75/0.59  fof(f169,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_17)),
% 1.75/0.59    inference(resolution,[],[f159,f80])).
% 1.75/0.59  fof(f159,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_17),
% 1.75/0.59    inference(avatar_component_clause,[],[f158])).
% 1.75/0.59  fof(f182,plain,(
% 1.75/0.59    ( ! [X4,X2,X3] : (k8_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k5_relat_1(k8_relat_1(X4,k6_relat_1(X3)),k6_relat_1(X2))) ) | (~spl2_1 | ~spl2_15 | ~spl2_17)),
% 1.75/0.59    inference(forward_demodulation,[],[f170,f169])).
% 1.75/0.59  fof(f170,plain,(
% 1.75/0.59    ( ! [X4,X2,X3] : (k8_relat_1(X2,k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))) = k5_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)),k6_relat_1(X2))) ) | (~spl2_15 | ~spl2_17)),
% 1.75/0.59    inference(resolution,[],[f159,f143])).
% 1.75/0.59  fof(f143,plain,(
% 1.75/0.59    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ) | ~spl2_15),
% 1.75/0.59    inference(avatar_component_clause,[],[f142])).
% 1.75/0.59  fof(f1096,plain,(
% 1.75/0.59    ( ! [X47,X45,X46] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X46),X47),X45)) = k5_relat_1(k7_relat_1(k6_relat_1(X47),X46),k6_relat_1(X45))) ) | (~spl2_1 | ~spl2_5 | ~spl2_17 | ~spl2_18 | ~spl2_20 | ~spl2_24 | ~spl2_32 | ~spl2_76)),
% 1.75/0.59    inference(backward_demodulation,[],[f1092,f1095])).
% 1.75/0.59  fof(f1095,plain,(
% 1.75/0.59    ( ! [X48,X49] : (k7_relat_1(k6_relat_1(X48),X49) = k4_relat_1(k7_relat_1(k6_relat_1(X49),X48))) ) | (~spl2_1 | ~spl2_5 | ~spl2_32 | ~spl2_76)),
% 1.75/0.59    inference(forward_demodulation,[],[f1094,f331])).
% 1.75/0.59  fof(f331,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_32),
% 1.75/0.59    inference(avatar_component_clause,[],[f330])).
% 1.75/0.59  fof(f1094,plain,(
% 1.75/0.59    ( ! [X48,X49] : (k4_relat_1(k5_relat_1(k6_relat_1(X48),k6_relat_1(X49))) = k7_relat_1(k6_relat_1(X48),X49)) ) | (~spl2_1 | ~spl2_5 | ~spl2_32 | ~spl2_76)),
% 1.75/0.59    inference(forward_demodulation,[],[f1093,f331])).
% 1.75/0.59  fof(f1093,plain,(
% 1.75/0.59    ( ! [X48,X49] : (k4_relat_1(k5_relat_1(k6_relat_1(X48),k6_relat_1(X49))) = k5_relat_1(k6_relat_1(X49),k6_relat_1(X48))) ) | (~spl2_1 | ~spl2_5 | ~spl2_76)),
% 1.75/0.59    inference(forward_demodulation,[],[f1083,f96])).
% 1.75/0.59  fof(f96,plain,(
% 1.75/0.59    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) ) | ~spl2_5),
% 1.75/0.59    inference(avatar_component_clause,[],[f95])).
% 1.75/0.59  fof(f1083,plain,(
% 1.75/0.59    ( ! [X48,X49] : (k4_relat_1(k5_relat_1(k6_relat_1(X48),k6_relat_1(X49))) = k5_relat_1(k4_relat_1(k6_relat_1(X49)),k6_relat_1(X48))) ) | (~spl2_1 | ~spl2_76)),
% 1.75/0.59    inference(resolution,[],[f1072,f80])).
% 1.75/0.59  fof(f1072,plain,(
% 1.75/0.59    ( ! [X48,X49] : (~v1_relat_1(X48) | k4_relat_1(k5_relat_1(k6_relat_1(X49),X48)) = k5_relat_1(k4_relat_1(X48),k6_relat_1(X49))) ) | ~spl2_76),
% 1.75/0.59    inference(avatar_component_clause,[],[f1071])).
% 1.75/0.59  fof(f1092,plain,(
% 1.75/0.59    ( ! [X47,X45,X46] : (k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X46),X47)),k6_relat_1(X45)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X46),X47),X45))) ) | (~spl2_1 | ~spl2_17 | ~spl2_18 | ~spl2_20 | ~spl2_24 | ~spl2_76)),
% 1.75/0.59    inference(forward_demodulation,[],[f1082,f235])).
% 1.75/0.59  fof(f235,plain,(
% 1.75/0.59    ( ! [X4,X2,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k5_relat_1(k6_relat_1(X4),k7_relat_1(k6_relat_1(X2),X3))) ) | (~spl2_1 | ~spl2_17 | ~spl2_18 | ~spl2_20)),
% 1.75/0.59    inference(forward_demodulation,[],[f215,f217])).
% 1.75/0.59  fof(f215,plain,(
% 1.75/0.59    ( ! [X4,X2,X3] : (k7_relat_1(k8_relat_1(X2,k6_relat_1(X3)),X4) = k5_relat_1(k6_relat_1(X4),k8_relat_1(X2,k6_relat_1(X3)))) ) | (~spl2_18 | ~spl2_20)),
% 1.75/0.59    inference(resolution,[],[f163,f186])).
% 1.75/0.59  fof(f186,plain,(
% 1.75/0.59    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ) | ~spl2_20),
% 1.75/0.59    inference(avatar_component_clause,[],[f185])).
% 1.75/0.59  fof(f1082,plain,(
% 1.75/0.59    ( ! [X47,X45,X46] : (k4_relat_1(k5_relat_1(k6_relat_1(X45),k7_relat_1(k6_relat_1(X46),X47))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X46),X47)),k6_relat_1(X45))) ) | (~spl2_24 | ~spl2_76)),
% 1.75/0.59    inference(resolution,[],[f1072,f248])).
% 1.75/0.59  fof(f248,plain,(
% 1.75/0.59    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | ~spl2_24),
% 1.75/0.59    inference(avatar_component_clause,[],[f247])).
% 1.75/0.59  fof(f1114,plain,(
% 1.75/0.59    spl2_77 | ~spl2_1 | ~spl2_5 | ~spl2_32 | ~spl2_76),
% 1.75/0.59    inference(avatar_split_clause,[],[f1095,f1071,f330,f95,f79,f1112])).
% 1.75/0.59  fof(f1073,plain,(
% 1.75/0.59    spl2_76 | ~spl2_1 | ~spl2_5 | ~spl2_74),
% 1.75/0.59    inference(avatar_split_clause,[],[f1059,f1042,f95,f79,f1071])).
% 1.75/0.59  fof(f1042,plain,(
% 1.75/0.59    spl2_74 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 1.75/0.59  fof(f1059,plain,(
% 1.75/0.59    ( ! [X48,X49] : (k4_relat_1(k5_relat_1(k6_relat_1(X49),X48)) = k5_relat_1(k4_relat_1(X48),k6_relat_1(X49)) | ~v1_relat_1(X48)) ) | (~spl2_1 | ~spl2_5 | ~spl2_74)),
% 1.75/0.59    inference(forward_demodulation,[],[f1058,f96])).
% 1.75/0.59  fof(f1058,plain,(
% 1.75/0.59    ( ! [X48,X49] : (~v1_relat_1(X48) | k4_relat_1(k5_relat_1(k6_relat_1(X49),X48)) = k5_relat_1(k4_relat_1(X48),k4_relat_1(k6_relat_1(X49)))) ) | (~spl2_1 | ~spl2_74)),
% 1.75/0.59    inference(resolution,[],[f1043,f80])).
% 1.75/0.59  fof(f1043,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) ) | ~spl2_74),
% 1.75/0.59    inference(avatar_component_clause,[],[f1042])).
% 1.75/0.59  fof(f1044,plain,(
% 1.75/0.59    spl2_74),
% 1.75/0.59    inference(avatar_split_clause,[],[f53,f1042])).
% 1.75/0.59  fof(f53,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f27])).
% 1.75/0.59  fof(f27,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.75/0.59    inference(ennf_transformation,[],[f14])).
% 1.75/0.59  fof(f14,axiom,(
% 1.75/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 1.75/0.59  fof(f986,plain,(
% 1.75/0.59    spl2_70 | ~spl2_59 | ~spl2_68),
% 1.75/0.59    inference(avatar_split_clause,[],[f966,f947,f619,f984])).
% 1.75/0.59  fof(f619,plain,(
% 1.75/0.59    spl2_59 <=> ! [X1,X2] : k7_relat_1(k6_relat_1(X2),X1) = k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X1))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 1.75/0.59  fof(f947,plain,(
% 1.75/0.59    spl2_68 <=> ! [X108,X107,X109] : k8_relat_1(X107,k7_relat_1(k6_relat_1(X108),X109)) = k7_relat_1(k7_relat_1(k6_relat_1(X107),X108),X109)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).
% 1.75/0.59  fof(f966,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) ) | (~spl2_59 | ~spl2_68)),
% 1.75/0.59    inference(superposition,[],[f948,f620])).
% 1.75/0.59  fof(f620,plain,(
% 1.75/0.59    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X2),X1) = k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X1))) ) | ~spl2_59),
% 1.75/0.59    inference(avatar_component_clause,[],[f619])).
% 1.75/0.59  fof(f948,plain,(
% 1.75/0.59    ( ! [X109,X107,X108] : (k8_relat_1(X107,k7_relat_1(k6_relat_1(X108),X109)) = k7_relat_1(k7_relat_1(k6_relat_1(X107),X108),X109)) ) | ~spl2_68),
% 1.75/0.59    inference(avatar_component_clause,[],[f947])).
% 1.75/0.59  fof(f974,plain,(
% 1.75/0.59    spl2_69 | ~spl2_11 | ~spl2_27 | ~spl2_68),
% 1.75/0.59    inference(avatar_split_clause,[],[f970,f947,f284,f121,f972])).
% 1.75/0.59  fof(f970,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) ) | (~spl2_11 | ~spl2_27 | ~spl2_68)),
% 1.75/0.59    inference(forward_demodulation,[],[f965,f285])).
% 1.75/0.59  fof(f965,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) ) | (~spl2_11 | ~spl2_68)),
% 1.75/0.59    inference(superposition,[],[f948,f122])).
% 1.75/0.59  fof(f949,plain,(
% 1.75/0.59    spl2_68 | ~spl2_1 | ~spl2_27 | ~spl2_65),
% 1.75/0.59    inference(avatar_split_clause,[],[f805,f717,f284,f79,f947])).
% 1.75/0.59  fof(f719,plain,(
% 1.75/0.59    spl2_65),
% 1.75/0.59    inference(avatar_split_clause,[],[f67,f717])).
% 1.75/0.59  fof(f67,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f40])).
% 1.75/0.59  fof(f40,plain,(
% 1.75/0.59    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.75/0.59    inference(ennf_transformation,[],[f11])).
% 1.75/0.59  fof(f11,axiom,(
% 1.75/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).
% 1.75/0.59  fof(f621,plain,(
% 1.75/0.59    spl2_59 | ~spl2_1 | ~spl2_8 | ~spl2_24 | ~spl2_32 | ~spl2_58),
% 1.75/0.59    inference(avatar_split_clause,[],[f613,f596,f330,f247,f107,f79,f619])).
% 1.75/0.59  fof(f107,plain,(
% 1.75/0.59    spl2_8 <=> ! [X1,X0] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.75/0.59  fof(f596,plain,(
% 1.75/0.59    spl2_58 <=> ! [X1,X0] : (~r1_tarski(X0,k6_relat_1(X1)) | ~v1_relat_1(X0) | k8_relat_1(X1,X0) = X0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 1.75/0.59  fof(f613,plain,(
% 1.75/0.59    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X2),X1) = k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X1))) ) | (~spl2_1 | ~spl2_8 | ~spl2_24 | ~spl2_32 | ~spl2_58)),
% 1.75/0.59    inference(forward_demodulation,[],[f612,f331])).
% 1.75/0.59  fof(f612,plain,(
% 1.75/0.59    ( ! [X2,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k8_relat_1(X1,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) ) | (~spl2_1 | ~spl2_8 | ~spl2_24 | ~spl2_32 | ~spl2_58)),
% 1.75/0.59    inference(subsumption_resolution,[],[f611,f248])).
% 1.75/0.59  fof(f611,plain,(
% 1.75/0.59    ( ! [X2,X1] : (~v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k8_relat_1(X1,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) ) | (~spl2_1 | ~spl2_8 | ~spl2_32 | ~spl2_58)),
% 1.75/0.59    inference(forward_demodulation,[],[f610,f331])).
% 1.75/0.59  fof(f610,plain,(
% 1.75/0.59    ( ! [X2,X1] : (~v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k8_relat_1(X1,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) ) | (~spl2_1 | ~spl2_8 | ~spl2_58)),
% 1.75/0.59    inference(subsumption_resolution,[],[f600,f80])).
% 1.75/0.59  fof(f600,plain,(
% 1.75/0.59    ( ! [X2,X1] : (~v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k8_relat_1(X1,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_8 | ~spl2_58)),
% 1.75/0.59    inference(resolution,[],[f597,f108])).
% 1.75/0.59  fof(f108,plain,(
% 1.75/0.59    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) ) | ~spl2_8),
% 1.75/0.59    inference(avatar_component_clause,[],[f107])).
% 1.75/0.59  fof(f597,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k6_relat_1(X1)) | ~v1_relat_1(X0) | k8_relat_1(X1,X0) = X0) ) | ~spl2_58),
% 1.75/0.59    inference(avatar_component_clause,[],[f596])).
% 1.75/0.59  fof(f598,plain,(
% 1.75/0.59    spl2_58 | ~spl2_34 | ~spl2_57),
% 1.75/0.59    inference(avatar_split_clause,[],[f594,f585,f342,f596])).
% 1.75/0.59  fof(f342,plain,(
% 1.75/0.59    spl2_34 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 1.75/0.59  fof(f585,plain,(
% 1.75/0.59    spl2_57 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X1),X0) | ~r1_tarski(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 1.75/0.59  fof(f594,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k6_relat_1(X1)) | ~v1_relat_1(X0) | k8_relat_1(X1,X0) = X0) ) | (~spl2_34 | ~spl2_57)),
% 1.75/0.59    inference(duplicate_literal_removal,[],[f591])).
% 1.75/0.59  fof(f591,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k6_relat_1(X1)) | ~v1_relat_1(X0) | k8_relat_1(X1,X0) = X0 | ~v1_relat_1(X0)) ) | (~spl2_34 | ~spl2_57)),
% 1.75/0.59    inference(resolution,[],[f586,f343])).
% 1.75/0.59  fof(f343,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) ) | ~spl2_34),
% 1.75/0.59    inference(avatar_component_clause,[],[f342])).
% 1.75/0.59  fof(f586,plain,(
% 1.75/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~r1_tarski(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) ) | ~spl2_57),
% 1.75/0.59    inference(avatar_component_clause,[],[f585])).
% 1.75/0.59  fof(f587,plain,(
% 1.75/0.59    spl2_57 | ~spl2_1 | ~spl2_4 | ~spl2_52),
% 1.75/0.59    inference(avatar_split_clause,[],[f574,f546,f91,f79,f585])).
% 1.75/0.59  fof(f91,plain,(
% 1.75/0.59    spl2_4 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.75/0.59  fof(f546,plain,(
% 1.75/0.59    spl2_52 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 1.75/0.59  fof(f574,plain,(
% 1.75/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~r1_tarski(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) ) | (~spl2_1 | ~spl2_4 | ~spl2_52)),
% 1.75/0.59    inference(subsumption_resolution,[],[f571,f80])).
% 1.75/0.59  fof(f571,plain,(
% 1.75/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~r1_tarski(X1,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) ) | (~spl2_4 | ~spl2_52)),
% 1.75/0.59    inference(superposition,[],[f547,f92])).
% 1.75/0.59  fof(f92,plain,(
% 1.75/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_4),
% 1.75/0.59    inference(avatar_component_clause,[],[f91])).
% 1.75/0.59  fof(f547,plain,(
% 1.75/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_52),
% 1.75/0.59    inference(avatar_component_clause,[],[f546])).
% 1.75/0.59  fof(f548,plain,(
% 1.75/0.59    spl2_52),
% 1.75/0.59    inference(avatar_split_clause,[],[f55,f546])).
% 1.75/0.59  fof(f55,plain,(
% 1.75/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f29])).
% 1.75/0.59  fof(f29,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.75/0.59    inference(flattening,[],[f28])).
% 1.75/0.59  fof(f28,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.75/0.59    inference(ennf_transformation,[],[f13])).
% 1.75/0.59  fof(f13,axiom,(
% 1.75/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.75/0.59  fof(f445,plain,(
% 1.75/0.59    ~spl2_45 | ~spl2_1 | ~spl2_17 | ~spl2_18),
% 1.75/0.59    inference(avatar_split_clause,[],[f232,f162,f158,f79,f442])).
% 1.75/0.59  fof(f232,plain,(
% 1.75/0.59    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | (~spl2_1 | ~spl2_17 | ~spl2_18)),
% 1.75/0.59    inference(backward_demodulation,[],[f172,f217])).
% 1.75/0.59  fof(f172,plain,(
% 1.75/0.59    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) | (~spl2_1 | ~spl2_17)),
% 1.75/0.59    inference(backward_demodulation,[],[f76,f169])).
% 1.75/0.59  fof(f76,plain,(
% 1.75/0.59    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.75/0.59    inference(definition_unfolding,[],[f46,f75])).
% 1.75/0.59  fof(f46,plain,(
% 1.75/0.59    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.75/0.59    inference(cnf_transformation,[],[f45])).
% 1.75/0.59  fof(f45,plain,(
% 1.75/0.59    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.75/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f44])).
% 1.75/0.59  fof(f44,plain,(
% 1.75/0.59    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.75/0.59    introduced(choice_axiom,[])).
% 1.75/0.59  fof(f25,plain,(
% 1.75/0.59    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.75/0.59    inference(ennf_transformation,[],[f23])).
% 1.75/0.59  fof(f23,negated_conjecture,(
% 1.75/0.59    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.75/0.59    inference(negated_conjecture,[],[f22])).
% 1.75/0.59  fof(f22,conjecture,(
% 1.75/0.59    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.75/0.59  fof(f344,plain,(
% 1.75/0.59    spl2_34),
% 1.75/0.59    inference(avatar_split_clause,[],[f63,f342])).
% 1.75/0.59  fof(f63,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f35])).
% 1.75/0.59  fof(f35,plain,(
% 1.75/0.59    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.75/0.59    inference(flattening,[],[f34])).
% 1.75/0.59  fof(f34,plain,(
% 1.75/0.59    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.75/0.59    inference(ennf_transformation,[],[f10])).
% 1.75/0.59  fof(f10,axiom,(
% 1.75/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 1.75/0.59  fof(f332,plain,(
% 1.75/0.59    spl2_32 | ~spl2_1 | ~spl2_18),
% 1.75/0.59    inference(avatar_split_clause,[],[f214,f162,f79,f330])).
% 1.75/0.59  fof(f286,plain,(
% 1.75/0.59    spl2_27 | ~spl2_1 | ~spl2_17 | ~spl2_18),
% 1.75/0.59    inference(avatar_split_clause,[],[f217,f162,f158,f79,f284])).
% 1.75/0.59  fof(f249,plain,(
% 1.75/0.59    spl2_24 | ~spl2_1 | ~spl2_17 | ~spl2_18 | ~spl2_20),
% 1.75/0.59    inference(avatar_split_clause,[],[f225,f185,f162,f158,f79,f247])).
% 1.75/0.59  fof(f225,plain,(
% 1.75/0.59    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | (~spl2_1 | ~spl2_17 | ~spl2_18 | ~spl2_20)),
% 1.75/0.59    inference(backward_demodulation,[],[f186,f217])).
% 1.75/0.59  fof(f187,plain,(
% 1.75/0.59    spl2_20 | ~spl2_1 | ~spl2_15 | ~spl2_17),
% 1.75/0.59    inference(avatar_split_clause,[],[f173,f158,f142,f79,f185])).
% 1.75/0.59  fof(f173,plain,(
% 1.75/0.59    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ) | (~spl2_1 | ~spl2_15 | ~spl2_17)),
% 1.75/0.59    inference(backward_demodulation,[],[f143,f169])).
% 1.75/0.59  fof(f164,plain,(
% 1.75/0.59    spl2_18),
% 1.75/0.59    inference(avatar_split_clause,[],[f60,f162])).
% 1.75/0.59  fof(f60,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f32])).
% 1.75/0.59  fof(f32,plain,(
% 1.75/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.75/0.59    inference(ennf_transformation,[],[f19])).
% 1.75/0.59  fof(f19,axiom,(
% 1.75/0.59    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.75/0.59  fof(f160,plain,(
% 1.75/0.59    spl2_17),
% 1.75/0.59    inference(avatar_split_clause,[],[f59,f158])).
% 1.75/0.59  fof(f59,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f31])).
% 1.75/0.59  fof(f31,plain,(
% 1.75/0.59    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.75/0.59    inference(ennf_transformation,[],[f9])).
% 1.75/0.59  fof(f9,axiom,(
% 1.75/0.59    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 1.75/0.59  fof(f144,plain,(
% 1.75/0.59    spl2_15 | ~spl2_1 | ~spl2_14),
% 1.75/0.59    inference(avatar_split_clause,[],[f140,f137,f79,f142])).
% 1.75/0.59  fof(f137,plain,(
% 1.75/0.59    spl2_14 <=> ! [X1,X0] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(k6_relat_1(X1),X0)))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.75/0.59  fof(f140,plain,(
% 1.75/0.59    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ) | (~spl2_1 | ~spl2_14)),
% 1.75/0.59    inference(resolution,[],[f138,f80])).
% 1.75/0.59  fof(f138,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(k6_relat_1(X1),X0))) ) | ~spl2_14),
% 1.75/0.59    inference(avatar_component_clause,[],[f137])).
% 1.75/0.59  fof(f139,plain,(
% 1.75/0.59    spl2_14 | ~spl2_1 | ~spl2_10),
% 1.75/0.59    inference(avatar_split_clause,[],[f135,f115,f79,f137])).
% 1.75/0.59  fof(f115,plain,(
% 1.75/0.59    spl2_10 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.75/0.59  fof(f135,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(k6_relat_1(X1),X0))) ) | (~spl2_1 | ~spl2_10)),
% 1.75/0.59    inference(resolution,[],[f116,f80])).
% 1.75/0.59  fof(f116,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) ) | ~spl2_10),
% 1.75/0.59    inference(avatar_component_clause,[],[f115])).
% 1.75/0.59  fof(f123,plain,(
% 1.75/0.59    spl2_11 | ~spl2_1 | ~spl2_3 | ~spl2_6),
% 1.75/0.59    inference(avatar_split_clause,[],[f119,f99,f87,f79,f121])).
% 1.75/0.59  fof(f87,plain,(
% 1.75/0.59    spl2_3 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.75/0.59  fof(f99,plain,(
% 1.75/0.59    spl2_6 <=> ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.75/0.59  fof(f119,plain,(
% 1.75/0.59    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | (~spl2_1 | ~spl2_3 | ~spl2_6)),
% 1.75/0.59    inference(forward_demodulation,[],[f118,f88])).
% 1.75/0.59  fof(f88,plain,(
% 1.75/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_3),
% 1.75/0.59    inference(avatar_component_clause,[],[f87])).
% 1.75/0.59  fof(f118,plain,(
% 1.75/0.59    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) ) | (~spl2_1 | ~spl2_6)),
% 1.75/0.59    inference(resolution,[],[f100,f80])).
% 1.75/0.59  fof(f100,plain,(
% 1.75/0.59    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) ) | ~spl2_6),
% 1.75/0.59    inference(avatar_component_clause,[],[f99])).
% 1.75/0.59  fof(f117,plain,(
% 1.75/0.59    spl2_10),
% 1.75/0.59    inference(avatar_split_clause,[],[f64,f115])).
% 1.75/0.59  fof(f64,plain,(
% 1.75/0.59    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f37])).
% 1.75/0.59  fof(f37,plain,(
% 1.75/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.75/0.59    inference(flattening,[],[f36])).
% 1.75/0.59  fof(f36,plain,(
% 1.75/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f6])).
% 1.75/0.59  fof(f6,axiom,(
% 1.75/0.59    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.75/0.59  fof(f109,plain,(
% 1.75/0.59    spl2_8),
% 1.75/0.59    inference(avatar_split_clause,[],[f61,f107])).
% 1.75/0.59  fof(f61,plain,(
% 1.75/0.59    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f33])).
% 1.75/0.59  fof(f33,plain,(
% 1.75/0.59    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.75/0.59    inference(ennf_transformation,[],[f17])).
% 1.75/0.59  fof(f17,axiom,(
% 1.75/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 1.75/0.59  fof(f101,plain,(
% 1.75/0.59    spl2_6),
% 1.75/0.59    inference(avatar_split_clause,[],[f52,f99])).
% 1.75/0.59  fof(f52,plain,(
% 1.75/0.59    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f26])).
% 1.75/0.59  fof(f26,plain,(
% 1.75/0.59    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.75/0.59    inference(ennf_transformation,[],[f20])).
% 1.75/0.59  fof(f20,axiom,(
% 1.75/0.59    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 1.75/0.59  fof(f97,plain,(
% 1.75/0.59    spl2_5),
% 1.75/0.59    inference(avatar_split_clause,[],[f47,f95])).
% 1.75/0.59  fof(f47,plain,(
% 1.75/0.59    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.75/0.59    inference(cnf_transformation,[],[f16])).
% 1.75/0.59  fof(f16,axiom,(
% 1.75/0.59    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 1.75/0.59  fof(f93,plain,(
% 1.75/0.59    spl2_4),
% 1.75/0.59    inference(avatar_split_clause,[],[f51,f91])).
% 1.75/0.59  fof(f51,plain,(
% 1.75/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.75/0.59    inference(cnf_transformation,[],[f15])).
% 1.75/0.59  fof(f15,axiom,(
% 1.75/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.75/0.59  fof(f89,plain,(
% 1.75/0.59    spl2_3),
% 1.75/0.59    inference(avatar_split_clause,[],[f50,f87])).
% 1.75/0.59  fof(f50,plain,(
% 1.75/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.75/0.59    inference(cnf_transformation,[],[f15])).
% 1.75/0.59  fof(f81,plain,(
% 1.75/0.59    spl2_1),
% 1.75/0.59    inference(avatar_split_clause,[],[f48,f79])).
% 1.75/0.59  fof(f48,plain,(
% 1.75/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.75/0.59    inference(cnf_transformation,[],[f24])).
% 1.75/0.59  fof(f24,plain,(
% 1.75/0.59    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.75/0.59    inference(pure_predicate_removal,[],[f21])).
% 1.75/0.59  fof(f21,axiom,(
% 1.75/0.59    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 1.75/0.59  % SZS output end Proof for theBenchmark
% 1.75/0.59  % (19194)------------------------------
% 1.75/0.59  % (19194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.59  % (19194)Termination reason: Refutation
% 1.75/0.59  
% 1.75/0.59  % (19194)Memory used [KB]: 8187
% 1.75/0.59  % (19194)Time elapsed: 0.120 s
% 1.75/0.59  % (19194)------------------------------
% 1.75/0.59  % (19194)------------------------------
% 1.75/0.60  % (19186)Success in time 0.234 s
%------------------------------------------------------------------------------
