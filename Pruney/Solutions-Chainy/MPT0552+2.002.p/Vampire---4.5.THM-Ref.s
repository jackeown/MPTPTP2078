%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:45 EST 2020

% Result     : Theorem 7.12s
% Output     : Refutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 346 expanded)
%              Number of leaves         :   40 ( 160 expanded)
%              Depth                    :    8
%              Number of atoms          :  518 ( 918 expanded)
%              Number of equality atoms :   54 ( 116 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3007,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f94,f110,f115,f119,f129,f136,f201,f205,f262,f269,f285,f312,f331,f351,f374,f443,f472,f479,f686,f721,f778,f807,f1304,f1339,f2792,f2903,f2948,f3004])).

fof(f3004,plain,
    ( spl3_5
    | ~ spl3_139 ),
    inference(avatar_contradiction_clause,[],[f2983])).

fof(f2983,plain,
    ( $false
    | spl3_5
    | ~ spl3_139 ),
    inference(unit_resulting_resolution,[],[f114,f2947])).

fof(f2947,plain,
    ( ! [X10,X11] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X10,X11)),k3_xboole_0(k9_relat_1(sK2,X10),k9_relat_1(sK2,X11)))
    | ~ spl3_139 ),
    inference(avatar_component_clause,[],[f2946])).

fof(f2946,plain,
    ( spl3_139
  <=> ! [X11,X10] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X10,X11)),k3_xboole_0(k9_relat_1(sK2,X10),k9_relat_1(sK2,X11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_139])])).

fof(f114,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl3_5
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f2948,plain,
    ( spl3_139
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_137 ),
    inference(avatar_split_clause,[],[f2935,f2901,f441,f372,f203,f134,f2946])).

fof(f134,plain,
    ( spl3_8
  <=> ! [X1,X0] : v1_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f203,plain,
    ( spl3_14
  <=> ! [X5,X6] :
        ( r1_tarski(k9_relat_1(sK2,X5),k2_relat_1(X6))
        | ~ r1_tarski(k7_relat_1(sK2,X5),X6)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(k7_relat_1(sK2,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f372,plain,
    ( spl3_28
  <=> ! [X4] : v1_relat_1(k7_relat_1(sK2,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f441,plain,
    ( spl3_30
  <=> ! [X1,X0] : k3_xboole_0(k9_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k8_relat_1(X1,sK2),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f2901,plain,
    ( spl3_137
  <=> ! [X3,X4] : r1_tarski(k7_relat_1(sK2,k3_xboole_0(X4,X3)),k7_relat_1(k8_relat_1(k9_relat_1(sK2,X3),sK2),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_137])])).

fof(f2935,plain,
    ( ! [X10,X11] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X10,X11)),k3_xboole_0(k9_relat_1(sK2,X10),k9_relat_1(sK2,X11)))
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_28
    | ~ spl3_30
    | ~ spl3_137 ),
    inference(forward_demodulation,[],[f2934,f442])).

fof(f442,plain,
    ( ! [X0,X1] : k3_xboole_0(k9_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k8_relat_1(X1,sK2),X0))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f441])).

fof(f2934,plain,
    ( ! [X10,X11] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X10,X11)),k2_relat_1(k7_relat_1(k8_relat_1(k9_relat_1(sK2,X11),sK2),X10)))
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_28
    | ~ spl3_137 ),
    inference(subsumption_resolution,[],[f2933,f373])).

fof(f373,plain,
    ( ! [X4] : v1_relat_1(k7_relat_1(sK2,X4))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f372])).

fof(f2933,plain,
    ( ! [X10,X11] :
        ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X10,X11)),k2_relat_1(k7_relat_1(k8_relat_1(k9_relat_1(sK2,X11),sK2),X10)))
        | ~ v1_relat_1(k7_relat_1(sK2,k3_xboole_0(X10,X11))) )
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_137 ),
    inference(subsumption_resolution,[],[f2907,f135])).

fof(f135,plain,
    ( ! [X0,X1] : v1_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f2907,plain,
    ( ! [X10,X11] :
        ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X10,X11)),k2_relat_1(k7_relat_1(k8_relat_1(k9_relat_1(sK2,X11),sK2),X10)))
        | ~ v1_relat_1(k7_relat_1(k8_relat_1(k9_relat_1(sK2,X11),sK2),X10))
        | ~ v1_relat_1(k7_relat_1(sK2,k3_xboole_0(X10,X11))) )
    | ~ spl3_14
    | ~ spl3_137 ),
    inference(resolution,[],[f2902,f204])).

fof(f204,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(k7_relat_1(sK2,X5),X6)
        | r1_tarski(k9_relat_1(sK2,X5),k2_relat_1(X6))
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(k7_relat_1(sK2,X5)) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f203])).

fof(f2902,plain,
    ( ! [X4,X3] : r1_tarski(k7_relat_1(sK2,k3_xboole_0(X4,X3)),k7_relat_1(k8_relat_1(k9_relat_1(sK2,X3),sK2),X4))
    | ~ spl3_137 ),
    inference(avatar_component_clause,[],[f2901])).

fof(f2903,plain,
    ( spl3_137
    | ~ spl3_85
    | ~ spl3_129 ),
    inference(avatar_split_clause,[],[f2815,f2790,f1337,f2901])).

fof(f1337,plain,
    ( spl3_85
  <=> ! [X7,X8,X6] : r1_tarski(k7_relat_1(k8_relat_1(X6,sK2),k3_xboole_0(X7,X8)),k7_relat_1(k8_relat_1(X6,sK2),X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).

fof(f2790,plain,
    ( spl3_129
  <=> ! [X1,X0] : k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_129])])).

fof(f2815,plain,
    ( ! [X4,X3] : r1_tarski(k7_relat_1(sK2,k3_xboole_0(X4,X3)),k7_relat_1(k8_relat_1(k9_relat_1(sK2,X3),sK2),X4))
    | ~ spl3_85
    | ~ spl3_129 ),
    inference(superposition,[],[f1338,f2791])).

fof(f2791,plain,
    ( ! [X0,X1] : k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),k3_xboole_0(X0,X1))
    | ~ spl3_129 ),
    inference(avatar_component_clause,[],[f2790])).

fof(f1338,plain,
    ( ! [X6,X8,X7] : r1_tarski(k7_relat_1(k8_relat_1(X6,sK2),k3_xboole_0(X7,X8)),k7_relat_1(k8_relat_1(X6,sK2),X7))
    | ~ spl3_85 ),
    inference(avatar_component_clause,[],[f1337])).

fof(f2792,plain,
    ( spl3_129
    | ~ spl3_20
    | ~ spl3_28
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f820,f805,f372,f283,f2790])).

fof(f283,plain,
    ( spl3_20
  <=> ! [X1,X2] :
        ( k7_relat_1(sK2,X1) = k7_relat_1(k8_relat_1(X2,sK2),X1)
        | ~ r1_tarski(k9_relat_1(sK2,X1),X2)
        | ~ v1_relat_1(k7_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f805,plain,
    ( spl3_56
  <=> ! [X3,X4] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X3,X4)),k9_relat_1(sK2,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f820,plain,
    ( ! [X0,X1] : k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),k3_xboole_0(X0,X1))
    | ~ spl3_20
    | ~ spl3_28
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f808,f373])).

fof(f808,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),k3_xboole_0(X0,X1))
        | ~ v1_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))) )
    | ~ spl3_20
    | ~ spl3_56 ),
    inference(resolution,[],[f806,f284])).

fof(f284,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(k9_relat_1(sK2,X1),X2)
        | k7_relat_1(sK2,X1) = k7_relat_1(k8_relat_1(X2,sK2),X1)
        | ~ v1_relat_1(k7_relat_1(sK2,X1)) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f283])).

fof(f806,plain,
    ( ! [X4,X3] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X3,X4)),k9_relat_1(sK2,X4))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f805])).

fof(f1339,plain,
    ( spl3_85
    | ~ spl3_8
    | ~ spl3_81 ),
    inference(avatar_split_clause,[],[f1329,f1302,f134,f1337])).

fof(f1302,plain,
    ( spl3_81
  <=> ! [X40,X41,X39] : k7_relat_1(k8_relat_1(X40,sK2),k3_xboole_0(X39,X41)) = k7_relat_1(k7_relat_1(k8_relat_1(X40,sK2),X39),X41) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f1329,plain,
    ( ! [X6,X8,X7] : r1_tarski(k7_relat_1(k8_relat_1(X6,sK2),k3_xboole_0(X7,X8)),k7_relat_1(k8_relat_1(X6,sK2),X7))
    | ~ spl3_8
    | ~ spl3_81 ),
    inference(subsumption_resolution,[],[f1319,f135])).

fof(f1319,plain,
    ( ! [X6,X8,X7] :
        ( r1_tarski(k7_relat_1(k8_relat_1(X6,sK2),k3_xboole_0(X7,X8)),k7_relat_1(k8_relat_1(X6,sK2),X7))
        | ~ v1_relat_1(k7_relat_1(k8_relat_1(X6,sK2),X7)) )
    | ~ spl3_81 ),
    inference(superposition,[],[f53,f1303])).

fof(f1303,plain,
    ( ! [X39,X41,X40] : k7_relat_1(k8_relat_1(X40,sK2),k3_xboole_0(X39,X41)) = k7_relat_1(k7_relat_1(k8_relat_1(X40,sK2),X39),X41)
    | ~ spl3_81 ),
    inference(avatar_component_clause,[],[f1302])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f1304,plain,
    ( spl3_81
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f404,f372,f117,f108,f1302])).

fof(f108,plain,
    ( spl3_4
  <=> ! [X16,X15] : k7_relat_1(k8_relat_1(X15,sK2),X16) = k8_relat_1(X15,k7_relat_1(sK2,X16)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f117,plain,
    ( spl3_6
  <=> ! [X18,X17] : k7_relat_1(k7_relat_1(sK2,X17),X18) = k7_relat_1(sK2,k3_xboole_0(X17,X18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f404,plain,
    ( ! [X39,X41,X40] : k7_relat_1(k8_relat_1(X40,sK2),k3_xboole_0(X39,X41)) = k7_relat_1(k7_relat_1(k8_relat_1(X40,sK2),X39),X41)
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f403,f109])).

fof(f109,plain,
    ( ! [X15,X16] : k7_relat_1(k8_relat_1(X15,sK2),X16) = k8_relat_1(X15,k7_relat_1(sK2,X16))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f403,plain,
    ( ! [X39,X41,X40] : k7_relat_1(k8_relat_1(X40,k7_relat_1(sK2,X39)),X41) = k7_relat_1(k8_relat_1(X40,sK2),k3_xboole_0(X39,X41))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f402,f109])).

fof(f402,plain,
    ( ! [X39,X41,X40] : k7_relat_1(k8_relat_1(X40,k7_relat_1(sK2,X39)),X41) = k8_relat_1(X40,k7_relat_1(sK2,k3_xboole_0(X39,X41)))
    | ~ spl3_6
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f394,f118])).

fof(f118,plain,
    ( ! [X17,X18] : k7_relat_1(k7_relat_1(sK2,X17),X18) = k7_relat_1(sK2,k3_xboole_0(X17,X18))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f394,plain,
    ( ! [X39,X41,X40] : k7_relat_1(k8_relat_1(X40,k7_relat_1(sK2,X39)),X41) = k8_relat_1(X40,k7_relat_1(k7_relat_1(sK2,X39),X41))
    | ~ spl3_28 ),
    inference(resolution,[],[f373,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(f807,plain,
    ( spl3_56
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f798,f776,f372,f199,f92,f805])).

fof(f92,plain,
    ( spl3_2
  <=> ! [X8] : k2_relat_1(k7_relat_1(sK2,X8)) = k9_relat_1(sK2,X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f199,plain,
    ( spl3_13
  <=> ! [X3,X4] :
        ( r1_tarski(k2_relat_1(X4),k9_relat_1(sK2,X3))
        | ~ r1_tarski(X4,k7_relat_1(sK2,X3))
        | ~ v1_relat_1(k7_relat_1(sK2,X3))
        | ~ v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f776,plain,
    ( spl3_55
  <=> ! [X7,X8] : r1_tarski(k7_relat_1(sK2,k3_xboole_0(X7,X8)),k7_relat_1(sK2,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f798,plain,
    ( ! [X4,X3] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X3,X4)),k9_relat_1(sK2,X4))
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f797,f93])).

fof(f93,plain,
    ( ! [X8] : k2_relat_1(k7_relat_1(sK2,X8)) = k9_relat_1(sK2,X8)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f797,plain,
    ( ! [X4,X3] : r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X3,X4))),k9_relat_1(sK2,X4))
    | ~ spl3_13
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f796,f373])).

fof(f796,plain,
    ( ! [X4,X3] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X3,X4))),k9_relat_1(sK2,X4))
        | ~ v1_relat_1(k7_relat_1(sK2,k3_xboole_0(X3,X4))) )
    | ~ spl3_13
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f780,f373])).

fof(f780,plain,
    ( ! [X4,X3] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X3,X4))),k9_relat_1(sK2,X4))
        | ~ v1_relat_1(k7_relat_1(sK2,X4))
        | ~ v1_relat_1(k7_relat_1(sK2,k3_xboole_0(X3,X4))) )
    | ~ spl3_13
    | ~ spl3_55 ),
    inference(resolution,[],[f777,f200])).

fof(f200,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X4,k7_relat_1(sK2,X3))
        | r1_tarski(k2_relat_1(X4),k9_relat_1(sK2,X3))
        | ~ v1_relat_1(k7_relat_1(sK2,X3))
        | ~ v1_relat_1(X4) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f199])).

fof(f777,plain,
    ( ! [X8,X7] : r1_tarski(k7_relat_1(sK2,k3_xboole_0(X7,X8)),k7_relat_1(sK2,X8))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f776])).

fof(f778,plain,
    ( spl3_55
    | ~ spl3_27
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f768,f719,f470,f466,f349,f776])).

fof(f349,plain,
    ( spl3_27
  <=> ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f466,plain,
    ( spl3_33
  <=> v1_relat_1(k8_relat_1(k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f470,plain,
    ( spl3_34
  <=> ! [X6] : r1_tarski(k7_relat_1(sK2,X6),k8_relat_1(k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f719,plain,
    ( spl3_51
  <=> ! [X11,X13,X12] :
        ( r1_tarski(k7_relat_1(sK2,k3_xboole_0(X11,X12)),k7_relat_1(X13,X12))
        | ~ r1_tarski(k7_relat_1(sK2,X11),X13)
        | ~ v1_relat_1(X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f768,plain,
    ( ! [X8,X7] : r1_tarski(k7_relat_1(sK2,k3_xboole_0(X7,X8)),k7_relat_1(sK2,X8))
    | ~ spl3_27
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_51 ),
    inference(forward_demodulation,[],[f767,f350])).

fof(f350,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f349])).

fof(f767,plain,
    ( ! [X8,X7] : r1_tarski(k7_relat_1(sK2,k3_xboole_0(X7,X8)),k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X8))
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_51 ),
    inference(subsumption_resolution,[],[f756,f467])).

fof(f467,plain,
    ( v1_relat_1(k8_relat_1(k2_relat_1(sK2),sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f466])).

fof(f756,plain,
    ( ! [X8,X7] :
        ( r1_tarski(k7_relat_1(sK2,k3_xboole_0(X7,X8)),k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X8))
        | ~ v1_relat_1(k8_relat_1(k2_relat_1(sK2),sK2)) )
    | ~ spl3_34
    | ~ spl3_51 ),
    inference(resolution,[],[f720,f471])).

fof(f471,plain,
    ( ! [X6] : r1_tarski(k7_relat_1(sK2,X6),k8_relat_1(k2_relat_1(sK2),sK2))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f470])).

fof(f720,plain,
    ( ! [X12,X13,X11] :
        ( ~ r1_tarski(k7_relat_1(sK2,X11),X13)
        | r1_tarski(k7_relat_1(sK2,k3_xboole_0(X11,X12)),k7_relat_1(X13,X12))
        | ~ v1_relat_1(X13) )
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f719])).

fof(f721,plain,
    ( spl3_51
    | ~ spl3_28
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f687,f684,f372,f719])).

fof(f684,plain,
    ( spl3_47
  <=> ! [X11,X13,X12] :
        ( r1_tarski(k7_relat_1(sK2,k3_xboole_0(X11,X12)),k7_relat_1(X13,X12))
        | ~ r1_tarski(k7_relat_1(sK2,X11),X13)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(k7_relat_1(sK2,X11)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f687,plain,
    ( ! [X12,X13,X11] :
        ( r1_tarski(k7_relat_1(sK2,k3_xboole_0(X11,X12)),k7_relat_1(X13,X12))
        | ~ r1_tarski(k7_relat_1(sK2,X11),X13)
        | ~ v1_relat_1(X13) )
    | ~ spl3_28
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f685,f373])).

fof(f685,plain,
    ( ! [X12,X13,X11] :
        ( r1_tarski(k7_relat_1(sK2,k3_xboole_0(X11,X12)),k7_relat_1(X13,X12))
        | ~ r1_tarski(k7_relat_1(sK2,X11),X13)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(k7_relat_1(sK2,X11)) )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f684])).

fof(f686,plain,
    ( spl3_47
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f160,f117,f684])).

fof(f160,plain,
    ( ! [X12,X13,X11] :
        ( r1_tarski(k7_relat_1(sK2,k3_xboole_0(X11,X12)),k7_relat_1(X13,X12))
        | ~ r1_tarski(k7_relat_1(sK2,X11),X13)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(k7_relat_1(sK2,X11)) )
    | ~ spl3_6 ),
    inference(superposition,[],[f57,f118])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f479,plain,
    ( ~ spl3_1
    | spl3_33 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | ~ spl3_1
    | spl3_33 ),
    inference(subsumption_resolution,[],[f474,f72])).

fof(f72,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f474,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_33 ),
    inference(resolution,[],[f468,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f468,plain,
    ( ~ v1_relat_1(k8_relat_1(k2_relat_1(sK2),sK2))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f466])).

fof(f472,plain,
    ( ~ spl3_33
    | spl3_34
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f356,f349,f470,f466])).

fof(f356,plain,
    ( ! [X6] :
        ( r1_tarski(k7_relat_1(sK2,X6),k8_relat_1(k2_relat_1(sK2),sK2))
        | ~ v1_relat_1(k8_relat_1(k2_relat_1(sK2),sK2)) )
    | ~ spl3_27 ),
    inference(superposition,[],[f53,f350])).

fof(f443,plain,
    ( spl3_30
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_24
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f363,f349,f310,f108,f92,f441])).

fof(f310,plain,
    ( spl3_24
  <=> ! [X27,X29,X28] : k2_relat_1(k8_relat_1(X29,k7_relat_1(k8_relat_1(X27,sK2),X28))) = k3_xboole_0(k2_relat_1(k7_relat_1(k8_relat_1(X27,sK2),X28)),X29) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f363,plain,
    ( ! [X0,X1] : k3_xboole_0(k9_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k8_relat_1(X1,sK2),X0))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_24
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f362,f109])).

fof(f362,plain,
    ( ! [X0,X1] : k2_relat_1(k8_relat_1(X1,k7_relat_1(sK2,X0))) = k3_xboole_0(k9_relat_1(sK2,X0),X1)
    | ~ spl3_2
    | ~ spl3_24
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f352,f93])).

fof(f352,plain,
    ( ! [X0,X1] : k2_relat_1(k8_relat_1(X1,k7_relat_1(sK2,X0))) = k3_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),X1)
    | ~ spl3_24
    | ~ spl3_27 ),
    inference(superposition,[],[f311,f350])).

fof(f311,plain,
    ( ! [X28,X29,X27] : k2_relat_1(k8_relat_1(X29,k7_relat_1(k8_relat_1(X27,sK2),X28))) = k3_xboole_0(k2_relat_1(k7_relat_1(k8_relat_1(X27,sK2),X28)),X29)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f310])).

fof(f374,plain,
    ( spl3_28
    | ~ spl3_8
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f354,f349,f134,f372])).

fof(f354,plain,
    ( ! [X4] : v1_relat_1(k7_relat_1(sK2,X4))
    | ~ spl3_8
    | ~ spl3_27 ),
    inference(superposition,[],[f135,f350])).

fof(f351,plain,
    ( spl3_27
    | ~ spl3_1
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f347,f329,f70,f349])).

fof(f329,plain,
    ( spl3_26
  <=> ! [X2] :
        ( k7_relat_1(sK2,X2) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X2)
        | ~ v1_relat_1(k7_relat_1(sK2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f347,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X0)
    | ~ spl3_1
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f345,f72])).

fof(f345,plain,
    ( ! [X0] :
        ( k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_26 ),
    inference(resolution,[],[f330,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f330,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k7_relat_1(sK2,X2))
        | k7_relat_1(sK2,X2) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X2) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f329])).

fof(f331,plain,
    ( spl3_26
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f324,f283,f267,f329])).

fof(f267,plain,
    ( spl3_18
  <=> ! [X0] : r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f324,plain,
    ( ! [X2] :
        ( k7_relat_1(sK2,X2) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X2)
        | ~ v1_relat_1(k7_relat_1(sK2,X2)) )
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(resolution,[],[f284,f268])).

fof(f268,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f267])).

fof(f312,plain,
    ( spl3_24
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f147,f134,f310])).

fof(f147,plain,
    ( ! [X28,X29,X27] : k2_relat_1(k8_relat_1(X29,k7_relat_1(k8_relat_1(X27,sK2),X28))) = k3_xboole_0(k2_relat_1(k7_relat_1(k8_relat_1(X27,sK2),X28)),X29)
    | ~ spl3_8 ),
    inference(resolution,[],[f135,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f285,plain,
    ( spl3_20
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f98,f92,f70,f283])).

fof(f98,plain,
    ( ! [X2,X1] :
        ( k7_relat_1(sK2,X1) = k7_relat_1(k8_relat_1(X2,sK2),X1)
        | ~ r1_tarski(k9_relat_1(sK2,X1),X2)
        | ~ v1_relat_1(k7_relat_1(sK2,X1)) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f95,f87])).

fof(f87,plain,
    ( ! [X15,X16] : k7_relat_1(k8_relat_1(X15,sK2),X16) = k8_relat_1(X15,k7_relat_1(sK2,X16))
    | ~ spl3_1 ),
    inference(resolution,[],[f72,f64])).

fof(f95,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(k9_relat_1(sK2,X1),X2)
        | k7_relat_1(sK2,X1) = k8_relat_1(X2,k7_relat_1(sK2,X1))
        | ~ v1_relat_1(k7_relat_1(sK2,X1)) )
    | ~ spl3_2 ),
    inference(superposition,[],[f56,f93])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f269,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f265,f260,f70,f267])).

fof(f260,plain,
    ( spl3_17
  <=> ! [X2] :
        ( r1_tarski(k9_relat_1(sK2,X2),k2_relat_1(sK2))
        | ~ v1_relat_1(k7_relat_1(sK2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f265,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f263,f72])).

fof(f263,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_17 ),
    inference(resolution,[],[f261,f52])).

fof(f261,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k7_relat_1(sK2,X2))
        | r1_tarski(k9_relat_1(sK2,X2),k2_relat_1(sK2)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f260])).

fof(f262,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f254,f203,f70,f260])).

fof(f254,plain,
    ( ! [X2] :
        ( r1_tarski(k9_relat_1(sK2,X2),k2_relat_1(sK2))
        | ~ v1_relat_1(k7_relat_1(sK2,X2)) )
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f251,f72])).

fof(f251,plain,
    ( ! [X2] :
        ( r1_tarski(k9_relat_1(sK2,X2),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(k7_relat_1(sK2,X2)) )
    | ~ spl3_14 ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,
    ( ! [X2] :
        ( r1_tarski(k9_relat_1(sK2,X2),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(k7_relat_1(sK2,X2))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_14 ),
    inference(resolution,[],[f204,f53])).

fof(f205,plain,
    ( spl3_14
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f97,f92,f203])).

fof(f97,plain,
    ( ! [X6,X5] :
        ( r1_tarski(k9_relat_1(sK2,X5),k2_relat_1(X6))
        | ~ r1_tarski(k7_relat_1(sK2,X5),X6)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(k7_relat_1(sK2,X5)) )
    | ~ spl3_2 ),
    inference(superposition,[],[f46,f93])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f201,plain,
    ( spl3_13
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f96,f92,f199])).

fof(f96,plain,
    ( ! [X4,X3] :
        ( r1_tarski(k2_relat_1(X4),k9_relat_1(sK2,X3))
        | ~ r1_tarski(X4,k7_relat_1(sK2,X3))
        | ~ v1_relat_1(k7_relat_1(sK2,X3))
        | ~ v1_relat_1(X4) )
    | ~ spl3_2 ),
    inference(superposition,[],[f46,f93])).

fof(f136,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f132,f127,f70,f134])).

fof(f127,plain,
    ( spl3_7
  <=> ! [X15,X14] :
        ( v1_relat_1(k7_relat_1(k8_relat_1(X14,sK2),X15))
        | ~ v1_relat_1(k7_relat_1(sK2,X15)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f132,plain,
    ( ! [X0,X1] : v1_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f130,f72])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_7 ),
    inference(resolution,[],[f128,f52])).

fof(f128,plain,
    ( ! [X14,X15] :
        ( ~ v1_relat_1(k7_relat_1(sK2,X15))
        | v1_relat_1(k7_relat_1(k8_relat_1(X14,sK2),X15)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f125,f108,f127])).

fof(f125,plain,
    ( ! [X14,X15] :
        ( v1_relat_1(k7_relat_1(k8_relat_1(X14,sK2),X15))
        | ~ v1_relat_1(k7_relat_1(sK2,X15)) )
    | ~ spl3_4 ),
    inference(superposition,[],[f51,f109])).

fof(f119,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f88,f70,f117])).

fof(f88,plain,
    ( ! [X17,X18] : k7_relat_1(k7_relat_1(sK2,X17),X18) = k7_relat_1(sK2,k3_xboole_0(X17,X18))
    | ~ spl3_1 ),
    inference(resolution,[],[f72,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f115,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f44,f112])).

fof(f44,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f110,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f87,f70,f108])).

fof(f94,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f82,f70,f92])).

fof(f82,plain,
    ( ! [X8] : k2_relat_1(k7_relat_1(sK2,X8)) = k9_relat_1(sK2,X8)
    | ~ spl3_1 ),
    inference(resolution,[],[f72,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f73,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f43,f70])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (27995)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (28011)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (27997)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (28000)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.40/0.55  % (28011)Refutation not found, incomplete strategy% (28011)------------------------------
% 1.40/0.55  % (28011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (28011)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (28011)Memory used [KB]: 10618
% 1.40/0.55  % (28011)Time elapsed: 0.145 s
% 1.40/0.55  % (28011)------------------------------
% 1.40/0.55  % (28011)------------------------------
% 1.40/0.55  % (28005)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.40/0.55  % (28003)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.40/0.56  % (28005)Refutation not found, incomplete strategy% (28005)------------------------------
% 1.40/0.56  % (28005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (28023)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.40/0.56  % (28026)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.58/0.57  % (28005)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.57  
% 1.58/0.57  % (28005)Memory used [KB]: 10746
% 1.58/0.57  % (28005)Time elapsed: 0.134 s
% 1.58/0.57  % (28005)------------------------------
% 1.58/0.57  % (28005)------------------------------
% 1.58/0.57  % (28016)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.58/0.57  % (27999)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.58/0.57  % (28008)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.58/0.57  % (28009)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.58/0.57  % (28019)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.58/0.59  % (28012)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.58/0.59  % (28001)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.58/0.59  % (28002)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.58/0.59  % (28020)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.58/0.59  % (28010)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.58/0.60  % (28025)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.58/0.60  % (27998)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.58/0.60  % (28025)Refutation not found, incomplete strategy% (28025)------------------------------
% 1.58/0.60  % (28025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.60  % (28025)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.60  
% 1.58/0.60  % (28025)Memory used [KB]: 10746
% 1.58/0.60  % (28025)Time elapsed: 0.180 s
% 1.58/0.60  % (28025)------------------------------
% 1.58/0.60  % (28025)------------------------------
% 1.58/0.61  % (27996)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.58/0.61  % (28015)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.58/0.61  % (28017)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.58/0.61  % (28014)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.58/0.61  % (28024)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.58/0.62  % (28007)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.58/0.62  % (28006)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 2.24/0.65  % (28021)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.24/0.66  % (28013)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.24/0.67  % (28004)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.81/0.74  % (28066)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.90/0.77  % (28067)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.90/0.80  % (28068)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.90/0.80  % (28068)Refutation not found, incomplete strategy% (28068)------------------------------
% 2.90/0.80  % (28068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.80  % (28068)Termination reason: Refutation not found, incomplete strategy
% 2.90/0.80  
% 2.90/0.80  % (28068)Memory used [KB]: 6140
% 2.90/0.80  % (28068)Time elapsed: 0.139 s
% 2.90/0.80  % (28068)------------------------------
% 2.90/0.80  % (28068)------------------------------
% 2.90/0.81  % (27998)Refutation not found, incomplete strategy% (27998)------------------------------
% 2.90/0.81  % (27998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.81  % (27998)Termination reason: Refutation not found, incomplete strategy
% 2.90/0.81  
% 2.90/0.81  % (27998)Memory used [KB]: 6140
% 2.90/0.81  % (27998)Time elapsed: 0.380 s
% 2.90/0.81  % (27998)------------------------------
% 2.90/0.81  % (27998)------------------------------
% 3.40/0.82  % (27997)Time limit reached!
% 3.40/0.82  % (27997)------------------------------
% 3.40/0.82  % (27997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.40/0.83  % (27997)Termination reason: Time limit
% 3.40/0.83  % (27997)Termination phase: Saturation
% 3.40/0.83  
% 3.40/0.83  % (27997)Memory used [KB]: 8827
% 3.40/0.83  % (27997)Time elapsed: 0.400 s
% 3.40/0.83  % (27997)------------------------------
% 3.40/0.83  % (27997)------------------------------
% 3.40/0.85  % (28020)Time limit reached!
% 3.40/0.85  % (28020)------------------------------
% 3.40/0.85  % (28020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.40/0.85  % (28020)Termination reason: Time limit
% 3.40/0.85  
% 3.40/0.85  % (28020)Memory used [KB]: 13048
% 3.40/0.85  % (28020)Time elapsed: 0.427 s
% 3.40/0.85  % (28020)------------------------------
% 3.40/0.85  % (28020)------------------------------
% 3.80/0.90  % (28098)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.80/0.94  % (28026)Time limit reached!
% 3.80/0.94  % (28026)------------------------------
% 3.80/0.94  % (28026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.80/0.94  % (28026)Termination reason: Time limit
% 3.80/0.94  % (28026)Termination phase: Saturation
% 3.80/0.94  
% 3.80/0.94  % (28026)Memory used [KB]: 5884
% 3.80/0.94  % (28026)Time elapsed: 0.521 s
% 3.80/0.94  % (28026)------------------------------
% 3.80/0.94  % (28026)------------------------------
% 3.80/0.94  % (28001)Time limit reached!
% 3.80/0.94  % (28001)------------------------------
% 3.80/0.94  % (28001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.80/0.94  % (28001)Termination reason: Time limit
% 3.80/0.94  
% 3.80/0.94  % (28001)Memory used [KB]: 15223
% 3.80/0.94  % (28001)Time elapsed: 0.519 s
% 3.80/0.94  % (28001)------------------------------
% 3.80/0.94  % (28001)------------------------------
% 3.80/0.94  % (28115)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.36/0.96  % (28108)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.36/0.96  % (28009)Time limit reached!
% 4.36/0.96  % (28009)------------------------------
% 4.36/0.96  % (28009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.96  % (28009)Termination reason: Time limit
% 4.36/0.96  % (28009)Termination phase: Saturation
% 4.36/0.96  
% 4.36/0.96  % (28009)Memory used [KB]: 4989
% 4.36/0.96  % (28009)Time elapsed: 0.500 s
% 4.36/0.96  % (28009)------------------------------
% 4.36/0.96  % (28009)------------------------------
% 4.36/0.97  % (28124)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.39/1.07  % (28179)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.39/1.07  % (28188)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 5.39/1.08  % (28002)Time limit reached!
% 5.39/1.08  % (28002)------------------------------
% 5.39/1.08  % (28002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.39/1.09  % (28002)Termination reason: Time limit
% 5.39/1.09  
% 5.39/1.09  % (28002)Memory used [KB]: 7803
% 5.39/1.09  % (28002)Time elapsed: 0.615 s
% 5.39/1.09  % (28002)------------------------------
% 5.39/1.09  % (28002)------------------------------
% 5.39/1.09  % (28196)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 6.36/1.22  % (28236)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 6.95/1.25  % (27996)Time limit reached!
% 6.95/1.25  % (27996)------------------------------
% 6.95/1.25  % (27996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.95/1.25  % (27996)Termination reason: Time limit
% 6.95/1.25  
% 6.95/1.25  % (27996)Memory used [KB]: 7675
% 6.95/1.25  % (27996)Time elapsed: 0.832 s
% 6.95/1.25  % (27996)------------------------------
% 6.95/1.25  % (27996)------------------------------
% 7.12/1.29  % (28196)Refutation found. Thanks to Tanya!
% 7.12/1.29  % SZS status Theorem for theBenchmark
% 7.12/1.30  % SZS output start Proof for theBenchmark
% 7.12/1.30  fof(f3007,plain,(
% 7.12/1.30    $false),
% 7.12/1.30    inference(avatar_sat_refutation,[],[f73,f94,f110,f115,f119,f129,f136,f201,f205,f262,f269,f285,f312,f331,f351,f374,f443,f472,f479,f686,f721,f778,f807,f1304,f1339,f2792,f2903,f2948,f3004])).
% 7.12/1.30  fof(f3004,plain,(
% 7.12/1.30    spl3_5 | ~spl3_139),
% 7.12/1.30    inference(avatar_contradiction_clause,[],[f2983])).
% 7.12/1.30  fof(f2983,plain,(
% 7.12/1.30    $false | (spl3_5 | ~spl3_139)),
% 7.12/1.30    inference(unit_resulting_resolution,[],[f114,f2947])).
% 7.12/1.30  fof(f2947,plain,(
% 7.12/1.30    ( ! [X10,X11] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X10,X11)),k3_xboole_0(k9_relat_1(sK2,X10),k9_relat_1(sK2,X11)))) ) | ~spl3_139),
% 7.12/1.30    inference(avatar_component_clause,[],[f2946])).
% 7.12/1.30  fof(f2946,plain,(
% 7.12/1.30    spl3_139 <=> ! [X11,X10] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X10,X11)),k3_xboole_0(k9_relat_1(sK2,X10),k9_relat_1(sK2,X11)))),
% 7.12/1.30    introduced(avatar_definition,[new_symbols(naming,[spl3_139])])).
% 7.12/1.30  fof(f114,plain,(
% 7.12/1.30    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) | spl3_5),
% 7.12/1.30    inference(avatar_component_clause,[],[f112])).
% 7.12/1.30  fof(f112,plain,(
% 7.12/1.30    spl3_5 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 7.12/1.30    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 7.12/1.30  fof(f2948,plain,(
% 7.12/1.30    spl3_139 | ~spl3_8 | ~spl3_14 | ~spl3_28 | ~spl3_30 | ~spl3_137),
% 7.12/1.30    inference(avatar_split_clause,[],[f2935,f2901,f441,f372,f203,f134,f2946])).
% 7.12/1.30  fof(f134,plain,(
% 7.12/1.30    spl3_8 <=> ! [X1,X0] : v1_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1))),
% 7.12/1.30    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 7.12/1.30  fof(f203,plain,(
% 7.12/1.30    spl3_14 <=> ! [X5,X6] : (r1_tarski(k9_relat_1(sK2,X5),k2_relat_1(X6)) | ~r1_tarski(k7_relat_1(sK2,X5),X6) | ~v1_relat_1(X6) | ~v1_relat_1(k7_relat_1(sK2,X5)))),
% 7.12/1.30    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 7.12/1.30  fof(f372,plain,(
% 7.12/1.30    spl3_28 <=> ! [X4] : v1_relat_1(k7_relat_1(sK2,X4))),
% 7.12/1.30    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 7.12/1.30  fof(f441,plain,(
% 7.12/1.30    spl3_30 <=> ! [X1,X0] : k3_xboole_0(k9_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k8_relat_1(X1,sK2),X0))),
% 7.12/1.30    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 7.12/1.30  fof(f2901,plain,(
% 7.12/1.30    spl3_137 <=> ! [X3,X4] : r1_tarski(k7_relat_1(sK2,k3_xboole_0(X4,X3)),k7_relat_1(k8_relat_1(k9_relat_1(sK2,X3),sK2),X4))),
% 7.12/1.30    introduced(avatar_definition,[new_symbols(naming,[spl3_137])])).
% 7.12/1.30  fof(f2935,plain,(
% 7.12/1.30    ( ! [X10,X11] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X10,X11)),k3_xboole_0(k9_relat_1(sK2,X10),k9_relat_1(sK2,X11)))) ) | (~spl3_8 | ~spl3_14 | ~spl3_28 | ~spl3_30 | ~spl3_137)),
% 7.12/1.30    inference(forward_demodulation,[],[f2934,f442])).
% 7.12/1.30  fof(f442,plain,(
% 7.12/1.30    ( ! [X0,X1] : (k3_xboole_0(k9_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k8_relat_1(X1,sK2),X0))) ) | ~spl3_30),
% 7.12/1.30    inference(avatar_component_clause,[],[f441])).
% 7.12/1.30  fof(f2934,plain,(
% 7.12/1.30    ( ! [X10,X11] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X10,X11)),k2_relat_1(k7_relat_1(k8_relat_1(k9_relat_1(sK2,X11),sK2),X10)))) ) | (~spl3_8 | ~spl3_14 | ~spl3_28 | ~spl3_137)),
% 7.12/1.30    inference(subsumption_resolution,[],[f2933,f373])).
% 7.12/1.30  fof(f373,plain,(
% 7.12/1.30    ( ! [X4] : (v1_relat_1(k7_relat_1(sK2,X4))) ) | ~spl3_28),
% 7.12/1.30    inference(avatar_component_clause,[],[f372])).
% 7.12/1.30  fof(f2933,plain,(
% 7.12/1.30    ( ! [X10,X11] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X10,X11)),k2_relat_1(k7_relat_1(k8_relat_1(k9_relat_1(sK2,X11),sK2),X10))) | ~v1_relat_1(k7_relat_1(sK2,k3_xboole_0(X10,X11)))) ) | (~spl3_8 | ~spl3_14 | ~spl3_137)),
% 7.12/1.30    inference(subsumption_resolution,[],[f2907,f135])).
% 7.12/1.30  fof(f135,plain,(
% 7.12/1.30    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1))) ) | ~spl3_8),
% 7.12/1.30    inference(avatar_component_clause,[],[f134])).
% 7.12/1.30  fof(f2907,plain,(
% 7.12/1.30    ( ! [X10,X11] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X10,X11)),k2_relat_1(k7_relat_1(k8_relat_1(k9_relat_1(sK2,X11),sK2),X10))) | ~v1_relat_1(k7_relat_1(k8_relat_1(k9_relat_1(sK2,X11),sK2),X10)) | ~v1_relat_1(k7_relat_1(sK2,k3_xboole_0(X10,X11)))) ) | (~spl3_14 | ~spl3_137)),
% 7.12/1.30    inference(resolution,[],[f2902,f204])).
% 7.12/1.30  fof(f204,plain,(
% 7.12/1.30    ( ! [X6,X5] : (~r1_tarski(k7_relat_1(sK2,X5),X6) | r1_tarski(k9_relat_1(sK2,X5),k2_relat_1(X6)) | ~v1_relat_1(X6) | ~v1_relat_1(k7_relat_1(sK2,X5))) ) | ~spl3_14),
% 7.12/1.30    inference(avatar_component_clause,[],[f203])).
% 7.12/1.30  fof(f2902,plain,(
% 7.12/1.30    ( ! [X4,X3] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X4,X3)),k7_relat_1(k8_relat_1(k9_relat_1(sK2,X3),sK2),X4))) ) | ~spl3_137),
% 7.12/1.30    inference(avatar_component_clause,[],[f2901])).
% 7.12/1.30  fof(f2903,plain,(
% 7.12/1.30    spl3_137 | ~spl3_85 | ~spl3_129),
% 7.12/1.30    inference(avatar_split_clause,[],[f2815,f2790,f1337,f2901])).
% 7.12/1.30  fof(f1337,plain,(
% 7.12/1.30    spl3_85 <=> ! [X7,X8,X6] : r1_tarski(k7_relat_1(k8_relat_1(X6,sK2),k3_xboole_0(X7,X8)),k7_relat_1(k8_relat_1(X6,sK2),X7))),
% 7.12/1.30    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).
% 7.12/1.30  fof(f2790,plain,(
% 7.12/1.30    spl3_129 <=> ! [X1,X0] : k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),k3_xboole_0(X0,X1))),
% 7.12/1.30    introduced(avatar_definition,[new_symbols(naming,[spl3_129])])).
% 7.12/1.30  fof(f2815,plain,(
% 7.12/1.30    ( ! [X4,X3] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X4,X3)),k7_relat_1(k8_relat_1(k9_relat_1(sK2,X3),sK2),X4))) ) | (~spl3_85 | ~spl3_129)),
% 7.12/1.30    inference(superposition,[],[f1338,f2791])).
% 7.12/1.30  fof(f2791,plain,(
% 7.12/1.30    ( ! [X0,X1] : (k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),k3_xboole_0(X0,X1))) ) | ~spl3_129),
% 7.12/1.30    inference(avatar_component_clause,[],[f2790])).
% 7.12/1.31  fof(f1338,plain,(
% 7.12/1.31    ( ! [X6,X8,X7] : (r1_tarski(k7_relat_1(k8_relat_1(X6,sK2),k3_xboole_0(X7,X8)),k7_relat_1(k8_relat_1(X6,sK2),X7))) ) | ~spl3_85),
% 7.12/1.31    inference(avatar_component_clause,[],[f1337])).
% 7.12/1.31  fof(f2792,plain,(
% 7.12/1.31    spl3_129 | ~spl3_20 | ~spl3_28 | ~spl3_56),
% 7.12/1.31    inference(avatar_split_clause,[],[f820,f805,f372,f283,f2790])).
% 7.12/1.31  fof(f283,plain,(
% 7.12/1.31    spl3_20 <=> ! [X1,X2] : (k7_relat_1(sK2,X1) = k7_relat_1(k8_relat_1(X2,sK2),X1) | ~r1_tarski(k9_relat_1(sK2,X1),X2) | ~v1_relat_1(k7_relat_1(sK2,X1)))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 7.12/1.31  fof(f805,plain,(
% 7.12/1.31    spl3_56 <=> ! [X3,X4] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X3,X4)),k9_relat_1(sK2,X4))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 7.12/1.31  fof(f820,plain,(
% 7.12/1.31    ( ! [X0,X1] : (k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),k3_xboole_0(X0,X1))) ) | (~spl3_20 | ~spl3_28 | ~spl3_56)),
% 7.12/1.31    inference(subsumption_resolution,[],[f808,f373])).
% 7.12/1.31  fof(f808,plain,(
% 7.12/1.31    ( ! [X0,X1] : (k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),k3_xboole_0(X0,X1)) | ~v1_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1)))) ) | (~spl3_20 | ~spl3_56)),
% 7.12/1.31    inference(resolution,[],[f806,f284])).
% 7.12/1.31  fof(f284,plain,(
% 7.12/1.31    ( ! [X2,X1] : (~r1_tarski(k9_relat_1(sK2,X1),X2) | k7_relat_1(sK2,X1) = k7_relat_1(k8_relat_1(X2,sK2),X1) | ~v1_relat_1(k7_relat_1(sK2,X1))) ) | ~spl3_20),
% 7.12/1.31    inference(avatar_component_clause,[],[f283])).
% 7.12/1.31  fof(f806,plain,(
% 7.12/1.31    ( ! [X4,X3] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X3,X4)),k9_relat_1(sK2,X4))) ) | ~spl3_56),
% 7.12/1.31    inference(avatar_component_clause,[],[f805])).
% 7.12/1.31  fof(f1339,plain,(
% 7.12/1.31    spl3_85 | ~spl3_8 | ~spl3_81),
% 7.12/1.31    inference(avatar_split_clause,[],[f1329,f1302,f134,f1337])).
% 7.12/1.31  fof(f1302,plain,(
% 7.12/1.31    spl3_81 <=> ! [X40,X41,X39] : k7_relat_1(k8_relat_1(X40,sK2),k3_xboole_0(X39,X41)) = k7_relat_1(k7_relat_1(k8_relat_1(X40,sK2),X39),X41)),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 7.12/1.31  fof(f1329,plain,(
% 7.12/1.31    ( ! [X6,X8,X7] : (r1_tarski(k7_relat_1(k8_relat_1(X6,sK2),k3_xboole_0(X7,X8)),k7_relat_1(k8_relat_1(X6,sK2),X7))) ) | (~spl3_8 | ~spl3_81)),
% 7.12/1.31    inference(subsumption_resolution,[],[f1319,f135])).
% 7.12/1.31  fof(f1319,plain,(
% 7.12/1.31    ( ! [X6,X8,X7] : (r1_tarski(k7_relat_1(k8_relat_1(X6,sK2),k3_xboole_0(X7,X8)),k7_relat_1(k8_relat_1(X6,sK2),X7)) | ~v1_relat_1(k7_relat_1(k8_relat_1(X6,sK2),X7))) ) | ~spl3_81),
% 7.12/1.31    inference(superposition,[],[f53,f1303])).
% 7.12/1.31  fof(f1303,plain,(
% 7.12/1.31    ( ! [X39,X41,X40] : (k7_relat_1(k8_relat_1(X40,sK2),k3_xboole_0(X39,X41)) = k7_relat_1(k7_relat_1(k8_relat_1(X40,sK2),X39),X41)) ) | ~spl3_81),
% 7.12/1.31    inference(avatar_component_clause,[],[f1302])).
% 7.12/1.31  fof(f53,plain,(
% 7.12/1.31    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 7.12/1.31    inference(cnf_transformation,[],[f27])).
% 7.12/1.31  fof(f27,plain,(
% 7.12/1.31    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 7.12/1.31    inference(ennf_transformation,[],[f18])).
% 7.12/1.31  fof(f18,axiom,(
% 7.12/1.31    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 7.12/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 7.12/1.31  fof(f1304,plain,(
% 7.12/1.31    spl3_81 | ~spl3_4 | ~spl3_6 | ~spl3_28),
% 7.12/1.31    inference(avatar_split_clause,[],[f404,f372,f117,f108,f1302])).
% 7.12/1.31  fof(f108,plain,(
% 7.12/1.31    spl3_4 <=> ! [X16,X15] : k7_relat_1(k8_relat_1(X15,sK2),X16) = k8_relat_1(X15,k7_relat_1(sK2,X16))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 7.12/1.31  fof(f117,plain,(
% 7.12/1.31    spl3_6 <=> ! [X18,X17] : k7_relat_1(k7_relat_1(sK2,X17),X18) = k7_relat_1(sK2,k3_xboole_0(X17,X18))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 7.12/1.31  fof(f404,plain,(
% 7.12/1.31    ( ! [X39,X41,X40] : (k7_relat_1(k8_relat_1(X40,sK2),k3_xboole_0(X39,X41)) = k7_relat_1(k7_relat_1(k8_relat_1(X40,sK2),X39),X41)) ) | (~spl3_4 | ~spl3_6 | ~spl3_28)),
% 7.12/1.31    inference(forward_demodulation,[],[f403,f109])).
% 7.12/1.31  fof(f109,plain,(
% 7.12/1.31    ( ! [X15,X16] : (k7_relat_1(k8_relat_1(X15,sK2),X16) = k8_relat_1(X15,k7_relat_1(sK2,X16))) ) | ~spl3_4),
% 7.12/1.31    inference(avatar_component_clause,[],[f108])).
% 7.12/1.31  fof(f403,plain,(
% 7.12/1.31    ( ! [X39,X41,X40] : (k7_relat_1(k8_relat_1(X40,k7_relat_1(sK2,X39)),X41) = k7_relat_1(k8_relat_1(X40,sK2),k3_xboole_0(X39,X41))) ) | (~spl3_4 | ~spl3_6 | ~spl3_28)),
% 7.12/1.31    inference(forward_demodulation,[],[f402,f109])).
% 7.12/1.31  fof(f402,plain,(
% 7.12/1.31    ( ! [X39,X41,X40] : (k7_relat_1(k8_relat_1(X40,k7_relat_1(sK2,X39)),X41) = k8_relat_1(X40,k7_relat_1(sK2,k3_xboole_0(X39,X41)))) ) | (~spl3_6 | ~spl3_28)),
% 7.12/1.31    inference(forward_demodulation,[],[f394,f118])).
% 7.12/1.31  fof(f118,plain,(
% 7.12/1.31    ( ! [X17,X18] : (k7_relat_1(k7_relat_1(sK2,X17),X18) = k7_relat_1(sK2,k3_xboole_0(X17,X18))) ) | ~spl3_6),
% 7.12/1.31    inference(avatar_component_clause,[],[f117])).
% 7.12/1.31  fof(f394,plain,(
% 7.12/1.31    ( ! [X39,X41,X40] : (k7_relat_1(k8_relat_1(X40,k7_relat_1(sK2,X39)),X41) = k8_relat_1(X40,k7_relat_1(k7_relat_1(sK2,X39),X41))) ) | ~spl3_28),
% 7.12/1.31    inference(resolution,[],[f373,f64])).
% 7.12/1.31  fof(f64,plain,(
% 7.12/1.31    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.12/1.31    inference(cnf_transformation,[],[f34])).
% 7.12/1.31  fof(f34,plain,(
% 7.12/1.31    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 7.12/1.31    inference(ennf_transformation,[],[f15])).
% 7.12/1.31  fof(f15,axiom,(
% 7.12/1.31    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 7.12/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).
% 7.12/1.31  fof(f807,plain,(
% 7.12/1.31    spl3_56 | ~spl3_2 | ~spl3_13 | ~spl3_28 | ~spl3_55),
% 7.12/1.31    inference(avatar_split_clause,[],[f798,f776,f372,f199,f92,f805])).
% 7.12/1.31  fof(f92,plain,(
% 7.12/1.31    spl3_2 <=> ! [X8] : k2_relat_1(k7_relat_1(sK2,X8)) = k9_relat_1(sK2,X8)),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 7.12/1.31  fof(f199,plain,(
% 7.12/1.31    spl3_13 <=> ! [X3,X4] : (r1_tarski(k2_relat_1(X4),k9_relat_1(sK2,X3)) | ~r1_tarski(X4,k7_relat_1(sK2,X3)) | ~v1_relat_1(k7_relat_1(sK2,X3)) | ~v1_relat_1(X4))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 7.12/1.31  fof(f776,plain,(
% 7.12/1.31    spl3_55 <=> ! [X7,X8] : r1_tarski(k7_relat_1(sK2,k3_xboole_0(X7,X8)),k7_relat_1(sK2,X8))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 7.12/1.31  fof(f798,plain,(
% 7.12/1.31    ( ! [X4,X3] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X3,X4)),k9_relat_1(sK2,X4))) ) | (~spl3_2 | ~spl3_13 | ~spl3_28 | ~spl3_55)),
% 7.12/1.31    inference(forward_demodulation,[],[f797,f93])).
% 7.12/1.31  fof(f93,plain,(
% 7.12/1.31    ( ! [X8] : (k2_relat_1(k7_relat_1(sK2,X8)) = k9_relat_1(sK2,X8)) ) | ~spl3_2),
% 7.12/1.31    inference(avatar_component_clause,[],[f92])).
% 7.12/1.31  fof(f797,plain,(
% 7.12/1.31    ( ! [X4,X3] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X3,X4))),k9_relat_1(sK2,X4))) ) | (~spl3_13 | ~spl3_28 | ~spl3_55)),
% 7.12/1.31    inference(subsumption_resolution,[],[f796,f373])).
% 7.12/1.31  fof(f796,plain,(
% 7.12/1.31    ( ! [X4,X3] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X3,X4))),k9_relat_1(sK2,X4)) | ~v1_relat_1(k7_relat_1(sK2,k3_xboole_0(X3,X4)))) ) | (~spl3_13 | ~spl3_28 | ~spl3_55)),
% 7.12/1.31    inference(subsumption_resolution,[],[f780,f373])).
% 7.12/1.31  fof(f780,plain,(
% 7.12/1.31    ( ! [X4,X3] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X3,X4))),k9_relat_1(sK2,X4)) | ~v1_relat_1(k7_relat_1(sK2,X4)) | ~v1_relat_1(k7_relat_1(sK2,k3_xboole_0(X3,X4)))) ) | (~spl3_13 | ~spl3_55)),
% 7.12/1.31    inference(resolution,[],[f777,f200])).
% 7.12/1.31  fof(f200,plain,(
% 7.12/1.31    ( ! [X4,X3] : (~r1_tarski(X4,k7_relat_1(sK2,X3)) | r1_tarski(k2_relat_1(X4),k9_relat_1(sK2,X3)) | ~v1_relat_1(k7_relat_1(sK2,X3)) | ~v1_relat_1(X4)) ) | ~spl3_13),
% 7.12/1.31    inference(avatar_component_clause,[],[f199])).
% 7.12/1.31  fof(f777,plain,(
% 7.12/1.31    ( ! [X8,X7] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X7,X8)),k7_relat_1(sK2,X8))) ) | ~spl3_55),
% 7.12/1.31    inference(avatar_component_clause,[],[f776])).
% 7.12/1.31  fof(f778,plain,(
% 7.12/1.31    spl3_55 | ~spl3_27 | ~spl3_33 | ~spl3_34 | ~spl3_51),
% 7.12/1.31    inference(avatar_split_clause,[],[f768,f719,f470,f466,f349,f776])).
% 7.12/1.31  fof(f349,plain,(
% 7.12/1.31    spl3_27 <=> ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X0)),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 7.12/1.31  fof(f466,plain,(
% 7.12/1.31    spl3_33 <=> v1_relat_1(k8_relat_1(k2_relat_1(sK2),sK2))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 7.12/1.31  fof(f470,plain,(
% 7.12/1.31    spl3_34 <=> ! [X6] : r1_tarski(k7_relat_1(sK2,X6),k8_relat_1(k2_relat_1(sK2),sK2))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 7.12/1.31  fof(f719,plain,(
% 7.12/1.31    spl3_51 <=> ! [X11,X13,X12] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X11,X12)),k7_relat_1(X13,X12)) | ~r1_tarski(k7_relat_1(sK2,X11),X13) | ~v1_relat_1(X13))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 7.12/1.31  fof(f768,plain,(
% 7.12/1.31    ( ! [X8,X7] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X7,X8)),k7_relat_1(sK2,X8))) ) | (~spl3_27 | ~spl3_33 | ~spl3_34 | ~spl3_51)),
% 7.12/1.31    inference(forward_demodulation,[],[f767,f350])).
% 7.12/1.31  fof(f350,plain,(
% 7.12/1.31    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X0)) ) | ~spl3_27),
% 7.12/1.31    inference(avatar_component_clause,[],[f349])).
% 7.12/1.31  fof(f767,plain,(
% 7.12/1.31    ( ! [X8,X7] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X7,X8)),k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X8))) ) | (~spl3_33 | ~spl3_34 | ~spl3_51)),
% 7.12/1.31    inference(subsumption_resolution,[],[f756,f467])).
% 7.12/1.31  fof(f467,plain,(
% 7.12/1.31    v1_relat_1(k8_relat_1(k2_relat_1(sK2),sK2)) | ~spl3_33),
% 7.12/1.31    inference(avatar_component_clause,[],[f466])).
% 7.12/1.31  fof(f756,plain,(
% 7.12/1.31    ( ! [X8,X7] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X7,X8)),k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X8)) | ~v1_relat_1(k8_relat_1(k2_relat_1(sK2),sK2))) ) | (~spl3_34 | ~spl3_51)),
% 7.12/1.31    inference(resolution,[],[f720,f471])).
% 7.12/1.31  fof(f471,plain,(
% 7.12/1.31    ( ! [X6] : (r1_tarski(k7_relat_1(sK2,X6),k8_relat_1(k2_relat_1(sK2),sK2))) ) | ~spl3_34),
% 7.12/1.31    inference(avatar_component_clause,[],[f470])).
% 7.12/1.31  fof(f720,plain,(
% 7.12/1.31    ( ! [X12,X13,X11] : (~r1_tarski(k7_relat_1(sK2,X11),X13) | r1_tarski(k7_relat_1(sK2,k3_xboole_0(X11,X12)),k7_relat_1(X13,X12)) | ~v1_relat_1(X13)) ) | ~spl3_51),
% 7.12/1.31    inference(avatar_component_clause,[],[f719])).
% 7.12/1.31  fof(f721,plain,(
% 7.12/1.31    spl3_51 | ~spl3_28 | ~spl3_47),
% 7.12/1.31    inference(avatar_split_clause,[],[f687,f684,f372,f719])).
% 7.12/1.31  fof(f684,plain,(
% 7.12/1.31    spl3_47 <=> ! [X11,X13,X12] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X11,X12)),k7_relat_1(X13,X12)) | ~r1_tarski(k7_relat_1(sK2,X11),X13) | ~v1_relat_1(X13) | ~v1_relat_1(k7_relat_1(sK2,X11)))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 7.12/1.31  fof(f687,plain,(
% 7.12/1.31    ( ! [X12,X13,X11] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X11,X12)),k7_relat_1(X13,X12)) | ~r1_tarski(k7_relat_1(sK2,X11),X13) | ~v1_relat_1(X13)) ) | (~spl3_28 | ~spl3_47)),
% 7.12/1.31    inference(subsumption_resolution,[],[f685,f373])).
% 7.12/1.31  fof(f685,plain,(
% 7.12/1.31    ( ! [X12,X13,X11] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X11,X12)),k7_relat_1(X13,X12)) | ~r1_tarski(k7_relat_1(sK2,X11),X13) | ~v1_relat_1(X13) | ~v1_relat_1(k7_relat_1(sK2,X11))) ) | ~spl3_47),
% 7.12/1.31    inference(avatar_component_clause,[],[f684])).
% 7.12/1.31  fof(f686,plain,(
% 7.12/1.31    spl3_47 | ~spl3_6),
% 7.12/1.31    inference(avatar_split_clause,[],[f160,f117,f684])).
% 7.12/1.31  fof(f160,plain,(
% 7.12/1.31    ( ! [X12,X13,X11] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X11,X12)),k7_relat_1(X13,X12)) | ~r1_tarski(k7_relat_1(sK2,X11),X13) | ~v1_relat_1(X13) | ~v1_relat_1(k7_relat_1(sK2,X11))) ) | ~spl3_6),
% 7.12/1.31    inference(superposition,[],[f57,f118])).
% 7.12/1.31  fof(f57,plain,(
% 7.12/1.31    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 7.12/1.31    inference(cnf_transformation,[],[f33])).
% 7.12/1.31  fof(f33,plain,(
% 7.12/1.31    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 7.12/1.31    inference(flattening,[],[f32])).
% 7.12/1.31  fof(f32,plain,(
% 7.12/1.31    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 7.12/1.31    inference(ennf_transformation,[],[f11])).
% 7.12/1.31  fof(f11,axiom,(
% 7.12/1.31    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 7.12/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 7.12/1.31  fof(f479,plain,(
% 7.12/1.31    ~spl3_1 | spl3_33),
% 7.12/1.31    inference(avatar_contradiction_clause,[],[f478])).
% 7.12/1.31  fof(f478,plain,(
% 7.12/1.31    $false | (~spl3_1 | spl3_33)),
% 7.12/1.31    inference(subsumption_resolution,[],[f474,f72])).
% 7.12/1.31  fof(f72,plain,(
% 7.12/1.31    v1_relat_1(sK2) | ~spl3_1),
% 7.12/1.31    inference(avatar_component_clause,[],[f70])).
% 7.12/1.31  fof(f70,plain,(
% 7.12/1.31    spl3_1 <=> v1_relat_1(sK2)),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 7.12/1.31  fof(f474,plain,(
% 7.12/1.31    ~v1_relat_1(sK2) | spl3_33),
% 7.12/1.31    inference(resolution,[],[f468,f51])).
% 7.12/1.31  fof(f51,plain,(
% 7.12/1.31    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 7.12/1.31    inference(cnf_transformation,[],[f25])).
% 7.12/1.31  fof(f25,plain,(
% 7.12/1.31    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 7.12/1.31    inference(ennf_transformation,[],[f9])).
% 7.12/1.31  fof(f9,axiom,(
% 7.12/1.31    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 7.12/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 7.12/1.31  fof(f468,plain,(
% 7.12/1.31    ~v1_relat_1(k8_relat_1(k2_relat_1(sK2),sK2)) | spl3_33),
% 7.12/1.31    inference(avatar_component_clause,[],[f466])).
% 7.12/1.31  fof(f472,plain,(
% 7.12/1.31    ~spl3_33 | spl3_34 | ~spl3_27),
% 7.12/1.31    inference(avatar_split_clause,[],[f356,f349,f470,f466])).
% 7.12/1.31  fof(f356,plain,(
% 7.12/1.31    ( ! [X6] : (r1_tarski(k7_relat_1(sK2,X6),k8_relat_1(k2_relat_1(sK2),sK2)) | ~v1_relat_1(k8_relat_1(k2_relat_1(sK2),sK2))) ) | ~spl3_27),
% 7.12/1.31    inference(superposition,[],[f53,f350])).
% 7.12/1.31  fof(f443,plain,(
% 7.12/1.31    spl3_30 | ~spl3_2 | ~spl3_4 | ~spl3_24 | ~spl3_27),
% 7.12/1.31    inference(avatar_split_clause,[],[f363,f349,f310,f108,f92,f441])).
% 7.12/1.31  fof(f310,plain,(
% 7.12/1.31    spl3_24 <=> ! [X27,X29,X28] : k2_relat_1(k8_relat_1(X29,k7_relat_1(k8_relat_1(X27,sK2),X28))) = k3_xboole_0(k2_relat_1(k7_relat_1(k8_relat_1(X27,sK2),X28)),X29)),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 7.12/1.31  fof(f363,plain,(
% 7.12/1.31    ( ! [X0,X1] : (k3_xboole_0(k9_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k8_relat_1(X1,sK2),X0))) ) | (~spl3_2 | ~spl3_4 | ~spl3_24 | ~spl3_27)),
% 7.12/1.31    inference(forward_demodulation,[],[f362,f109])).
% 7.12/1.31  fof(f362,plain,(
% 7.12/1.31    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X1,k7_relat_1(sK2,X0))) = k3_xboole_0(k9_relat_1(sK2,X0),X1)) ) | (~spl3_2 | ~spl3_24 | ~spl3_27)),
% 7.12/1.31    inference(forward_demodulation,[],[f352,f93])).
% 7.12/1.31  fof(f352,plain,(
% 7.12/1.31    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X1,k7_relat_1(sK2,X0))) = k3_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),X1)) ) | (~spl3_24 | ~spl3_27)),
% 7.12/1.31    inference(superposition,[],[f311,f350])).
% 7.12/1.31  fof(f311,plain,(
% 7.12/1.31    ( ! [X28,X29,X27] : (k2_relat_1(k8_relat_1(X29,k7_relat_1(k8_relat_1(X27,sK2),X28))) = k3_xboole_0(k2_relat_1(k7_relat_1(k8_relat_1(X27,sK2),X28)),X29)) ) | ~spl3_24),
% 7.12/1.31    inference(avatar_component_clause,[],[f310])).
% 7.12/1.31  fof(f374,plain,(
% 7.12/1.31    spl3_28 | ~spl3_8 | ~spl3_27),
% 7.12/1.31    inference(avatar_split_clause,[],[f354,f349,f134,f372])).
% 7.12/1.31  fof(f354,plain,(
% 7.12/1.31    ( ! [X4] : (v1_relat_1(k7_relat_1(sK2,X4))) ) | (~spl3_8 | ~spl3_27)),
% 7.12/1.31    inference(superposition,[],[f135,f350])).
% 7.12/1.31  fof(f351,plain,(
% 7.12/1.31    spl3_27 | ~spl3_1 | ~spl3_26),
% 7.12/1.31    inference(avatar_split_clause,[],[f347,f329,f70,f349])).
% 7.12/1.31  fof(f329,plain,(
% 7.12/1.31    spl3_26 <=> ! [X2] : (k7_relat_1(sK2,X2) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X2) | ~v1_relat_1(k7_relat_1(sK2,X2)))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 7.12/1.31  fof(f347,plain,(
% 7.12/1.31    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X0)) ) | (~spl3_1 | ~spl3_26)),
% 7.12/1.31    inference(subsumption_resolution,[],[f345,f72])).
% 7.12/1.31  fof(f345,plain,(
% 7.12/1.31    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X0) | ~v1_relat_1(sK2)) ) | ~spl3_26),
% 7.12/1.31    inference(resolution,[],[f330,f52])).
% 7.12/1.31  fof(f52,plain,(
% 7.12/1.31    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.12/1.31    inference(cnf_transformation,[],[f26])).
% 7.12/1.31  fof(f26,plain,(
% 7.12/1.31    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 7.12/1.31    inference(ennf_transformation,[],[f8])).
% 7.12/1.31  fof(f8,axiom,(
% 7.12/1.31    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 7.12/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 7.12/1.31  fof(f330,plain,(
% 7.12/1.31    ( ! [X2] : (~v1_relat_1(k7_relat_1(sK2,X2)) | k7_relat_1(sK2,X2) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X2)) ) | ~spl3_26),
% 7.12/1.31    inference(avatar_component_clause,[],[f329])).
% 7.12/1.31  fof(f331,plain,(
% 7.12/1.31    spl3_26 | ~spl3_18 | ~spl3_20),
% 7.12/1.31    inference(avatar_split_clause,[],[f324,f283,f267,f329])).
% 7.12/1.31  fof(f267,plain,(
% 7.12/1.31    spl3_18 <=> ! [X0] : r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 7.12/1.31  fof(f324,plain,(
% 7.12/1.31    ( ! [X2] : (k7_relat_1(sK2,X2) = k7_relat_1(k8_relat_1(k2_relat_1(sK2),sK2),X2) | ~v1_relat_1(k7_relat_1(sK2,X2))) ) | (~spl3_18 | ~spl3_20)),
% 7.12/1.31    inference(resolution,[],[f284,f268])).
% 7.12/1.31  fof(f268,plain,(
% 7.12/1.31    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2))) ) | ~spl3_18),
% 7.12/1.31    inference(avatar_component_clause,[],[f267])).
% 7.12/1.31  fof(f312,plain,(
% 7.12/1.31    spl3_24 | ~spl3_8),
% 7.12/1.31    inference(avatar_split_clause,[],[f147,f134,f310])).
% 7.12/1.31  fof(f147,plain,(
% 7.12/1.31    ( ! [X28,X29,X27] : (k2_relat_1(k8_relat_1(X29,k7_relat_1(k8_relat_1(X27,sK2),X28))) = k3_xboole_0(k2_relat_1(k7_relat_1(k8_relat_1(X27,sK2),X28)),X29)) ) | ~spl3_8),
% 7.12/1.31    inference(resolution,[],[f135,f55])).
% 7.12/1.31  fof(f55,plain,(
% 7.12/1.31    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.12/1.31    inference(cnf_transformation,[],[f29])).
% 7.12/1.31  fof(f29,plain,(
% 7.12/1.31    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.12/1.31    inference(ennf_transformation,[],[f12])).
% 7.12/1.31  fof(f12,axiom,(
% 7.12/1.31    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 7.12/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 7.12/1.31  fof(f285,plain,(
% 7.12/1.31    spl3_20 | ~spl3_1 | ~spl3_2),
% 7.12/1.31    inference(avatar_split_clause,[],[f98,f92,f70,f283])).
% 7.12/1.31  fof(f98,plain,(
% 7.12/1.31    ( ! [X2,X1] : (k7_relat_1(sK2,X1) = k7_relat_1(k8_relat_1(X2,sK2),X1) | ~r1_tarski(k9_relat_1(sK2,X1),X2) | ~v1_relat_1(k7_relat_1(sK2,X1))) ) | (~spl3_1 | ~spl3_2)),
% 7.12/1.31    inference(forward_demodulation,[],[f95,f87])).
% 7.12/1.31  fof(f87,plain,(
% 7.12/1.31    ( ! [X15,X16] : (k7_relat_1(k8_relat_1(X15,sK2),X16) = k8_relat_1(X15,k7_relat_1(sK2,X16))) ) | ~spl3_1),
% 7.12/1.31    inference(resolution,[],[f72,f64])).
% 7.12/1.31  fof(f95,plain,(
% 7.12/1.31    ( ! [X2,X1] : (~r1_tarski(k9_relat_1(sK2,X1),X2) | k7_relat_1(sK2,X1) = k8_relat_1(X2,k7_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X1))) ) | ~spl3_2),
% 7.12/1.31    inference(superposition,[],[f56,f93])).
% 7.12/1.31  fof(f56,plain,(
% 7.12/1.31    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.12/1.31    inference(cnf_transformation,[],[f31])).
% 7.12/1.31  fof(f31,plain,(
% 7.12/1.31    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.12/1.31    inference(flattening,[],[f30])).
% 7.12/1.31  fof(f30,plain,(
% 7.12/1.31    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.12/1.31    inference(ennf_transformation,[],[f13])).
% 7.12/1.31  fof(f13,axiom,(
% 7.12/1.31    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 7.12/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 7.12/1.31  fof(f269,plain,(
% 7.12/1.31    spl3_18 | ~spl3_1 | ~spl3_17),
% 7.12/1.31    inference(avatar_split_clause,[],[f265,f260,f70,f267])).
% 7.12/1.31  fof(f260,plain,(
% 7.12/1.31    spl3_17 <=> ! [X2] : (r1_tarski(k9_relat_1(sK2,X2),k2_relat_1(sK2)) | ~v1_relat_1(k7_relat_1(sK2,X2)))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 7.12/1.31  fof(f265,plain,(
% 7.12/1.31    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2))) ) | (~spl3_1 | ~spl3_17)),
% 7.12/1.31    inference(subsumption_resolution,[],[f263,f72])).
% 7.12/1.31  fof(f263,plain,(
% 7.12/1.31    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl3_17),
% 7.12/1.31    inference(resolution,[],[f261,f52])).
% 7.12/1.31  fof(f261,plain,(
% 7.12/1.31    ( ! [X2] : (~v1_relat_1(k7_relat_1(sK2,X2)) | r1_tarski(k9_relat_1(sK2,X2),k2_relat_1(sK2))) ) | ~spl3_17),
% 7.12/1.31    inference(avatar_component_clause,[],[f260])).
% 7.12/1.31  fof(f262,plain,(
% 7.12/1.31    spl3_17 | ~spl3_1 | ~spl3_14),
% 7.12/1.31    inference(avatar_split_clause,[],[f254,f203,f70,f260])).
% 7.12/1.31  fof(f254,plain,(
% 7.12/1.31    ( ! [X2] : (r1_tarski(k9_relat_1(sK2,X2),k2_relat_1(sK2)) | ~v1_relat_1(k7_relat_1(sK2,X2))) ) | (~spl3_1 | ~spl3_14)),
% 7.12/1.31    inference(subsumption_resolution,[],[f251,f72])).
% 7.12/1.31  fof(f251,plain,(
% 7.12/1.31    ( ! [X2] : (r1_tarski(k9_relat_1(sK2,X2),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(k7_relat_1(sK2,X2))) ) | ~spl3_14),
% 7.12/1.31    inference(duplicate_literal_removal,[],[f244])).
% 7.12/1.31  fof(f244,plain,(
% 7.12/1.31    ( ! [X2] : (r1_tarski(k9_relat_1(sK2,X2),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(k7_relat_1(sK2,X2)) | ~v1_relat_1(sK2)) ) | ~spl3_14),
% 7.12/1.31    inference(resolution,[],[f204,f53])).
% 7.12/1.31  fof(f205,plain,(
% 7.12/1.31    spl3_14 | ~spl3_2),
% 7.12/1.31    inference(avatar_split_clause,[],[f97,f92,f203])).
% 7.12/1.31  fof(f97,plain,(
% 7.12/1.31    ( ! [X6,X5] : (r1_tarski(k9_relat_1(sK2,X5),k2_relat_1(X6)) | ~r1_tarski(k7_relat_1(sK2,X5),X6) | ~v1_relat_1(X6) | ~v1_relat_1(k7_relat_1(sK2,X5))) ) | ~spl3_2),
% 7.12/1.31    inference(superposition,[],[f46,f93])).
% 7.12/1.31  fof(f46,plain,(
% 7.12/1.31    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.12/1.31    inference(cnf_transformation,[],[f23])).
% 7.12/1.31  fof(f23,plain,(
% 7.12/1.31    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.12/1.31    inference(flattening,[],[f22])).
% 7.12/1.31  fof(f22,plain,(
% 7.12/1.31    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.12/1.31    inference(ennf_transformation,[],[f17])).
% 7.12/1.31  fof(f17,axiom,(
% 7.12/1.31    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.12/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 7.12/1.31  fof(f201,plain,(
% 7.12/1.31    spl3_13 | ~spl3_2),
% 7.12/1.31    inference(avatar_split_clause,[],[f96,f92,f199])).
% 7.12/1.31  fof(f96,plain,(
% 7.12/1.31    ( ! [X4,X3] : (r1_tarski(k2_relat_1(X4),k9_relat_1(sK2,X3)) | ~r1_tarski(X4,k7_relat_1(sK2,X3)) | ~v1_relat_1(k7_relat_1(sK2,X3)) | ~v1_relat_1(X4)) ) | ~spl3_2),
% 7.12/1.31    inference(superposition,[],[f46,f93])).
% 7.12/1.31  fof(f136,plain,(
% 7.12/1.31    spl3_8 | ~spl3_1 | ~spl3_7),
% 7.12/1.31    inference(avatar_split_clause,[],[f132,f127,f70,f134])).
% 7.12/1.31  fof(f127,plain,(
% 7.12/1.31    spl3_7 <=> ! [X15,X14] : (v1_relat_1(k7_relat_1(k8_relat_1(X14,sK2),X15)) | ~v1_relat_1(k7_relat_1(sK2,X15)))),
% 7.12/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 7.12/1.31  fof(f132,plain,(
% 7.12/1.31    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1))) ) | (~spl3_1 | ~spl3_7)),
% 7.12/1.31    inference(subsumption_resolution,[],[f130,f72])).
% 7.12/1.31  fof(f130,plain,(
% 7.12/1.31    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) | ~v1_relat_1(sK2)) ) | ~spl3_7),
% 7.12/1.31    inference(resolution,[],[f128,f52])).
% 7.12/1.31  fof(f128,plain,(
% 7.12/1.31    ( ! [X14,X15] : (~v1_relat_1(k7_relat_1(sK2,X15)) | v1_relat_1(k7_relat_1(k8_relat_1(X14,sK2),X15))) ) | ~spl3_7),
% 7.12/1.31    inference(avatar_component_clause,[],[f127])).
% 7.12/1.31  fof(f129,plain,(
% 7.12/1.31    spl3_7 | ~spl3_4),
% 7.12/1.31    inference(avatar_split_clause,[],[f125,f108,f127])).
% 7.12/1.31  fof(f125,plain,(
% 7.12/1.31    ( ! [X14,X15] : (v1_relat_1(k7_relat_1(k8_relat_1(X14,sK2),X15)) | ~v1_relat_1(k7_relat_1(sK2,X15))) ) | ~spl3_4),
% 7.12/1.31    inference(superposition,[],[f51,f109])).
% 7.12/1.31  fof(f119,plain,(
% 7.12/1.31    spl3_6 | ~spl3_1),
% 7.12/1.31    inference(avatar_split_clause,[],[f88,f70,f117])).
% 7.12/1.31  fof(f88,plain,(
% 7.12/1.31    ( ! [X17,X18] : (k7_relat_1(k7_relat_1(sK2,X17),X18) = k7_relat_1(sK2,k3_xboole_0(X17,X18))) ) | ~spl3_1),
% 7.12/1.31    inference(resolution,[],[f72,f65])).
% 7.12/1.31  fof(f65,plain,(
% 7.12/1.31    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 7.12/1.31    inference(cnf_transformation,[],[f35])).
% 7.12/1.31  fof(f35,plain,(
% 7.12/1.31    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.12/1.31    inference(ennf_transformation,[],[f10])).
% 7.12/1.31  fof(f10,axiom,(
% 7.12/1.31    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 7.12/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 7.12/1.31  fof(f115,plain,(
% 7.12/1.31    ~spl3_5),
% 7.12/1.31    inference(avatar_split_clause,[],[f44,f112])).
% 7.12/1.31  fof(f44,plain,(
% 7.12/1.31    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 7.12/1.31    inference(cnf_transformation,[],[f39])).
% 7.12/1.31  fof(f39,plain,(
% 7.12/1.31    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 7.12/1.31    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f38])).
% 7.12/1.31  fof(f38,plain,(
% 7.12/1.31    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 7.12/1.31    introduced(choice_axiom,[])).
% 7.12/1.31  fof(f21,plain,(
% 7.12/1.31    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 7.12/1.31    inference(ennf_transformation,[],[f20])).
% 7.12/1.31  fof(f20,negated_conjecture,(
% 7.12/1.31    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 7.12/1.31    inference(negated_conjecture,[],[f19])).
% 7.12/1.31  fof(f19,conjecture,(
% 7.12/1.31    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 7.12/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 7.12/1.31  fof(f110,plain,(
% 7.12/1.31    spl3_4 | ~spl3_1),
% 7.12/1.31    inference(avatar_split_clause,[],[f87,f70,f108])).
% 7.12/1.31  fof(f94,plain,(
% 7.12/1.31    spl3_2 | ~spl3_1),
% 7.12/1.31    inference(avatar_split_clause,[],[f82,f70,f92])).
% 7.12/1.31  fof(f82,plain,(
% 7.12/1.31    ( ! [X8] : (k2_relat_1(k7_relat_1(sK2,X8)) = k9_relat_1(sK2,X8)) ) | ~spl3_1),
% 7.12/1.31    inference(resolution,[],[f72,f54])).
% 7.12/1.31  fof(f54,plain,(
% 7.12/1.31    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.12/1.31    inference(cnf_transformation,[],[f28])).
% 7.12/1.31  fof(f28,plain,(
% 7.12/1.31    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.12/1.31    inference(ennf_transformation,[],[f16])).
% 7.12/1.31  fof(f16,axiom,(
% 7.12/1.31    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.12/1.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 7.12/1.31  fof(f73,plain,(
% 7.12/1.31    spl3_1),
% 7.12/1.31    inference(avatar_split_clause,[],[f43,f70])).
% 7.12/1.31  fof(f43,plain,(
% 7.12/1.31    v1_relat_1(sK2)),
% 7.12/1.31    inference(cnf_transformation,[],[f39])).
% 7.12/1.31  % SZS output end Proof for theBenchmark
% 7.12/1.31  % (28196)------------------------------
% 7.12/1.31  % (28196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.12/1.31  % (28196)Termination reason: Refutation
% 7.12/1.31  
% 7.12/1.31  % (28196)Memory used [KB]: 12920
% 7.12/1.31  % (28196)Time elapsed: 0.320 s
% 7.12/1.31  % (28196)------------------------------
% 7.12/1.31  % (28196)------------------------------
% 7.12/1.31  % (27994)Success in time 0.943 s
%------------------------------------------------------------------------------
