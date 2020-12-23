%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 302 expanded)
%              Number of leaves         :   45 ( 158 expanded)
%              Depth                    :    6
%              Number of atoms          :  378 ( 656 expanded)
%              Number of equality atoms :  129 ( 268 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2632,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f45,f57,f61,f65,f69,f73,f77,f83,f91,f95,f110,f126,f130,f139,f148,f183,f209,f226,f313,f322,f357,f403,f456,f582,f606,f751,f1039,f1234,f1300,f2598,f2620])).

fof(f2620,plain,
    ( spl4_1
    | ~ spl4_8
    | ~ spl4_127 ),
    inference(avatar_contradiction_clause,[],[f2619])).

fof(f2619,plain,
    ( $false
    | spl4_1
    | ~ spl4_8
    | ~ spl4_127 ),
    inference(subsumption_resolution,[],[f36,f2599])).

fof(f2599,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)
    | ~ spl4_8
    | ~ spl4_127 ),
    inference(superposition,[],[f2597,f64])).

fof(f64,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_8
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f2597,plain,
    ( ! [X12,X10,X13,X11] : k2_enumset1(X10,X11,X12,X13) = k3_enumset1(X10,X10,X12,X11,X13)
    | ~ spl4_127 ),
    inference(avatar_component_clause,[],[f2596])).

fof(f2596,plain,
    ( spl4_127
  <=> ! [X11,X13,X10,X12] : k2_enumset1(X10,X11,X12,X13) = k3_enumset1(X10,X10,X12,X11,X13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_127])])).

fof(f36,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2598,plain,
    ( spl4_127
    | ~ spl4_85
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f1304,f1298,f1232,f2596])).

fof(f1232,plain,
    ( spl4_85
  <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k3_enumset1(X0,X1,X3,X2,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f1298,plain,
    ( spl4_87
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X1,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f1304,plain,
    ( ! [X12,X10,X13,X11] : k2_enumset1(X10,X11,X12,X13) = k3_enumset1(X10,X10,X12,X11,X13)
    | ~ spl4_85
    | ~ spl4_87 ),
    inference(superposition,[],[f1299,f1233])).

fof(f1233,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k3_enumset1(X0,X1,X3,X2,X4)
    | ~ spl4_85 ),
    inference(avatar_component_clause,[],[f1232])).

fof(f1299,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X1,X1,X2,X3)
    | ~ spl4_87 ),
    inference(avatar_component_clause,[],[f1298])).

fof(f1300,plain,
    ( spl4_87
    | ~ spl4_38
    | ~ spl4_42
    | ~ spl4_53
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f1040,f1037,f580,f401,f355,f1298])).

fof(f355,plain,
    ( spl4_38
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f401,plain,
    ( spl4_42
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f580,plain,
    ( spl4_53
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f1037,plain,
    ( spl4_78
  <=> ! [X1,X3,X0,X2] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k4_enumset1(X0,X0,X1,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f1040,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X1,X1,X2,X3)
    | ~ spl4_38
    | ~ spl4_42
    | ~ spl4_53
    | ~ spl4_78 ),
    inference(forward_demodulation,[],[f1038,f718])).

fof(f718,plain,
    ( ! [X61,X59,X62,X60] : k2_xboole_0(k1_tarski(X62),k1_enumset1(X59,X60,X61)) = k2_enumset1(X62,X59,X60,X61)
    | ~ spl4_38
    | ~ spl4_42
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f703,f356])).

fof(f356,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f355])).

fof(f703,plain,
    ( ! [X61,X59,X62,X60] : k3_enumset1(X62,X59,X60,X61,X61) = k2_xboole_0(k1_tarski(X62),k1_enumset1(X59,X60,X61))
    | ~ spl4_42
    | ~ spl4_53 ),
    inference(superposition,[],[f402,f581])).

fof(f581,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f580])).

fof(f402,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f401])).

fof(f1038,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k4_enumset1(X0,X0,X1,X1,X2,X3)
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f1037])).

fof(f1234,plain,
    ( spl4_85
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f770,f749,f71,f67,f1232])).

fof(f67,plain,
    ( spl4_9
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f71,plain,
    ( spl4_10
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f749,plain,
    ( spl4_60
  <=> ! [X9,X5,X7,X8,X10,X6] : k5_enumset1(X5,X6,X7,X8,X8,X9,X10) = k4_enumset1(X6,X5,X7,X9,X8,X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f770,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k3_enumset1(X0,X1,X3,X2,X4)
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_60 ),
    inference(forward_demodulation,[],[f752,f68])).

fof(f68,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f752,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k4_enumset1(X0,X0,X1,X3,X2,X4)
    | ~ spl4_10
    | ~ spl4_60 ),
    inference(superposition,[],[f750,f72])).

fof(f72,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f750,plain,
    ( ! [X6,X10,X8,X7,X5,X9] : k5_enumset1(X5,X6,X7,X8,X8,X9,X10) = k4_enumset1(X6,X5,X7,X9,X8,X10)
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f749])).

fof(f1039,plain,
    ( spl4_78
    | ~ spl4_2
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f459,f454,f39,f1037])).

fof(f39,plain,
    ( spl4_2
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f454,plain,
    ( spl4_47
  <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f459,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k4_enumset1(X0,X0,X1,X1,X2,X3)
    | ~ spl4_2
    | ~ spl4_47 ),
    inference(superposition,[],[f455,f40])).

fof(f40,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f455,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f454])).

fof(f751,plain,
    ( spl4_60
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_35
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f607,f604,f320,f71,f59,f749])).

fof(f59,plain,
    ( spl4_7
  <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f320,plain,
    ( spl4_35
  <=> ! [X9,X11,X7,X8,X10,X12,X6] : k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X7,X6,X8)) = k5_enumset1(X9,X10,X11,X12,X6,X7,X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f604,plain,
    ( spl4_54
  <=> ! [X9,X5,X7,X8,X10,X6] : k5_enumset1(X5,X6,X7,X8,X8,X9,X10) = k2_xboole_0(k1_enumset1(X6,X5,X7),k1_enumset1(X8,X9,X10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f607,plain,
    ( ! [X6,X10,X8,X7,X5,X9] : k5_enumset1(X5,X6,X7,X8,X8,X9,X10) = k4_enumset1(X6,X5,X7,X9,X8,X10)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_35
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f605,f329])).

fof(f329,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X4,X3,X5)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f323,f72])).

fof(f323,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k5_enumset1(X0,X0,X1,X2,X4,X3,X5)
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(superposition,[],[f321,f60])).

fof(f60,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f321,plain,
    ( ! [X6,X12,X10,X8,X7,X11,X9] : k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X7,X6,X8)) = k5_enumset1(X9,X10,X11,X12,X6,X7,X8)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f320])).

fof(f605,plain,
    ( ! [X6,X10,X8,X7,X5,X9] : k5_enumset1(X5,X6,X7,X8,X8,X9,X10) = k2_xboole_0(k1_enumset1(X6,X5,X7),k1_enumset1(X8,X9,X10))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f604])).

fof(f606,plain,
    ( spl4_54
    | ~ spl4_6
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f213,f207,f55,f604])).

fof(f55,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f207,plain,
    ( spl4_27
  <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k2_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f213,plain,
    ( ! [X6,X10,X8,X7,X5,X9] : k5_enumset1(X5,X6,X7,X8,X8,X9,X10) = k2_xboole_0(k1_enumset1(X6,X5,X7),k1_enumset1(X8,X9,X10))
    | ~ spl4_6
    | ~ spl4_27 ),
    inference(superposition,[],[f208,f56])).

fof(f56,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f208,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k2_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f207])).

fof(f582,plain,
    ( spl4_53
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f362,f355,f63,f59,f580])).

fof(f362,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f358,f60])).

fof(f358,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)
    | ~ spl4_8
    | ~ spl4_38 ),
    inference(superposition,[],[f356,f64])).

fof(f456,plain,
    ( spl4_47
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f220,f207,f71,f43,f454])).

fof(f43,plain,
    ( spl4_3
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f220,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f210,f44])).

fof(f44,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f210,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(superposition,[],[f208,f72])).

fof(f403,plain,
    ( spl4_42
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f229,f224,f67,f39,f401])).

fof(f224,plain,
    ( spl4_28
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f229,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f227,f68])).

fof(f227,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))
    | ~ spl4_2
    | ~ spl4_28 ),
    inference(superposition,[],[f225,f40])).

fof(f225,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f224])).

fof(f357,plain,
    ( spl4_38
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f192,f181,f67,f63,f355])).

fof(f181,plain,
    ( spl4_24
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f192,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f188,f64])).

fof(f188,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(superposition,[],[f182,f68])).

fof(f182,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f181])).

fof(f322,plain,
    ( spl4_35
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f314,f311,f181,f93,f81,f320])).

fof(f81,plain,
    ( spl4_12
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f93,plain,
    ( spl4_14
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f311,plain,
    ( spl4_33
  <=> ! [X9,X11,X7,X8,X10,X12,X6] : k6_enumset1(X9,X10,X11,X12,X6,X6,X7,X8) = k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X7,X6,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f314,plain,
    ( ! [X6,X12,X10,X8,X7,X11,X9] : k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X7,X6,X8)) = k5_enumset1(X9,X10,X11,X12,X6,X7,X8)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f312,f195])).

fof(f195,plain,
    ( ! [X14,X12,X10,X15,X13,X11,X16] : k6_enumset1(X10,X11,X12,X13,X14,X14,X15,X16) = k5_enumset1(X10,X11,X12,X13,X14,X15,X16)
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f191,f82])).

fof(f82,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f191,plain,
    ( ! [X14,X12,X10,X15,X13,X11,X16] : k6_enumset1(X10,X11,X12,X13,X14,X14,X15,X16) = k2_xboole_0(k3_enumset1(X10,X11,X12,X13,X14),k2_tarski(X15,X16))
    | ~ spl4_14
    | ~ spl4_24 ),
    inference(superposition,[],[f94,f182])).

fof(f94,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f312,plain,
    ( ! [X6,X12,X10,X8,X7,X11,X9] : k6_enumset1(X9,X10,X11,X12,X6,X6,X7,X8) = k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X7,X6,X8))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f311])).

fof(f313,plain,
    ( spl4_33
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f152,f146,f55,f311])).

fof(f146,plain,
    ( spl4_22
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f152,plain,
    ( ! [X6,X12,X10,X8,X7,X11,X9] : k6_enumset1(X9,X10,X11,X12,X6,X6,X7,X8) = k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X7,X6,X8))
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(superposition,[],[f147,f56])).

fof(f147,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f146])).

fof(f226,plain,
    ( spl4_28
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f144,f137,f71,f43,f224])).

fof(f137,plain,
    ( spl4_21
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f144,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f140,f72])).

fof(f140,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(superposition,[],[f138,f44])).

fof(f138,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f137])).

fof(f209,plain,
    ( spl4_27
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f143,f137,f59,f207])).

fof(f143,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k2_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2))
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(superposition,[],[f138,f60])).

fof(f183,plain,
    ( spl4_24
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f113,f108,f71,f67,f181])).

fof(f108,plain,
    ( spl4_16
  <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f113,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f111,f68])).

fof(f111,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(superposition,[],[f109,f72])).

fof(f109,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f108])).

fof(f148,plain,
    ( spl4_22
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f97,f89,f59,f146])).

fof(f89,plain,
    ( spl4_13
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f97,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2))
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(superposition,[],[f90,f60])).

fof(f90,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f139,plain,
    ( spl4_21
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f131,f128,f124,f137])).

fof(f124,plain,
    ( spl4_18
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f128,plain,
    ( spl4_19
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f131,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f129,f125])).

fof(f125,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f124])).

fof(f129,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,
    ( spl4_19
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f96,f89,f59,f128])).

fof(f96,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(superposition,[],[f90,f60])).

fof(f126,plain,
    ( spl4_18
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f100,f93,f81,f67,f124])).

fof(f100,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f98,f82])).

fof(f98,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(superposition,[],[f94,f68])).

fof(f110,plain,
    ( spl4_16
    | ~ spl4_2
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f87,f81,f75,f39,f108])).

fof(f75,plain,
    ( spl4_11
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f87,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)
    | ~ spl4_2
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f85,f76])).

fof(f76,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f75])).

fof(f85,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(superposition,[],[f82,f40])).

fof(f95,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f32,f93])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f91,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f31,f89])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f83,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f30,f81])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(f77,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f73,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f69,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f65,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f61,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

fof(f45,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:41:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (5628)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (5619)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (5629)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (5625)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (5621)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (5614)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (5625)Refutation not found, incomplete strategy% (5625)------------------------------
% 0.22/0.48  % (5625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (5625)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (5625)Memory used [KB]: 10490
% 0.22/0.48  % (5625)Time elapsed: 0.051 s
% 0.22/0.48  % (5625)------------------------------
% 0.22/0.48  % (5625)------------------------------
% 0.22/0.48  % (5615)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (5617)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (5627)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (5622)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (5623)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (5624)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (5616)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (5618)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (5630)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (5620)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (5626)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.52  % (5619)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f2632,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f37,f41,f45,f57,f61,f65,f69,f73,f77,f83,f91,f95,f110,f126,f130,f139,f148,f183,f209,f226,f313,f322,f357,f403,f456,f582,f606,f751,f1039,f1234,f1300,f2598,f2620])).
% 0.22/0.52  fof(f2620,plain,(
% 0.22/0.52    spl4_1 | ~spl4_8 | ~spl4_127),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f2619])).
% 0.22/0.52  fof(f2619,plain,(
% 0.22/0.52    $false | (spl4_1 | ~spl4_8 | ~spl4_127)),
% 0.22/0.52    inference(subsumption_resolution,[],[f36,f2599])).
% 0.22/0.52  fof(f2599,plain,(
% 0.22/0.52    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)) ) | (~spl4_8 | ~spl4_127)),
% 0.22/0.52    inference(superposition,[],[f2597,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) ) | ~spl4_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    spl4_8 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.52  fof(f2597,plain,(
% 0.22/0.52    ( ! [X12,X10,X13,X11] : (k2_enumset1(X10,X11,X12,X13) = k3_enumset1(X10,X10,X12,X11,X13)) ) | ~spl4_127),
% 0.22/0.52    inference(avatar_component_clause,[],[f2596])).
% 0.22/0.52  fof(f2596,plain,(
% 0.22/0.52    spl4_127 <=> ! [X11,X13,X10,X12] : k2_enumset1(X10,X11,X12,X13) = k3_enumset1(X10,X10,X12,X11,X13)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_127])])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) | spl4_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.52  fof(f2598,plain,(
% 0.22/0.52    spl4_127 | ~spl4_85 | ~spl4_87),
% 0.22/0.52    inference(avatar_split_clause,[],[f1304,f1298,f1232,f2596])).
% 0.22/0.52  fof(f1232,plain,(
% 0.22/0.52    spl4_85 <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k3_enumset1(X0,X1,X3,X2,X4)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 0.22/0.52  fof(f1298,plain,(
% 0.22/0.52    spl4_87 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X1,X1,X2,X3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 0.22/0.52  fof(f1304,plain,(
% 0.22/0.52    ( ! [X12,X10,X13,X11] : (k2_enumset1(X10,X11,X12,X13) = k3_enumset1(X10,X10,X12,X11,X13)) ) | (~spl4_85 | ~spl4_87)),
% 0.22/0.52    inference(superposition,[],[f1299,f1233])).
% 0.22/0.52  fof(f1233,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X2,X3,X4) = k3_enumset1(X0,X1,X3,X2,X4)) ) | ~spl4_85),
% 0.22/0.52    inference(avatar_component_clause,[],[f1232])).
% 0.22/0.52  fof(f1299,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X1,X1,X2,X3)) ) | ~spl4_87),
% 0.22/0.52    inference(avatar_component_clause,[],[f1298])).
% 0.22/0.52  fof(f1300,plain,(
% 0.22/0.52    spl4_87 | ~spl4_38 | ~spl4_42 | ~spl4_53 | ~spl4_78),
% 0.22/0.52    inference(avatar_split_clause,[],[f1040,f1037,f580,f401,f355,f1298])).
% 0.22/0.52  fof(f355,plain,(
% 0.22/0.52    spl4_38 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.22/0.52  fof(f401,plain,(
% 0.22/0.52    spl4_42 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.22/0.52  fof(f580,plain,(
% 0.22/0.52    spl4_53 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.22/0.52  fof(f1037,plain,(
% 0.22/0.52    spl4_78 <=> ! [X1,X3,X0,X2] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k4_enumset1(X0,X0,X1,X1,X2,X3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 0.22/0.52  fof(f1040,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X1,X1,X2,X3)) ) | (~spl4_38 | ~spl4_42 | ~spl4_53 | ~spl4_78)),
% 0.22/0.52    inference(forward_demodulation,[],[f1038,f718])).
% 0.22/0.52  fof(f718,plain,(
% 0.22/0.52    ( ! [X61,X59,X62,X60] : (k2_xboole_0(k1_tarski(X62),k1_enumset1(X59,X60,X61)) = k2_enumset1(X62,X59,X60,X61)) ) | (~spl4_38 | ~spl4_42 | ~spl4_53)),
% 0.22/0.52    inference(forward_demodulation,[],[f703,f356])).
% 0.22/0.52  fof(f356,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) ) | ~spl4_38),
% 0.22/0.52    inference(avatar_component_clause,[],[f355])).
% 0.22/0.52  fof(f703,plain,(
% 0.22/0.52    ( ! [X61,X59,X62,X60] : (k3_enumset1(X62,X59,X60,X61,X61) = k2_xboole_0(k1_tarski(X62),k1_enumset1(X59,X60,X61))) ) | (~spl4_42 | ~spl4_53)),
% 0.22/0.52    inference(superposition,[],[f402,f581])).
% 0.22/0.52  fof(f581,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) ) | ~spl4_53),
% 0.22/0.52    inference(avatar_component_clause,[],[f580])).
% 0.22/0.52  fof(f402,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) ) | ~spl4_42),
% 0.22/0.52    inference(avatar_component_clause,[],[f401])).
% 0.22/0.52  fof(f1038,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k4_enumset1(X0,X0,X1,X1,X2,X3)) ) | ~spl4_78),
% 0.22/0.52    inference(avatar_component_clause,[],[f1037])).
% 0.22/0.52  fof(f1234,plain,(
% 0.22/0.52    spl4_85 | ~spl4_9 | ~spl4_10 | ~spl4_60),
% 0.22/0.52    inference(avatar_split_clause,[],[f770,f749,f71,f67,f1232])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    spl4_9 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    spl4_10 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.52  fof(f749,plain,(
% 0.22/0.52    spl4_60 <=> ! [X9,X5,X7,X8,X10,X6] : k5_enumset1(X5,X6,X7,X8,X8,X9,X10) = k4_enumset1(X6,X5,X7,X9,X8,X10)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 0.22/0.52  fof(f770,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X2,X3,X4) = k3_enumset1(X0,X1,X3,X2,X4)) ) | (~spl4_9 | ~spl4_10 | ~spl4_60)),
% 0.22/0.52    inference(forward_demodulation,[],[f752,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) ) | ~spl4_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f67])).
% 0.22/0.52  fof(f752,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X2,X3,X4) = k4_enumset1(X0,X0,X1,X3,X2,X4)) ) | (~spl4_10 | ~spl4_60)),
% 0.22/0.52    inference(superposition,[],[f750,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ) | ~spl4_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f71])).
% 0.22/0.52  fof(f750,plain,(
% 0.22/0.52    ( ! [X6,X10,X8,X7,X5,X9] : (k5_enumset1(X5,X6,X7,X8,X8,X9,X10) = k4_enumset1(X6,X5,X7,X9,X8,X10)) ) | ~spl4_60),
% 0.22/0.52    inference(avatar_component_clause,[],[f749])).
% 0.22/0.52  fof(f1039,plain,(
% 0.22/0.52    spl4_78 | ~spl4_2 | ~spl4_47),
% 0.22/0.52    inference(avatar_split_clause,[],[f459,f454,f39,f1037])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    spl4_2 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.52  fof(f454,plain,(
% 0.22/0.52    spl4_47 <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.22/0.52  fof(f459,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k4_enumset1(X0,X0,X1,X1,X2,X3)) ) | (~spl4_2 | ~spl4_47)),
% 0.22/0.52    inference(superposition,[],[f455,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl4_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f39])).
% 0.22/0.52  fof(f455,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) ) | ~spl4_47),
% 0.22/0.52    inference(avatar_component_clause,[],[f454])).
% 0.22/0.52  fof(f751,plain,(
% 0.22/0.52    spl4_60 | ~spl4_7 | ~spl4_10 | ~spl4_35 | ~spl4_54),
% 0.22/0.52    inference(avatar_split_clause,[],[f607,f604,f320,f71,f59,f749])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    spl4_7 <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.52  fof(f320,plain,(
% 0.22/0.52    spl4_35 <=> ! [X9,X11,X7,X8,X10,X12,X6] : k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X7,X6,X8)) = k5_enumset1(X9,X10,X11,X12,X6,X7,X8)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.22/0.52  fof(f604,plain,(
% 0.22/0.52    spl4_54 <=> ! [X9,X5,X7,X8,X10,X6] : k5_enumset1(X5,X6,X7,X8,X8,X9,X10) = k2_xboole_0(k1_enumset1(X6,X5,X7),k1_enumset1(X8,X9,X10))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.22/0.52  fof(f607,plain,(
% 0.22/0.52    ( ! [X6,X10,X8,X7,X5,X9] : (k5_enumset1(X5,X6,X7,X8,X8,X9,X10) = k4_enumset1(X6,X5,X7,X9,X8,X10)) ) | (~spl4_7 | ~spl4_10 | ~spl4_35 | ~spl4_54)),
% 0.22/0.52    inference(forward_demodulation,[],[f605,f329])).
% 0.22/0.52  fof(f329,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X4,X3,X5)) ) | (~spl4_7 | ~spl4_10 | ~spl4_35)),
% 0.22/0.52    inference(forward_demodulation,[],[f323,f72])).
% 0.22/0.52  fof(f323,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k5_enumset1(X0,X0,X1,X2,X4,X3,X5)) ) | (~spl4_7 | ~spl4_35)),
% 0.22/0.52    inference(superposition,[],[f321,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) ) | ~spl4_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f59])).
% 0.22/0.52  fof(f321,plain,(
% 0.22/0.52    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X7,X6,X8)) = k5_enumset1(X9,X10,X11,X12,X6,X7,X8)) ) | ~spl4_35),
% 0.22/0.52    inference(avatar_component_clause,[],[f320])).
% 0.22/0.52  fof(f605,plain,(
% 0.22/0.52    ( ! [X6,X10,X8,X7,X5,X9] : (k5_enumset1(X5,X6,X7,X8,X8,X9,X10) = k2_xboole_0(k1_enumset1(X6,X5,X7),k1_enumset1(X8,X9,X10))) ) | ~spl4_54),
% 0.22/0.52    inference(avatar_component_clause,[],[f604])).
% 0.22/0.52  fof(f606,plain,(
% 0.22/0.52    spl4_54 | ~spl4_6 | ~spl4_27),
% 0.22/0.52    inference(avatar_split_clause,[],[f213,f207,f55,f604])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    spl4_6 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.52  fof(f207,plain,(
% 0.22/0.52    spl4_27 <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k2_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    ( ! [X6,X10,X8,X7,X5,X9] : (k5_enumset1(X5,X6,X7,X8,X8,X9,X10) = k2_xboole_0(k1_enumset1(X6,X5,X7),k1_enumset1(X8,X9,X10))) ) | (~spl4_6 | ~spl4_27)),
% 0.22/0.52    inference(superposition,[],[f208,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) ) | ~spl4_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f55])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k2_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2))) ) | ~spl4_27),
% 0.22/0.52    inference(avatar_component_clause,[],[f207])).
% 0.22/0.52  fof(f582,plain,(
% 0.22/0.52    spl4_53 | ~spl4_7 | ~spl4_8 | ~spl4_38),
% 0.22/0.52    inference(avatar_split_clause,[],[f362,f355,f63,f59,f580])).
% 0.22/0.52  fof(f362,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) ) | (~spl4_7 | ~spl4_8 | ~spl4_38)),
% 0.22/0.52    inference(forward_demodulation,[],[f358,f60])).
% 0.22/0.52  fof(f358,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) ) | (~spl4_8 | ~spl4_38)),
% 0.22/0.52    inference(superposition,[],[f356,f64])).
% 0.22/0.52  fof(f456,plain,(
% 0.22/0.52    spl4_47 | ~spl4_3 | ~spl4_10 | ~spl4_27),
% 0.22/0.52    inference(avatar_split_clause,[],[f220,f207,f71,f43,f454])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    spl4_3 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) ) | (~spl4_3 | ~spl4_10 | ~spl4_27)),
% 0.22/0.52    inference(forward_demodulation,[],[f210,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) ) | ~spl4_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f43])).
% 0.22/0.52  fof(f210,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) ) | (~spl4_10 | ~spl4_27)),
% 0.22/0.52    inference(superposition,[],[f208,f72])).
% 0.22/0.52  fof(f403,plain,(
% 0.22/0.52    spl4_42 | ~spl4_2 | ~spl4_9 | ~spl4_28),
% 0.22/0.52    inference(avatar_split_clause,[],[f229,f224,f67,f39,f401])).
% 0.22/0.52  fof(f224,plain,(
% 0.22/0.52    spl4_28 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.52  fof(f229,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) ) | (~spl4_2 | ~spl4_9 | ~spl4_28)),
% 0.22/0.52    inference(forward_demodulation,[],[f227,f68])).
% 0.22/0.52  fof(f227,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) ) | (~spl4_2 | ~spl4_28)),
% 0.22/0.52    inference(superposition,[],[f225,f40])).
% 0.22/0.52  fof(f225,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) ) | ~spl4_28),
% 0.22/0.52    inference(avatar_component_clause,[],[f224])).
% 0.22/0.52  fof(f357,plain,(
% 0.22/0.52    spl4_38 | ~spl4_8 | ~spl4_9 | ~spl4_24),
% 0.22/0.52    inference(avatar_split_clause,[],[f192,f181,f67,f63,f355])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    spl4_24 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) ) | (~spl4_8 | ~spl4_9 | ~spl4_24)),
% 0.22/0.52    inference(forward_demodulation,[],[f188,f64])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) ) | (~spl4_9 | ~spl4_24)),
% 0.22/0.52    inference(superposition,[],[f182,f68])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) ) | ~spl4_24),
% 0.22/0.52    inference(avatar_component_clause,[],[f181])).
% 0.22/0.52  fof(f322,plain,(
% 0.22/0.52    spl4_35 | ~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_33),
% 0.22/0.52    inference(avatar_split_clause,[],[f314,f311,f181,f93,f81,f320])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl4_12 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    spl4_14 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.52  fof(f311,plain,(
% 0.22/0.52    spl4_33 <=> ! [X9,X11,X7,X8,X10,X12,X6] : k6_enumset1(X9,X10,X11,X12,X6,X6,X7,X8) = k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X7,X6,X8))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.22/0.52  fof(f314,plain,(
% 0.22/0.52    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X7,X6,X8)) = k5_enumset1(X9,X10,X11,X12,X6,X7,X8)) ) | (~spl4_12 | ~spl4_14 | ~spl4_24 | ~spl4_33)),
% 0.22/0.52    inference(forward_demodulation,[],[f312,f195])).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    ( ! [X14,X12,X10,X15,X13,X11,X16] : (k6_enumset1(X10,X11,X12,X13,X14,X14,X15,X16) = k5_enumset1(X10,X11,X12,X13,X14,X15,X16)) ) | (~spl4_12 | ~spl4_14 | ~spl4_24)),
% 0.22/0.52    inference(forward_demodulation,[],[f191,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) ) | ~spl4_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f81])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    ( ! [X14,X12,X10,X15,X13,X11,X16] : (k6_enumset1(X10,X11,X12,X13,X14,X14,X15,X16) = k2_xboole_0(k3_enumset1(X10,X11,X12,X13,X14),k2_tarski(X15,X16))) ) | (~spl4_14 | ~spl4_24)),
% 0.22/0.52    inference(superposition,[],[f94,f182])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) ) | ~spl4_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f93])).
% 0.22/0.52  fof(f312,plain,(
% 0.22/0.52    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k6_enumset1(X9,X10,X11,X12,X6,X6,X7,X8) = k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X7,X6,X8))) ) | ~spl4_33),
% 0.22/0.52    inference(avatar_component_clause,[],[f311])).
% 0.22/0.52  fof(f313,plain,(
% 0.22/0.52    spl4_33 | ~spl4_6 | ~spl4_22),
% 0.22/0.52    inference(avatar_split_clause,[],[f152,f146,f55,f311])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    spl4_22 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k6_enumset1(X9,X10,X11,X12,X6,X6,X7,X8) = k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_enumset1(X7,X6,X8))) ) | (~spl4_6 | ~spl4_22)),
% 0.22/0.52    inference(superposition,[],[f147,f56])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2))) ) | ~spl4_22),
% 0.22/0.52    inference(avatar_component_clause,[],[f146])).
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    spl4_28 | ~spl4_3 | ~spl4_10 | ~spl4_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f144,f137,f71,f43,f224])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    spl4_21 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) ) | (~spl4_3 | ~spl4_10 | ~spl4_21)),
% 0.22/0.52    inference(forward_demodulation,[],[f140,f72])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) ) | (~spl4_3 | ~spl4_21)),
% 0.22/0.52    inference(superposition,[],[f138,f44])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) ) | ~spl4_21),
% 0.22/0.52    inference(avatar_component_clause,[],[f137])).
% 0.22/0.52  fof(f209,plain,(
% 0.22/0.52    spl4_27 | ~spl4_7 | ~spl4_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f143,f137,f59,f207])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k2_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2))) ) | (~spl4_7 | ~spl4_21)),
% 0.22/0.52    inference(superposition,[],[f138,f60])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    spl4_24 | ~spl4_9 | ~spl4_10 | ~spl4_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f113,f108,f71,f67,f181])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    spl4_16 <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) ) | (~spl4_9 | ~spl4_10 | ~spl4_16)),
% 0.22/0.52    inference(forward_demodulation,[],[f111,f68])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) ) | (~spl4_10 | ~spl4_16)),
% 0.22/0.52    inference(superposition,[],[f109,f72])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)) ) | ~spl4_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f108])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    spl4_22 | ~spl4_7 | ~spl4_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f97,f89,f59,f146])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    spl4_13 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2))) ) | (~spl4_7 | ~spl4_13)),
% 0.22/0.52    inference(superposition,[],[f90,f60])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) ) | ~spl4_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f89])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    spl4_21 | ~spl4_18 | ~spl4_19),
% 0.22/0.52    inference(avatar_split_clause,[],[f131,f128,f124,f137])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    spl4_18 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    spl4_19 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) ) | (~spl4_18 | ~spl4_19)),
% 0.22/0.53    inference(forward_demodulation,[],[f129,f125])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ) | ~spl4_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f124])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) ) | ~spl4_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f128])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    spl4_19 | ~spl4_7 | ~spl4_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f96,f89,f59,f128])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) ) | (~spl4_7 | ~spl4_13)),
% 0.22/0.53    inference(superposition,[],[f90,f60])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    spl4_18 | ~spl4_9 | ~spl4_12 | ~spl4_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f100,f93,f81,f67,f124])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ) | (~spl4_9 | ~spl4_12 | ~spl4_14)),
% 0.22/0.53    inference(forward_demodulation,[],[f98,f82])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ) | (~spl4_9 | ~spl4_14)),
% 0.22/0.53    inference(superposition,[],[f94,f68])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl4_16 | ~spl4_2 | ~spl4_11 | ~spl4_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f87,f81,f75,f39,f108])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl4_11 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)) ) | (~spl4_2 | ~spl4_11 | ~spl4_12)),
% 0.22/0.53    inference(forward_demodulation,[],[f85,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) ) | ~spl4_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f75])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) ) | (~spl4_2 | ~spl4_12)),
% 0.22/0.53    inference(superposition,[],[f82,f40])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl4_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f32,f93])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl4_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f89])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    spl4_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f81])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl4_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f75])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    spl4_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f28,f71])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    spl4_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f67])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl4_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f26,f63])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f25,f59])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f24,f55])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f21,f43])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f20,f39])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ~spl4_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f19,f34])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.22/0.53    inference(negated_conjecture,[],[f14])).
% 0.22/0.53  fof(f14,conjecture,(
% 0.22/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (5619)------------------------------
% 0.22/0.53  % (5619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5619)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (5619)Memory used [KB]: 8059
% 0.22/0.53  % (5619)Time elapsed: 0.092 s
% 0.22/0.53  % (5619)------------------------------
% 0.22/0.53  % (5619)------------------------------
% 0.22/0.53  % (5611)Success in time 0.166 s
%------------------------------------------------------------------------------
