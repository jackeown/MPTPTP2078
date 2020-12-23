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
% DateTime   : Thu Dec  3 12:52:33 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  276 ( 573 expanded)
%              Number of leaves         :   65 ( 277 expanded)
%              Depth                    :   10
%              Number of atoms          :  833 (1551 expanded)
%              Number of equality atoms :  157 ( 340 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f93,f97,f103,f109,f127,f131,f139,f147,f152,f156,f165,f174,f181,f187,f191,f205,f215,f229,f239,f243,f247,f256,f270,f290,f294,f319,f333,f362,f396,f577,f601,f605,f609,f946,f962,f980,f1101,f1860,f1990,f2128,f2917,f3770,f3939])).

fof(f3939,plain,
    ( ~ spl2_8
    | spl2_16
    | ~ spl2_20
    | ~ spl2_34
    | ~ spl2_38
    | ~ spl2_43
    | ~ spl2_71
    | ~ spl2_76
    | ~ spl2_88
    | ~ spl2_147 ),
    inference(avatar_contradiction_clause,[],[f3936])).

fof(f3936,plain,
    ( $false
    | ~ spl2_8
    | spl2_16
    | ~ spl2_20
    | ~ spl2_34
    | ~ spl2_38
    | ~ spl2_43
    | ~ spl2_71
    | ~ spl2_76
    | ~ spl2_88
    | ~ spl2_147 ),
    inference(subsumption_resolution,[],[f151,f3935])).

fof(f3935,plain,
    ( ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4)))
    | ~ spl2_8
    | ~ spl2_20
    | ~ spl2_34
    | ~ spl2_38
    | ~ spl2_43
    | ~ spl2_71
    | ~ spl2_76
    | ~ spl2_88
    | ~ spl2_147 ),
    inference(backward_demodulation,[],[f1948,f3818])).

fof(f3818,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X3)
    | ~ spl2_20
    | ~ spl2_71
    | ~ spl2_76
    | ~ spl2_147 ),
    inference(backward_demodulation,[],[f979,f3801])).

fof(f3801,plain,
    ( ! [X10,X9] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X9),X10))) = k7_relat_1(k6_relat_1(X10),X9)
    | ~ spl2_20
    | ~ spl2_76
    | ~ spl2_147 ),
    inference(forward_demodulation,[],[f3775,f1100])).

fof(f1100,plain,
    ( ! [X14,X13] : k7_relat_1(k6_relat_1(X14),X13) = k7_relat_1(k6_relat_1(X14),k2_relat_1(k7_relat_1(k6_relat_1(X13),X14)))
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f1099])).

fof(f1099,plain,
    ( spl2_76
  <=> ! [X13,X14] : k7_relat_1(k6_relat_1(X14),X13) = k7_relat_1(k6_relat_1(X14),k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f3775,plain,
    ( ! [X10,X9] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X9),X10))) = k7_relat_1(k6_relat_1(X10),k2_relat_1(k7_relat_1(k6_relat_1(X9),X10)))
    | ~ spl2_20
    | ~ spl2_147 ),
    inference(resolution,[],[f3769,f180])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f3769,plain,
    ( ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0)
    | ~ spl2_147 ),
    inference(avatar_component_clause,[],[f3768])).

fof(f3768,plain,
    ( spl2_147
  <=> ! [X1,X0] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_147])])).

fof(f979,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f978])).

fof(f978,plain,
    ( spl2_71
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f1948,plain,
    ( ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X4)
    | ~ spl2_8
    | ~ spl2_34
    | ~ spl2_38
    | ~ spl2_43
    | ~ spl2_88 ),
    inference(forward_demodulation,[],[f1945,f293])).

fof(f293,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl2_34
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f1945,plain,
    ( ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X3),X4)
    | ~ spl2_8
    | ~ spl2_38
    | ~ spl2_43
    | ~ spl2_88 ),
    inference(backward_demodulation,[],[f1873,f1944])).

fof(f1944,plain,
    ( ! [X23,X21,X22] : k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X22,X22,X22,X23))),X21) = k7_relat_1(k7_relat_1(k6_relat_1(X23),X22),X21)
    | ~ spl2_38
    | ~ spl2_43
    | ~ spl2_88 ),
    inference(forward_demodulation,[],[f1884,f361])).

fof(f361,plain,
    ( ! [X6,X7,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl2_43
  <=> ! [X5,X7,X6] : k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f1884,plain,
    ( ! [X23,X21,X22] : k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X22,X22,X22,X23))),X21) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X21),X22),X23))
    | ~ spl2_38
    | ~ spl2_88 ),
    inference(superposition,[],[f332,f1859])).

fof(f1859,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ spl2_88 ),
    inference(avatar_component_clause,[],[f1858])).

fof(f1858,plain,
    ( spl2_88
  <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f332,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl2_38
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f1873,plain,
    ( ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3),X4)
    | ~ spl2_8
    | ~ spl2_88 ),
    inference(superposition,[],[f1859,f102])).

fof(f102,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_8
  <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f151,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl2_16
  <=> k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f3770,plain,
    ( spl2_147
    | ~ spl2_57
    | ~ spl2_136 ),
    inference(avatar_split_clause,[],[f3755,f2915,f607,f3768])).

fof(f607,plain,
    ( spl2_57
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f2915,plain,
    ( spl2_136
  <=> ! [X36,X38,X37,X39] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X36),X37))),X38),X39)),X36) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).

fof(f3755,plain,
    ( ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0)
    | ~ spl2_57
    | ~ spl2_136 ),
    inference(superposition,[],[f2916,f608])).

fof(f608,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0)
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f607])).

fof(f2916,plain,
    ( ! [X39,X37,X38,X36] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X36),X37))),X38),X39)),X36)
    | ~ spl2_136 ),
    inference(avatar_component_clause,[],[f2915])).

fof(f2917,plain,
    ( spl2_136
    | ~ spl2_55
    | ~ spl2_100 ),
    inference(avatar_split_clause,[],[f2342,f2126,f599,f2915])).

fof(f599,plain,
    ( spl2_55
  <=> ! [X5,X4] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(X4),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f2126,plain,
    ( spl2_100
  <=> ! [X11,X13,X12,X14] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X11),X12),X13),X14)),X11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).

fof(f2342,plain,
    ( ! [X39,X37,X38,X36] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X36),X37))),X38),X39)),X36)
    | ~ spl2_55
    | ~ spl2_100 ),
    inference(superposition,[],[f2127,f600])).

fof(f600,plain,
    ( ! [X4,X5] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(X4),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f599])).

fof(f2127,plain,
    ( ! [X14,X12,X13,X11] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X11),X12),X13),X14)),X11)
    | ~ spl2_100 ),
    inference(avatar_component_clause,[],[f2126])).

fof(f2128,plain,
    ( spl2_100
    | ~ spl2_88
    | ~ spl2_90 ),
    inference(avatar_split_clause,[],[f2018,f1988,f1858,f2126])).

fof(f1988,plain,
    ( spl2_90
  <=> ! [X13,X12,X14] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X14)),X12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).

fof(f2018,plain,
    ( ! [X14,X12,X13,X11] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X11),X12),X13),X14)),X11)
    | ~ spl2_88
    | ~ spl2_90 ),
    inference(superposition,[],[f1989,f1859])).

fof(f1989,plain,
    ( ! [X14,X12,X13] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X14)),X12)
    | ~ spl2_90 ),
    inference(avatar_component_clause,[],[f1988])).

fof(f1990,plain,
    ( spl2_90
    | ~ spl2_31
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f1881,f1858,f268,f1988])).

fof(f268,plain,
    ( spl2_31
  <=> ! [X1,X0] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f1881,plain,
    ( ! [X14,X12,X13] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X14)),X12)
    | ~ spl2_31
    | ~ spl2_88 ),
    inference(superposition,[],[f269,f1859])).

fof(f269,plain,
    ( ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f268])).

fof(f1860,plain,
    ( spl2_88
    | ~ spl2_1
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f578,f394,f71,f1858])).

fof(f71,plain,
    ( spl2_1
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f394,plain,
    ( spl2_45
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f578,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ spl2_1
    | ~ spl2_45 ),
    inference(resolution,[],[f395,f72])).

fof(f72,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f395,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f394])).

fof(f1101,plain,
    ( spl2_76
    | ~ spl2_38
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f1029,f978,f331,f1099])).

fof(f1029,plain,
    ( ! [X14,X13] : k7_relat_1(k6_relat_1(X14),X13) = k7_relat_1(k6_relat_1(X14),k2_relat_1(k7_relat_1(k6_relat_1(X13),X14)))
    | ~ spl2_38
    | ~ spl2_71 ),
    inference(forward_demodulation,[],[f993,f332])).

fof(f993,plain,
    ( ! [X14,X13] : k7_relat_1(k6_relat_1(X14),k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))) = k4_relat_1(k7_relat_1(k6_relat_1(X13),X14))
    | ~ spl2_38
    | ~ spl2_71 ),
    inference(superposition,[],[f332,f979])).

fof(f980,plain,
    ( spl2_71
    | ~ spl2_29
    | ~ spl2_66
    | ~ spl2_70 ),
    inference(avatar_split_clause,[],[f975,f960,f944,f245,f978])).

fof(f245,plain,
    ( spl2_29
  <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f944,plain,
    ( spl2_66
  <=> ! [X3,X4] : k7_relat_1(k6_relat_1(X3),X4) = k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f960,plain,
    ( spl2_70
  <=> ! [X13,X14] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))),X13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f975,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)
    | ~ spl2_29
    | ~ spl2_66
    | ~ spl2_70 ),
    inference(forward_demodulation,[],[f968,f961])).

fof(f961,plain,
    ( ! [X14,X13] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))),X13)
    | ~ spl2_70 ),
    inference(avatar_component_clause,[],[f960])).

fof(f968,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3)
    | ~ spl2_29
    | ~ spl2_66 ),
    inference(superposition,[],[f945,f246])).

fof(f246,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f245])).

fof(f945,plain,
    ( ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f944])).

fof(f962,plain,
    ( spl2_70
    | ~ spl2_4
    | ~ spl2_38
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f772,f603,f331,f83,f960])).

fof(f83,plain,
    ( spl2_4
  <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f603,plain,
    ( spl2_56
  <=> ! [X7,X6] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))) = k7_relat_1(k6_relat_1(X6),k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f772,plain,
    ( ! [X14,X13] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))),X13)
    | ~ spl2_4
    | ~ spl2_38
    | ~ spl2_56 ),
    inference(forward_demodulation,[],[f742,f84])).

fof(f84,plain,
    ( ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f742,plain,
    ( ! [X14,X13] : k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))),X13) = k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))))
    | ~ spl2_38
    | ~ spl2_56 ),
    inference(superposition,[],[f332,f604])).

fof(f604,plain,
    ( ! [X6,X7] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))) = k7_relat_1(k6_relat_1(X6),k2_relat_1(k7_relat_1(k6_relat_1(X6),X7)))
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f603])).

fof(f946,plain,
    ( spl2_66
    | ~ spl2_18
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f218,f213,f163,f944])).

fof(f163,plain,
    ( spl2_18
  <=> ! [X1,X2] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f213,plain,
    ( spl2_24
  <=> ! [X0] :
        ( k8_relat_1(k2_relat_1(X0),X0) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f218,plain,
    ( ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))
    | ~ spl2_18
    | ~ spl2_24 ),
    inference(resolution,[],[f214,f164])).

fof(f164,plain,
    ( ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f163])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k8_relat_1(k2_relat_1(X0),X0) = X0 )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f609,plain,
    ( spl2_57
    | ~ spl2_38
    | ~ spl2_43
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f597,f575,f360,f331,f607])).

fof(f575,plain,
    ( spl2_54
  <=> ! [X9,X8] : k7_relat_1(k6_relat_1(X8),X9) = k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),k1_relat_1(k7_relat_1(k6_relat_1(X8),X9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f597,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0)
    | ~ spl2_38
    | ~ spl2_43
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f585,f332])).

fof(f585,plain,
    ( ! [X0,X1] : k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0)
    | ~ spl2_43
    | ~ spl2_54 ),
    inference(superposition,[],[f361,f576])).

fof(f576,plain,
    ( ! [X8,X9] : k7_relat_1(k6_relat_1(X8),X9) = k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),k1_relat_1(k7_relat_1(k6_relat_1(X8),X9)))
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f575])).

fof(f605,plain,
    ( spl2_56
    | ~ spl2_20
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f274,f268,f179,f603])).

fof(f274,plain,
    ( ! [X6,X7] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))) = k7_relat_1(k6_relat_1(X6),k2_relat_1(k7_relat_1(k6_relat_1(X6),X7)))
    | ~ spl2_20
    | ~ spl2_31 ),
    inference(resolution,[],[f269,f180])).

fof(f601,plain,
    ( spl2_55
    | ~ spl2_20
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f259,f254,f179,f599])).

fof(f254,plain,
    ( spl2_30
  <=> ! [X1,X0] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f259,plain,
    ( ! [X4,X5] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(X4),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))
    | ~ spl2_20
    | ~ spl2_30 ),
    inference(resolution,[],[f255,f180])).

fof(f255,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f254])).

fof(f577,plain,
    ( spl2_54
    | ~ spl2_6
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f169,f163,f91,f575])).

fof(f91,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f169,plain,
    ( ! [X8,X9] : k7_relat_1(k6_relat_1(X8),X9) = k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),k1_relat_1(k7_relat_1(k6_relat_1(X8),X9)))
    | ~ spl2_6
    | ~ spl2_18 ),
    inference(resolution,[],[f164,f92])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,k1_relat_1(X0)) = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f396,plain,(
    spl2_45 ),
    inference(avatar_split_clause,[],[f69,f394])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f362,plain,
    ( spl2_43
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_26
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f329,f317,f227,f163,f154,f145,f129,f125,f83,f71,f360])).

fof(f125,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f129,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f145,plain,
    ( spl2_15
  <=> ! [X1,X0] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f154,plain,
    ( spl2_17
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f227,plain,
    ( spl2_26
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f317,plain,
    ( spl2_37
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f329,plain,
    ( ! [X6,X7,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_26
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f328,f166])).

fof(f166,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_13
    | ~ spl2_18 ),
    inference(resolution,[],[f164,f130])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f328,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_26
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f327,f234])).

fof(f234,plain,
    ( ! [X4,X5,X3] : k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)
    | ~ spl2_1
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_18
    | ~ spl2_26 ),
    inference(backward_demodulation,[],[f167,f233])).

fof(f233,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2))
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f230,f146])).

fof(f146,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f230,plain,
    ( ! [X2,X0,X1] : k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2)
    | ~ spl2_1
    | ~ spl2_26 ),
    inference(resolution,[],[f228,f72])).

fof(f228,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f227])).

fof(f167,plain,
    ( ! [X4,X5,X3] : k8_relat_1(X3,k7_relat_1(k6_relat_1(X4),X5)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3))
    | ~ spl2_12
    | ~ spl2_18 ),
    inference(resolution,[],[f164,f126])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f327,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f322,f325])).

fof(f325,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f324,f155])).

fof(f155,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f324,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f323,f155])).

fof(f323,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f320,f84])).

fof(f320,plain,
    ( ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))
    | ~ spl2_1
    | ~ spl2_37 ),
    inference(resolution,[],[f318,f72])).

fof(f318,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f317])).

fof(f322,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5))
    | ~ spl2_18
    | ~ spl2_37 ),
    inference(resolution,[],[f318,f164])).

fof(f333,plain,
    ( spl2_38
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f325,f317,f154,f83,f71,f331])).

fof(f319,plain,
    ( spl2_37
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f315,f288,f83,f71,f317])).

fof(f288,plain,
    ( spl2_33
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f315,plain,
    ( ! [X0,X1] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f312,f84])).

fof(f312,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1))) )
    | ~ spl2_1
    | ~ spl2_33 ),
    inference(resolution,[],[f289,f72])).

fof(f289,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f288])).

fof(f294,plain,
    ( spl2_34
    | ~ spl2_8
    | ~ spl2_15
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f286,f245,f145,f101,f292])).

fof(f286,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)
    | ~ spl2_8
    | ~ spl2_15
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f283,f146])).

fof(f283,plain,
    ( ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)
    | ~ spl2_8
    | ~ spl2_29 ),
    inference(superposition,[],[f246,f102])).

fof(f290,plain,(
    spl2_33 ),
    inference(avatar_split_clause,[],[f51,f288])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f270,plain,
    ( spl2_31
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_18
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f266,f241,f163,f79,f71,f268])).

fof(f79,plain,
    ( spl2_3
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f241,plain,
    ( spl2_28
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f266,plain,
    ( ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_18
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f265,f80])).

fof(f80,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f265,plain,
    ( ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k2_relat_1(k6_relat_1(X0)))
    | ~ spl2_1
    | ~ spl2_18
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f262,f72])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k6_relat_1(X0))
        | r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k2_relat_1(k6_relat_1(X0))) )
    | ~ spl2_18
    | ~ spl2_28 ),
    inference(resolution,[],[f242,f164])).

fof(f242,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0)
        | r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f241])).

fof(f256,plain,
    ( spl2_30
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_18
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f252,f237,f163,f75,f71,f254])).

fof(f75,plain,
    ( spl2_2
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f237,plain,
    ( spl2_27
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f252,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_18
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f251,f76])).

fof(f76,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f251,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0)))
    | ~ spl2_1
    | ~ spl2_18
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f248,f72])).

fof(f248,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k6_relat_1(X0))
        | r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0))) )
    | ~ spl2_18
    | ~ spl2_27 ),
    inference(resolution,[],[f238,f164])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0)
        | r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f237])).

fof(f247,plain,
    ( spl2_29
    | ~ spl2_1
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f233,f227,f145,f71,f245])).

fof(f243,plain,
    ( spl2_28
    | ~ spl2_5
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f201,f189,f87,f241])).

fof(f87,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f189,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1)) )
    | ~ spl2_5
    | ~ spl2_22 ),
    inference(duplicate_literal_removal,[],[f198])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5
    | ~ spl2_22 ),
    inference(resolution,[],[f190,f88])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f189])).

fof(f239,plain,
    ( spl2_27
    | ~ spl2_5
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f195,f185,f87,f237])).

fof(f185,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1)) )
    | ~ spl2_5
    | ~ spl2_21 ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5
    | ~ spl2_21 ),
    inference(resolution,[],[f186,f88])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f185])).

fof(f229,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f63,f227])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f215,plain,
    ( spl2_24
    | ~ spl2_19
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f206,f203,f172,f213])).

fof(f172,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f203,plain,
    ( spl2_23
  <=> ! [X2] : r1_tarski(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f206,plain,
    ( ! [X0] :
        ( k8_relat_1(k2_relat_1(X0),X0) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_19
    | ~ spl2_23 ),
    inference(resolution,[],[f204,f173])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f172])).

fof(f204,plain,
    ( ! [X2] : r1_tarski(X2,X2)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f203])).

fof(f205,plain,
    ( spl2_23
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f197,f185,f107,f75,f71,f203])).

fof(f107,plain,
    ( spl2_9
  <=> ! [X0] : r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f197,plain,
    ( ! [X2] : r1_tarski(X2,X2)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f196,f76])).

fof(f196,plain,
    ( ! [X2] : r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(k6_relat_1(X2)))
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_21 ),
    inference(subsumption_resolution,[],[f194,f72])).

fof(f194,plain,
    ( ! [X2] :
        ( r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(k6_relat_1(X2)))
        | ~ v1_relat_1(k6_relat_1(X2)) )
    | ~ spl2_9
    | ~ spl2_21 ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( ! [X2] :
        ( r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(k6_relat_1(X2)))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X2)) )
    | ~ spl2_9
    | ~ spl2_21 ),
    inference(resolution,[],[f186,f108])).

fof(f108,plain,
    ( ! [X0] : r1_tarski(k6_relat_1(X0),k6_relat_1(X0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f191,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f53,f189])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f187,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f52,f185])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f181,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f177,f172,f145,f79,f71,f179])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f176,f146])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f175,f72])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(superposition,[],[f173,f80])).

fof(f174,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f60,f172])).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f165,plain,
    ( spl2_18
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f161,f154,f95,f71,f163])).

fof(f95,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f161,plain,
    ( ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f160,f72])).

fof(f160,plain,
    ( ! [X2,X1] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f159,f72])).

fof(f159,plain,
    ( ! [X2,X1] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_7
    | ~ spl2_17 ),
    inference(superposition,[],[f96,f155])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f156,plain,
    ( spl2_17
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f140,f129,f71,f154])).

fof(f140,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(resolution,[],[f130,f72])).

fof(f152,plain,
    ( ~ spl2_16
    | ~ spl2_1
    | ~ spl2_12
    | ~ spl2_13
    | spl2_14 ),
    inference(avatar_split_clause,[],[f143,f136,f129,f125,f71,f149])).

fof(f136,plain,
    ( spl2_14
  <=> k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k8_relat_1(sK0,k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f143,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_12
    | ~ spl2_13
    | spl2_14 ),
    inference(backward_demodulation,[],[f138,f142])).

fof(f142,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(backward_demodulation,[],[f132,f140])).

fof(f132,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(resolution,[],[f126,f72])).

fof(f138,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f147,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f142,f129,f125,f71,f145])).

fof(f139,plain,
    ( ~ spl2_14
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f134,f125,f71,f136])).

fof(f134,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(backward_demodulation,[],[f68,f132])).

fof(f68,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f44,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f42])).

fof(f42,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f131,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f59,f129])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f127,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f58,f125])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f109,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f105,f101,f87,f71,f107])).

fof(f105,plain,
    ( ! [X0] : r1_tarski(k6_relat_1(X0),k6_relat_1(X0))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f104,f72])).

fof(f104,plain,
    ( ! [X0] :
        ( r1_tarski(k6_relat_1(X0),k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(superposition,[],[f88,f102])).

fof(f103,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f99,f91,f75,f71,f101])).

fof(f99,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f98,f76])).

fof(f98,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(resolution,[],[f92,f72])).

fof(f97,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f61,f95])).

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f93,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f49,f91])).

fof(f49,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f89,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f57,f87])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f85,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f45,f83])).

fof(f45,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f81,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f48,f79])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f77,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f47,f75])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f46,f71])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (11147)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (11155)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (11155)Refutation not found, incomplete strategy% (11155)------------------------------
% 0.20/0.47  % (11155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (11155)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (11155)Memory used [KB]: 10618
% 0.20/0.47  % (11155)Time elapsed: 0.056 s
% 0.20/0.47  % (11155)------------------------------
% 0.20/0.47  % (11155)------------------------------
% 0.20/0.49  % (11151)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (11148)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (11144)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (11158)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (11152)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (11161)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (11146)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (11149)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (11160)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (11159)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.51  % (11153)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.52  % (11150)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (11145)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.52  % (11157)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.52  % (11154)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.53  % (11156)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.57/0.59  % (11151)Refutation found. Thanks to Tanya!
% 1.57/0.59  % SZS status Theorem for theBenchmark
% 1.57/0.59  % SZS output start Proof for theBenchmark
% 1.57/0.59  fof(f4179,plain,(
% 1.57/0.59    $false),
% 1.57/0.59    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f93,f97,f103,f109,f127,f131,f139,f147,f152,f156,f165,f174,f181,f187,f191,f205,f215,f229,f239,f243,f247,f256,f270,f290,f294,f319,f333,f362,f396,f577,f601,f605,f609,f946,f962,f980,f1101,f1860,f1990,f2128,f2917,f3770,f3939])).
% 1.57/0.59  fof(f3939,plain,(
% 1.57/0.59    ~spl2_8 | spl2_16 | ~spl2_20 | ~spl2_34 | ~spl2_38 | ~spl2_43 | ~spl2_71 | ~spl2_76 | ~spl2_88 | ~spl2_147),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f3936])).
% 1.57/0.59  fof(f3936,plain,(
% 1.57/0.59    $false | (~spl2_8 | spl2_16 | ~spl2_20 | ~spl2_34 | ~spl2_38 | ~spl2_43 | ~spl2_71 | ~spl2_76 | ~spl2_88 | ~spl2_147)),
% 1.57/0.59    inference(subsumption_resolution,[],[f151,f3935])).
% 1.57/0.59  fof(f3935,plain,(
% 1.57/0.59    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4)))) ) | (~spl2_8 | ~spl2_20 | ~spl2_34 | ~spl2_38 | ~spl2_43 | ~spl2_71 | ~spl2_76 | ~spl2_88 | ~spl2_147)),
% 1.57/0.59    inference(backward_demodulation,[],[f1948,f3818])).
% 1.57/0.59  fof(f3818,plain,(
% 1.57/0.59    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X3)) ) | (~spl2_20 | ~spl2_71 | ~spl2_76 | ~spl2_147)),
% 1.57/0.59    inference(backward_demodulation,[],[f979,f3801])).
% 1.57/0.59  fof(f3801,plain,(
% 1.57/0.59    ( ! [X10,X9] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X9),X10))) = k7_relat_1(k6_relat_1(X10),X9)) ) | (~spl2_20 | ~spl2_76 | ~spl2_147)),
% 1.57/0.59    inference(forward_demodulation,[],[f3775,f1100])).
% 1.57/0.59  fof(f1100,plain,(
% 1.57/0.59    ( ! [X14,X13] : (k7_relat_1(k6_relat_1(X14),X13) = k7_relat_1(k6_relat_1(X14),k2_relat_1(k7_relat_1(k6_relat_1(X13),X14)))) ) | ~spl2_76),
% 1.57/0.59    inference(avatar_component_clause,[],[f1099])).
% 1.57/0.59  fof(f1099,plain,(
% 1.57/0.59    spl2_76 <=> ! [X13,X14] : k7_relat_1(k6_relat_1(X14),X13) = k7_relat_1(k6_relat_1(X14),k2_relat_1(k7_relat_1(k6_relat_1(X13),X14)))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 1.57/0.59  fof(f3775,plain,(
% 1.57/0.59    ( ! [X10,X9] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X9),X10))) = k7_relat_1(k6_relat_1(X10),k2_relat_1(k7_relat_1(k6_relat_1(X9),X10)))) ) | (~spl2_20 | ~spl2_147)),
% 1.57/0.59    inference(resolution,[],[f3769,f180])).
% 1.57/0.59  fof(f180,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_20),
% 1.57/0.59    inference(avatar_component_clause,[],[f179])).
% 1.57/0.59  fof(f179,plain,(
% 1.57/0.59    spl2_20 <=> ! [X1,X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 1.57/0.59  fof(f3769,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0)) ) | ~spl2_147),
% 1.57/0.59    inference(avatar_component_clause,[],[f3768])).
% 1.57/0.59  fof(f3768,plain,(
% 1.57/0.59    spl2_147 <=> ! [X1,X0] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_147])])).
% 1.57/0.59  fof(f979,plain,(
% 1.57/0.59    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)) ) | ~spl2_71),
% 1.57/0.59    inference(avatar_component_clause,[],[f978])).
% 1.57/0.59  fof(f978,plain,(
% 1.57/0.59    spl2_71 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 1.57/0.59  fof(f1948,plain,(
% 1.57/0.59    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X4)) ) | (~spl2_8 | ~spl2_34 | ~spl2_38 | ~spl2_43 | ~spl2_88)),
% 1.57/0.59    inference(forward_demodulation,[],[f1945,f293])).
% 1.57/0.59  fof(f293,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) ) | ~spl2_34),
% 1.57/0.59    inference(avatar_component_clause,[],[f292])).
% 1.57/0.59  fof(f292,plain,(
% 1.57/0.59    spl2_34 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 1.57/0.59  fof(f1945,plain,(
% 1.57/0.59    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X3),X4)) ) | (~spl2_8 | ~spl2_38 | ~spl2_43 | ~spl2_88)),
% 1.57/0.59    inference(backward_demodulation,[],[f1873,f1944])).
% 1.57/0.59  fof(f1944,plain,(
% 1.57/0.59    ( ! [X23,X21,X22] : (k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X22,X22,X22,X23))),X21) = k7_relat_1(k7_relat_1(k6_relat_1(X23),X22),X21)) ) | (~spl2_38 | ~spl2_43 | ~spl2_88)),
% 1.57/0.59    inference(forward_demodulation,[],[f1884,f361])).
% 1.57/0.59  fof(f361,plain,(
% 1.57/0.59    ( ! [X6,X7,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))) ) | ~spl2_43),
% 1.57/0.59    inference(avatar_component_clause,[],[f360])).
% 1.57/0.59  fof(f360,plain,(
% 1.57/0.59    spl2_43 <=> ! [X5,X7,X6] : k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 1.57/0.59  fof(f1884,plain,(
% 1.57/0.59    ( ! [X23,X21,X22] : (k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X22,X22,X22,X23))),X21) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X21),X22),X23))) ) | (~spl2_38 | ~spl2_88)),
% 1.57/0.59    inference(superposition,[],[f332,f1859])).
% 1.57/0.59  fof(f1859,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) ) | ~spl2_88),
% 1.57/0.59    inference(avatar_component_clause,[],[f1858])).
% 1.57/0.59  fof(f1858,plain,(
% 1.57/0.59    spl2_88 <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 1.57/0.59  fof(f332,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | ~spl2_38),
% 1.57/0.59    inference(avatar_component_clause,[],[f331])).
% 1.57/0.59  fof(f331,plain,(
% 1.57/0.59    spl2_38 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 1.57/0.59  fof(f1873,plain,(
% 1.57/0.59    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3),X4)) ) | (~spl2_8 | ~spl2_88)),
% 1.57/0.59    inference(superposition,[],[f1859,f102])).
% 1.57/0.59  fof(f102,plain,(
% 1.57/0.59    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | ~spl2_8),
% 1.57/0.59    inference(avatar_component_clause,[],[f101])).
% 1.57/0.59  fof(f101,plain,(
% 1.57/0.59    spl2_8 <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.57/0.59  fof(f151,plain,(
% 1.57/0.59    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_16),
% 1.57/0.59    inference(avatar_component_clause,[],[f149])).
% 1.57/0.59  fof(f149,plain,(
% 1.57/0.59    spl2_16 <=> k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.57/0.59  fof(f3770,plain,(
% 1.57/0.59    spl2_147 | ~spl2_57 | ~spl2_136),
% 1.57/0.59    inference(avatar_split_clause,[],[f3755,f2915,f607,f3768])).
% 1.57/0.59  fof(f607,plain,(
% 1.57/0.59    spl2_57 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 1.57/0.59  fof(f2915,plain,(
% 1.57/0.59    spl2_136 <=> ! [X36,X38,X37,X39] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X36),X37))),X38),X39)),X36)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).
% 1.57/0.59  fof(f3755,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0)) ) | (~spl2_57 | ~spl2_136)),
% 1.57/0.59    inference(superposition,[],[f2916,f608])).
% 1.57/0.59  fof(f608,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0)) ) | ~spl2_57),
% 1.57/0.59    inference(avatar_component_clause,[],[f607])).
% 1.57/0.59  fof(f2916,plain,(
% 1.57/0.59    ( ! [X39,X37,X38,X36] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X36),X37))),X38),X39)),X36)) ) | ~spl2_136),
% 1.57/0.59    inference(avatar_component_clause,[],[f2915])).
% 1.57/0.59  fof(f2917,plain,(
% 1.57/0.59    spl2_136 | ~spl2_55 | ~spl2_100),
% 1.57/0.59    inference(avatar_split_clause,[],[f2342,f2126,f599,f2915])).
% 1.57/0.59  fof(f599,plain,(
% 1.57/0.59    spl2_55 <=> ! [X5,X4] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(X4),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 1.57/0.59  fof(f2126,plain,(
% 1.57/0.59    spl2_100 <=> ! [X11,X13,X12,X14] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X11),X12),X13),X14)),X11)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).
% 1.57/0.59  fof(f2342,plain,(
% 1.57/0.59    ( ! [X39,X37,X38,X36] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X36),X37))),X38),X39)),X36)) ) | (~spl2_55 | ~spl2_100)),
% 1.57/0.59    inference(superposition,[],[f2127,f600])).
% 1.57/0.59  fof(f600,plain,(
% 1.57/0.59    ( ! [X4,X5] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(X4),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))) ) | ~spl2_55),
% 1.57/0.59    inference(avatar_component_clause,[],[f599])).
% 1.57/0.59  fof(f2127,plain,(
% 1.57/0.59    ( ! [X14,X12,X13,X11] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X11),X12),X13),X14)),X11)) ) | ~spl2_100),
% 1.57/0.59    inference(avatar_component_clause,[],[f2126])).
% 1.57/0.59  fof(f2128,plain,(
% 1.57/0.59    spl2_100 | ~spl2_88 | ~spl2_90),
% 1.57/0.59    inference(avatar_split_clause,[],[f2018,f1988,f1858,f2126])).
% 1.57/0.59  fof(f1988,plain,(
% 1.57/0.59    spl2_90 <=> ! [X13,X12,X14] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X14)),X12)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).
% 1.57/0.59  fof(f2018,plain,(
% 1.57/0.59    ( ! [X14,X12,X13,X11] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X11),X12),X13),X14)),X11)) ) | (~spl2_88 | ~spl2_90)),
% 1.57/0.59    inference(superposition,[],[f1989,f1859])).
% 1.57/0.59  fof(f1989,plain,(
% 1.57/0.59    ( ! [X14,X12,X13] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X14)),X12)) ) | ~spl2_90),
% 1.57/0.59    inference(avatar_component_clause,[],[f1988])).
% 1.57/0.59  fof(f1990,plain,(
% 1.57/0.59    spl2_90 | ~spl2_31 | ~spl2_88),
% 1.57/0.59    inference(avatar_split_clause,[],[f1881,f1858,f268,f1988])).
% 1.57/0.59  fof(f268,plain,(
% 1.57/0.59    spl2_31 <=> ! [X1,X0] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 1.57/0.59  fof(f1881,plain,(
% 1.57/0.59    ( ! [X14,X12,X13] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X14)),X12)) ) | (~spl2_31 | ~spl2_88)),
% 1.57/0.59    inference(superposition,[],[f269,f1859])).
% 1.57/0.59  fof(f269,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | ~spl2_31),
% 1.57/0.59    inference(avatar_component_clause,[],[f268])).
% 1.57/0.59  fof(f1860,plain,(
% 1.57/0.59    spl2_88 | ~spl2_1 | ~spl2_45),
% 1.57/0.59    inference(avatar_split_clause,[],[f578,f394,f71,f1858])).
% 1.57/0.59  fof(f71,plain,(
% 1.57/0.59    spl2_1 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.57/0.59  fof(f394,plain,(
% 1.57/0.59    spl2_45 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 1.57/0.59  fof(f578,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) ) | (~spl2_1 | ~spl2_45)),
% 1.57/0.59    inference(resolution,[],[f395,f72])).
% 1.57/0.59  fof(f72,plain,(
% 1.57/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_1),
% 1.57/0.59    inference(avatar_component_clause,[],[f71])).
% 1.57/0.59  fof(f395,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) ) | ~spl2_45),
% 1.57/0.59    inference(avatar_component_clause,[],[f394])).
% 1.57/0.59  fof(f1101,plain,(
% 1.57/0.59    spl2_76 | ~spl2_38 | ~spl2_71),
% 1.57/0.59    inference(avatar_split_clause,[],[f1029,f978,f331,f1099])).
% 1.57/0.59  fof(f1029,plain,(
% 1.57/0.59    ( ! [X14,X13] : (k7_relat_1(k6_relat_1(X14),X13) = k7_relat_1(k6_relat_1(X14),k2_relat_1(k7_relat_1(k6_relat_1(X13),X14)))) ) | (~spl2_38 | ~spl2_71)),
% 1.57/0.59    inference(forward_demodulation,[],[f993,f332])).
% 1.57/0.59  fof(f993,plain,(
% 1.57/0.59    ( ! [X14,X13] : (k7_relat_1(k6_relat_1(X14),k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))) = k4_relat_1(k7_relat_1(k6_relat_1(X13),X14))) ) | (~spl2_38 | ~spl2_71)),
% 1.57/0.59    inference(superposition,[],[f332,f979])).
% 1.57/0.59  fof(f980,plain,(
% 1.57/0.59    spl2_71 | ~spl2_29 | ~spl2_66 | ~spl2_70),
% 1.57/0.59    inference(avatar_split_clause,[],[f975,f960,f944,f245,f978])).
% 1.57/0.59  fof(f245,plain,(
% 1.57/0.59    spl2_29 <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 1.57/0.59  fof(f944,plain,(
% 1.57/0.59    spl2_66 <=> ! [X3,X4] : k7_relat_1(k6_relat_1(X3),X4) = k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 1.57/0.59  fof(f960,plain,(
% 1.57/0.59    spl2_70 <=> ! [X13,X14] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))),X13)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 1.57/0.59  fof(f975,plain,(
% 1.57/0.59    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)) ) | (~spl2_29 | ~spl2_66 | ~spl2_70)),
% 1.57/0.59    inference(forward_demodulation,[],[f968,f961])).
% 1.57/0.59  fof(f961,plain,(
% 1.57/0.59    ( ! [X14,X13] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))),X13)) ) | ~spl2_70),
% 1.57/0.59    inference(avatar_component_clause,[],[f960])).
% 1.57/0.59  fof(f968,plain,(
% 1.57/0.59    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3)) ) | (~spl2_29 | ~spl2_66)),
% 1.57/0.59    inference(superposition,[],[f945,f246])).
% 1.57/0.59  fof(f246,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2))) ) | ~spl2_29),
% 1.57/0.59    inference(avatar_component_clause,[],[f245])).
% 1.57/0.59  fof(f945,plain,(
% 1.57/0.59    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))) ) | ~spl2_66),
% 1.57/0.59    inference(avatar_component_clause,[],[f944])).
% 1.57/0.59  fof(f962,plain,(
% 1.57/0.59    spl2_70 | ~spl2_4 | ~spl2_38 | ~spl2_56),
% 1.57/0.59    inference(avatar_split_clause,[],[f772,f603,f331,f83,f960])).
% 1.57/0.59  fof(f83,plain,(
% 1.57/0.59    spl2_4 <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.57/0.59  fof(f603,plain,(
% 1.57/0.59    spl2_56 <=> ! [X7,X6] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))) = k7_relat_1(k6_relat_1(X6),k2_relat_1(k7_relat_1(k6_relat_1(X6),X7)))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 1.57/0.59  fof(f772,plain,(
% 1.57/0.59    ( ! [X14,X13] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))),X13)) ) | (~spl2_4 | ~spl2_38 | ~spl2_56)),
% 1.57/0.59    inference(forward_demodulation,[],[f742,f84])).
% 1.57/0.59  fof(f84,plain,(
% 1.57/0.59    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) ) | ~spl2_4),
% 1.57/0.59    inference(avatar_component_clause,[],[f83])).
% 1.57/0.59  fof(f742,plain,(
% 1.57/0.59    ( ! [X14,X13] : (k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))),X13) = k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X13),X14))))) ) | (~spl2_38 | ~spl2_56)),
% 1.57/0.59    inference(superposition,[],[f332,f604])).
% 1.57/0.59  fof(f604,plain,(
% 1.57/0.59    ( ! [X6,X7] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))) = k7_relat_1(k6_relat_1(X6),k2_relat_1(k7_relat_1(k6_relat_1(X6),X7)))) ) | ~spl2_56),
% 1.57/0.59    inference(avatar_component_clause,[],[f603])).
% 1.57/0.59  fof(f946,plain,(
% 1.57/0.59    spl2_66 | ~spl2_18 | ~spl2_24),
% 1.57/0.59    inference(avatar_split_clause,[],[f218,f213,f163,f944])).
% 1.57/0.59  fof(f163,plain,(
% 1.57/0.59    spl2_18 <=> ! [X1,X2] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.57/0.59  fof(f213,plain,(
% 1.57/0.59    spl2_24 <=> ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.57/0.59  fof(f218,plain,(
% 1.57/0.59    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))) ) | (~spl2_18 | ~spl2_24)),
% 1.57/0.59    inference(resolution,[],[f214,f164])).
% 1.57/0.59  fof(f164,plain,(
% 1.57/0.59    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ) | ~spl2_18),
% 1.57/0.59    inference(avatar_component_clause,[],[f163])).
% 1.57/0.59  fof(f214,plain,(
% 1.57/0.59    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0) ) | ~spl2_24),
% 1.57/0.59    inference(avatar_component_clause,[],[f213])).
% 1.57/0.59  fof(f609,plain,(
% 1.57/0.59    spl2_57 | ~spl2_38 | ~spl2_43 | ~spl2_54),
% 1.57/0.59    inference(avatar_split_clause,[],[f597,f575,f360,f331,f607])).
% 1.57/0.59  fof(f575,plain,(
% 1.57/0.59    spl2_54 <=> ! [X9,X8] : k7_relat_1(k6_relat_1(X8),X9) = k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),k1_relat_1(k7_relat_1(k6_relat_1(X8),X9)))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 1.57/0.59  fof(f597,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0)) ) | (~spl2_38 | ~spl2_43 | ~spl2_54)),
% 1.57/0.59    inference(forward_demodulation,[],[f585,f332])).
% 1.57/0.59  fof(f585,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0)) ) | (~spl2_43 | ~spl2_54)),
% 1.57/0.59    inference(superposition,[],[f361,f576])).
% 1.57/0.59  fof(f576,plain,(
% 1.57/0.59    ( ! [X8,X9] : (k7_relat_1(k6_relat_1(X8),X9) = k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),k1_relat_1(k7_relat_1(k6_relat_1(X8),X9)))) ) | ~spl2_54),
% 1.57/0.59    inference(avatar_component_clause,[],[f575])).
% 1.57/0.59  fof(f605,plain,(
% 1.57/0.59    spl2_56 | ~spl2_20 | ~spl2_31),
% 1.57/0.59    inference(avatar_split_clause,[],[f274,f268,f179,f603])).
% 1.57/0.59  fof(f274,plain,(
% 1.57/0.59    ( ! [X6,X7] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X6),X7))) = k7_relat_1(k6_relat_1(X6),k2_relat_1(k7_relat_1(k6_relat_1(X6),X7)))) ) | (~spl2_20 | ~spl2_31)),
% 1.57/0.59    inference(resolution,[],[f269,f180])).
% 1.57/0.59  fof(f601,plain,(
% 1.57/0.59    spl2_55 | ~spl2_20 | ~spl2_30),
% 1.57/0.59    inference(avatar_split_clause,[],[f259,f254,f179,f599])).
% 1.57/0.59  fof(f254,plain,(
% 1.57/0.59    spl2_30 <=> ! [X1,X0] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 1.57/0.59  fof(f259,plain,(
% 1.57/0.59    ( ! [X4,X5] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(X4),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))) ) | (~spl2_20 | ~spl2_30)),
% 1.57/0.59    inference(resolution,[],[f255,f180])).
% 1.57/0.59  fof(f255,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | ~spl2_30),
% 1.57/0.59    inference(avatar_component_clause,[],[f254])).
% 1.57/0.59  fof(f577,plain,(
% 1.57/0.59    spl2_54 | ~spl2_6 | ~spl2_18),
% 1.57/0.59    inference(avatar_split_clause,[],[f169,f163,f91,f575])).
% 1.57/0.59  fof(f91,plain,(
% 1.57/0.59    spl2_6 <=> ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.57/0.59  fof(f169,plain,(
% 1.57/0.59    ( ! [X8,X9] : (k7_relat_1(k6_relat_1(X8),X9) = k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),k1_relat_1(k7_relat_1(k6_relat_1(X8),X9)))) ) | (~spl2_6 | ~spl2_18)),
% 1.57/0.59    inference(resolution,[],[f164,f92])).
% 1.57/0.59  fof(f92,plain,(
% 1.57/0.59    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) ) | ~spl2_6),
% 1.57/0.59    inference(avatar_component_clause,[],[f91])).
% 1.57/0.59  fof(f396,plain,(
% 1.57/0.59    spl2_45),
% 1.57/0.59    inference(avatar_split_clause,[],[f69,f394])).
% 1.57/0.59  fof(f69,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 1.57/0.59    inference(definition_unfolding,[],[f64,f67])).
% 1.57/0.59  fof(f67,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.57/0.59    inference(definition_unfolding,[],[f55,f66])).
% 1.57/0.59  fof(f66,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.57/0.59    inference(definition_unfolding,[],[f56,f62])).
% 1.57/0.59  fof(f62,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f2])).
% 1.57/0.59  fof(f2,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.57/0.59  fof(f56,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f1])).
% 1.57/0.59  fof(f1,axiom,(
% 1.57/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.57/0.59  fof(f55,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f3])).
% 1.57/0.59  fof(f3,axiom,(
% 1.57/0.59    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.57/0.59  fof(f64,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f39])).
% 1.57/0.59  fof(f39,plain,(
% 1.57/0.59    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.57/0.59    inference(ennf_transformation,[],[f5])).
% 1.57/0.59  fof(f5,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 1.57/0.59  fof(f362,plain,(
% 1.57/0.59    spl2_43 | ~spl2_1 | ~spl2_4 | ~spl2_12 | ~spl2_13 | ~spl2_15 | ~spl2_17 | ~spl2_18 | ~spl2_26 | ~spl2_37),
% 1.57/0.59    inference(avatar_split_clause,[],[f329,f317,f227,f163,f154,f145,f129,f125,f83,f71,f360])).
% 1.57/0.59  fof(f125,plain,(
% 1.57/0.59    spl2_12 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.57/0.59  fof(f129,plain,(
% 1.57/0.59    spl2_13 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.57/0.59  fof(f145,plain,(
% 1.57/0.59    spl2_15 <=> ! [X1,X0] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.57/0.59  fof(f154,plain,(
% 1.57/0.59    spl2_17 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.57/0.59  fof(f227,plain,(
% 1.57/0.59    spl2_26 <=> ! [X1,X0,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 1.57/0.59  fof(f317,plain,(
% 1.57/0.59    spl2_37 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 1.57/0.59  fof(f329,plain,(
% 1.57/0.59    ( ! [X6,X7,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))) ) | (~spl2_1 | ~spl2_4 | ~spl2_12 | ~spl2_13 | ~spl2_15 | ~spl2_17 | ~spl2_18 | ~spl2_26 | ~spl2_37)),
% 1.57/0.59    inference(forward_demodulation,[],[f328,f166])).
% 1.57/0.59  fof(f166,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_13 | ~spl2_18)),
% 1.57/0.59    inference(resolution,[],[f164,f130])).
% 1.57/0.59  fof(f130,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_13),
% 1.57/0.59    inference(avatar_component_clause,[],[f129])).
% 1.57/0.59  fof(f328,plain,(
% 1.57/0.59    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)) ) | (~spl2_1 | ~spl2_4 | ~spl2_12 | ~spl2_15 | ~spl2_17 | ~spl2_18 | ~spl2_26 | ~spl2_37)),
% 1.57/0.59    inference(forward_demodulation,[],[f327,f234])).
% 1.57/0.59  fof(f234,plain,(
% 1.57/0.59    ( ! [X4,X5,X3] : (k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)) ) | (~spl2_1 | ~spl2_12 | ~spl2_15 | ~spl2_18 | ~spl2_26)),
% 1.57/0.59    inference(backward_demodulation,[],[f167,f233])).
% 1.57/0.59  fof(f233,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2))) ) | (~spl2_1 | ~spl2_15 | ~spl2_26)),
% 1.57/0.59    inference(forward_demodulation,[],[f230,f146])).
% 1.57/0.59  fof(f146,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_15),
% 1.57/0.59    inference(avatar_component_clause,[],[f145])).
% 1.57/0.59  fof(f230,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2)) ) | (~spl2_1 | ~spl2_26)),
% 1.57/0.59    inference(resolution,[],[f228,f72])).
% 1.57/0.59  fof(f228,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))) ) | ~spl2_26),
% 1.57/0.59    inference(avatar_component_clause,[],[f227])).
% 1.57/0.59  fof(f167,plain,(
% 1.57/0.59    ( ! [X4,X5,X3] : (k8_relat_1(X3,k7_relat_1(k6_relat_1(X4),X5)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3))) ) | (~spl2_12 | ~spl2_18)),
% 1.57/0.59    inference(resolution,[],[f164,f126])).
% 1.57/0.59  fof(f126,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_12),
% 1.57/0.59    inference(avatar_component_clause,[],[f125])).
% 1.57/0.59  fof(f327,plain,(
% 1.57/0.59    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5))) ) | (~spl2_1 | ~spl2_4 | ~spl2_17 | ~spl2_18 | ~spl2_37)),
% 1.57/0.59    inference(forward_demodulation,[],[f322,f325])).
% 1.57/0.59  fof(f325,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | (~spl2_1 | ~spl2_4 | ~spl2_17 | ~spl2_37)),
% 1.57/0.59    inference(forward_demodulation,[],[f324,f155])).
% 1.57/0.59  fof(f155,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_17),
% 1.57/0.59    inference(avatar_component_clause,[],[f154])).
% 1.57/0.59  fof(f324,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | (~spl2_1 | ~spl2_4 | ~spl2_17 | ~spl2_37)),
% 1.57/0.59    inference(forward_demodulation,[],[f323,f155])).
% 1.57/0.59  fof(f323,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ) | (~spl2_1 | ~spl2_4 | ~spl2_37)),
% 1.57/0.59    inference(forward_demodulation,[],[f320,f84])).
% 1.57/0.59  fof(f320,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))) ) | (~spl2_1 | ~spl2_37)),
% 1.57/0.59    inference(resolution,[],[f318,f72])).
% 1.57/0.59  fof(f318,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) ) | ~spl2_37),
% 1.57/0.59    inference(avatar_component_clause,[],[f317])).
% 1.57/0.59  fof(f322,plain,(
% 1.57/0.59    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5))) ) | (~spl2_18 | ~spl2_37)),
% 1.57/0.59    inference(resolution,[],[f318,f164])).
% 1.57/0.59  fof(f333,plain,(
% 1.57/0.59    spl2_38 | ~spl2_1 | ~spl2_4 | ~spl2_17 | ~spl2_37),
% 1.57/0.59    inference(avatar_split_clause,[],[f325,f317,f154,f83,f71,f331])).
% 1.57/0.59  fof(f319,plain,(
% 1.57/0.59    spl2_37 | ~spl2_1 | ~spl2_4 | ~spl2_33),
% 1.57/0.59    inference(avatar_split_clause,[],[f315,f288,f83,f71,f317])).
% 1.57/0.59  fof(f288,plain,(
% 1.57/0.59    spl2_33 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 1.57/0.59  fof(f315,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(X0)) ) | (~spl2_1 | ~spl2_4 | ~spl2_33)),
% 1.57/0.59    inference(forward_demodulation,[],[f312,f84])).
% 1.57/0.59  fof(f312,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1)))) ) | (~spl2_1 | ~spl2_33)),
% 1.57/0.59    inference(resolution,[],[f289,f72])).
% 1.57/0.59  fof(f289,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) ) | ~spl2_33),
% 1.57/0.59    inference(avatar_component_clause,[],[f288])).
% 1.57/0.59  fof(f294,plain,(
% 1.57/0.59    spl2_34 | ~spl2_8 | ~spl2_15 | ~spl2_29),
% 1.57/0.59    inference(avatar_split_clause,[],[f286,f245,f145,f101,f292])).
% 1.57/0.59  fof(f286,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) ) | (~spl2_8 | ~spl2_15 | ~spl2_29)),
% 1.57/0.59    inference(forward_demodulation,[],[f283,f146])).
% 1.57/0.59  fof(f283,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) ) | (~spl2_8 | ~spl2_29)),
% 1.57/0.59    inference(superposition,[],[f246,f102])).
% 1.57/0.59  fof(f290,plain,(
% 1.57/0.59    spl2_33),
% 1.57/0.59    inference(avatar_split_clause,[],[f51,f288])).
% 1.57/0.59  fof(f51,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f27])).
% 1.57/0.59  fof(f27,plain,(
% 1.57/0.59    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(ennf_transformation,[],[f11])).
% 1.57/0.59  fof(f11,axiom,(
% 1.57/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.57/0.59  fof(f270,plain,(
% 1.57/0.59    spl2_31 | ~spl2_1 | ~spl2_3 | ~spl2_18 | ~spl2_28),
% 1.57/0.59    inference(avatar_split_clause,[],[f266,f241,f163,f79,f71,f268])).
% 1.57/0.59  fof(f79,plain,(
% 1.57/0.59    spl2_3 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.57/0.59  fof(f241,plain,(
% 1.57/0.59    spl2_28 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 1.57/0.59  fof(f266,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | (~spl2_1 | ~spl2_3 | ~spl2_18 | ~spl2_28)),
% 1.57/0.59    inference(forward_demodulation,[],[f265,f80])).
% 1.57/0.59  fof(f80,plain,(
% 1.57/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_3),
% 1.57/0.59    inference(avatar_component_clause,[],[f79])).
% 1.57/0.59  fof(f265,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k2_relat_1(k6_relat_1(X0)))) ) | (~spl2_1 | ~spl2_18 | ~spl2_28)),
% 1.57/0.59    inference(subsumption_resolution,[],[f262,f72])).
% 1.57/0.59  fof(f262,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k2_relat_1(k6_relat_1(X0)))) ) | (~spl2_18 | ~spl2_28)),
% 1.57/0.59    inference(resolution,[],[f242,f164])).
% 1.57/0.59  fof(f242,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))) ) | ~spl2_28),
% 1.57/0.59    inference(avatar_component_clause,[],[f241])).
% 1.57/0.59  fof(f256,plain,(
% 1.57/0.59    spl2_30 | ~spl2_1 | ~spl2_2 | ~spl2_18 | ~spl2_27),
% 1.57/0.59    inference(avatar_split_clause,[],[f252,f237,f163,f75,f71,f254])).
% 1.57/0.59  fof(f75,plain,(
% 1.57/0.59    spl2_2 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.57/0.59  fof(f237,plain,(
% 1.57/0.59    spl2_27 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 1.57/0.59  fof(f252,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_18 | ~spl2_27)),
% 1.57/0.59    inference(forward_demodulation,[],[f251,f76])).
% 1.57/0.59  fof(f76,plain,(
% 1.57/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_2),
% 1.57/0.59    inference(avatar_component_clause,[],[f75])).
% 1.57/0.59  fof(f251,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0)))) ) | (~spl2_1 | ~spl2_18 | ~spl2_27)),
% 1.57/0.59    inference(subsumption_resolution,[],[f248,f72])).
% 1.57/0.59  fof(f248,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0)))) ) | (~spl2_18 | ~spl2_27)),
% 1.57/0.59    inference(resolution,[],[f238,f164])).
% 1.57/0.59  fof(f238,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))) ) | ~spl2_27),
% 1.57/0.59    inference(avatar_component_clause,[],[f237])).
% 1.57/0.59  fof(f247,plain,(
% 1.57/0.59    spl2_29 | ~spl2_1 | ~spl2_15 | ~spl2_26),
% 1.57/0.59    inference(avatar_split_clause,[],[f233,f227,f145,f71,f245])).
% 1.57/0.59  fof(f243,plain,(
% 1.57/0.59    spl2_28 | ~spl2_5 | ~spl2_22),
% 1.57/0.59    inference(avatar_split_clause,[],[f201,f189,f87,f241])).
% 1.57/0.59  fof(f87,plain,(
% 1.57/0.59    spl2_5 <=> ! [X1,X0] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.57/0.59  fof(f189,plain,(
% 1.57/0.59    spl2_22 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 1.57/0.59  fof(f201,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1))) ) | (~spl2_5 | ~spl2_22)),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f198])).
% 1.57/0.59  fof(f198,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | (~spl2_5 | ~spl2_22)),
% 1.57/0.59    inference(resolution,[],[f190,f88])).
% 1.57/0.59  fof(f88,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) ) | ~spl2_5),
% 1.57/0.59    inference(avatar_component_clause,[],[f87])).
% 1.57/0.59  fof(f190,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_22),
% 1.57/0.59    inference(avatar_component_clause,[],[f189])).
% 1.57/0.59  fof(f239,plain,(
% 1.57/0.59    spl2_27 | ~spl2_5 | ~spl2_21),
% 1.57/0.59    inference(avatar_split_clause,[],[f195,f185,f87,f237])).
% 1.57/0.59  fof(f185,plain,(
% 1.57/0.59    spl2_21 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.57/0.59  fof(f195,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1))) ) | (~spl2_5 | ~spl2_21)),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f192])).
% 1.57/0.59  fof(f192,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | (~spl2_5 | ~spl2_21)),
% 1.57/0.59    inference(resolution,[],[f186,f88])).
% 1.57/0.59  fof(f186,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_21),
% 1.57/0.59    inference(avatar_component_clause,[],[f185])).
% 1.57/0.59  fof(f229,plain,(
% 1.57/0.59    spl2_26),
% 1.57/0.59    inference(avatar_split_clause,[],[f63,f227])).
% 1.57/0.59  fof(f63,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f38])).
% 1.57/0.59  fof(f38,plain,(
% 1.57/0.59    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.57/0.59    inference(ennf_transformation,[],[f9])).
% 1.57/0.59  fof(f9,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 1.57/0.59  fof(f215,plain,(
% 1.57/0.59    spl2_24 | ~spl2_19 | ~spl2_23),
% 1.57/0.59    inference(avatar_split_clause,[],[f206,f203,f172,f213])).
% 1.57/0.59  fof(f172,plain,(
% 1.57/0.59    spl2_19 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.57/0.59  fof(f203,plain,(
% 1.57/0.59    spl2_23 <=> ! [X2] : r1_tarski(X2,X2)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 1.57/0.59  fof(f206,plain,(
% 1.57/0.59    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) ) | (~spl2_19 | ~spl2_23)),
% 1.57/0.59    inference(resolution,[],[f204,f173])).
% 1.57/0.59  fof(f173,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) ) | ~spl2_19),
% 1.57/0.59    inference(avatar_component_clause,[],[f172])).
% 1.57/0.59  fof(f204,plain,(
% 1.57/0.59    ( ! [X2] : (r1_tarski(X2,X2)) ) | ~spl2_23),
% 1.57/0.59    inference(avatar_component_clause,[],[f203])).
% 1.57/0.59  fof(f205,plain,(
% 1.57/0.59    spl2_23 | ~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_21),
% 1.57/0.59    inference(avatar_split_clause,[],[f197,f185,f107,f75,f71,f203])).
% 1.57/0.59  fof(f107,plain,(
% 1.57/0.59    spl2_9 <=> ! [X0] : r1_tarski(k6_relat_1(X0),k6_relat_1(X0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.57/0.59  fof(f197,plain,(
% 1.57/0.59    ( ! [X2] : (r1_tarski(X2,X2)) ) | (~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_21)),
% 1.57/0.59    inference(forward_demodulation,[],[f196,f76])).
% 1.57/0.59  fof(f196,plain,(
% 1.57/0.59    ( ! [X2] : (r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(k6_relat_1(X2)))) ) | (~spl2_1 | ~spl2_9 | ~spl2_21)),
% 1.57/0.59    inference(subsumption_resolution,[],[f194,f72])).
% 1.57/0.59  fof(f194,plain,(
% 1.57/0.59    ( ! [X2] : (r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2))) ) | (~spl2_9 | ~spl2_21)),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f193])).
% 1.57/0.59  fof(f193,plain,(
% 1.57/0.59    ( ! [X2] : (r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X2))) ) | (~spl2_9 | ~spl2_21)),
% 1.57/0.59    inference(resolution,[],[f186,f108])).
% 1.57/0.59  fof(f108,plain,(
% 1.57/0.59    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k6_relat_1(X0))) ) | ~spl2_9),
% 1.57/0.59    inference(avatar_component_clause,[],[f107])).
% 1.57/0.59  fof(f191,plain,(
% 1.57/0.59    spl2_22),
% 1.57/0.59    inference(avatar_split_clause,[],[f53,f189])).
% 1.57/0.59  fof(f53,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f29])).
% 1.57/0.59  fof(f29,plain,(
% 1.57/0.59    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(flattening,[],[f28])).
% 1.57/0.59  fof(f28,plain,(
% 1.57/0.59    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(ennf_transformation,[],[f10])).
% 1.57/0.59  fof(f10,axiom,(
% 1.57/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.57/0.59  fof(f187,plain,(
% 1.57/0.59    spl2_21),
% 1.57/0.59    inference(avatar_split_clause,[],[f52,f185])).
% 1.57/0.59  fof(f52,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f29])).
% 1.57/0.59  fof(f181,plain,(
% 1.57/0.59    spl2_20 | ~spl2_1 | ~spl2_3 | ~spl2_15 | ~spl2_19),
% 1.57/0.59    inference(avatar_split_clause,[],[f177,f172,f145,f79,f71,f179])).
% 1.57/0.59  fof(f177,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1)) ) | (~spl2_1 | ~spl2_3 | ~spl2_15 | ~spl2_19)),
% 1.57/0.59    inference(forward_demodulation,[],[f176,f146])).
% 1.57/0.59  fof(f176,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) ) | (~spl2_1 | ~spl2_3 | ~spl2_19)),
% 1.57/0.59    inference(subsumption_resolution,[],[f175,f72])).
% 1.57/0.59  fof(f175,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_3 | ~spl2_19)),
% 1.57/0.59    inference(superposition,[],[f173,f80])).
% 1.57/0.59  fof(f174,plain,(
% 1.57/0.59    spl2_19),
% 1.57/0.59    inference(avatar_split_clause,[],[f60,f172])).
% 1.57/0.59  fof(f60,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f35])).
% 1.57/0.60  fof(f35,plain,(
% 1.57/0.60    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.57/0.60    inference(flattening,[],[f34])).
% 1.57/0.60  fof(f34,plain,(
% 1.57/0.60    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.57/0.60    inference(ennf_transformation,[],[f8])).
% 1.57/0.60  fof(f8,axiom,(
% 1.57/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 1.57/0.60  fof(f165,plain,(
% 1.57/0.60    spl2_18 | ~spl2_1 | ~spl2_7 | ~spl2_17),
% 1.57/0.60    inference(avatar_split_clause,[],[f161,f154,f95,f71,f163])).
% 1.57/0.60  fof(f95,plain,(
% 1.57/0.60    spl2_7 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.57/0.60  fof(f161,plain,(
% 1.57/0.60    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ) | (~spl2_1 | ~spl2_7 | ~spl2_17)),
% 1.57/0.60    inference(subsumption_resolution,[],[f160,f72])).
% 1.57/0.60  fof(f160,plain,(
% 1.57/0.60    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_7 | ~spl2_17)),
% 1.57/0.60    inference(subsumption_resolution,[],[f159,f72])).
% 1.57/0.60  fof(f159,plain,(
% 1.57/0.60    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_7 | ~spl2_17)),
% 1.57/0.60    inference(superposition,[],[f96,f155])).
% 1.57/0.60  fof(f96,plain,(
% 1.57/0.60    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_7),
% 1.57/0.60    inference(avatar_component_clause,[],[f95])).
% 1.57/0.60  fof(f156,plain,(
% 1.57/0.60    spl2_17 | ~spl2_1 | ~spl2_13),
% 1.57/0.60    inference(avatar_split_clause,[],[f140,f129,f71,f154])).
% 1.57/0.60  fof(f140,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_13)),
% 1.57/0.60    inference(resolution,[],[f130,f72])).
% 1.57/0.60  fof(f152,plain,(
% 1.57/0.60    ~spl2_16 | ~spl2_1 | ~spl2_12 | ~spl2_13 | spl2_14),
% 1.57/0.60    inference(avatar_split_clause,[],[f143,f136,f129,f125,f71,f149])).
% 1.57/0.60  fof(f136,plain,(
% 1.57/0.60    spl2_14 <=> k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k8_relat_1(sK0,k6_relat_1(sK1))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.57/0.60  fof(f143,plain,(
% 1.57/0.60    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | (~spl2_1 | ~spl2_12 | ~spl2_13 | spl2_14)),
% 1.57/0.60    inference(backward_demodulation,[],[f138,f142])).
% 1.57/0.60  fof(f142,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_12 | ~spl2_13)),
% 1.57/0.60    inference(backward_demodulation,[],[f132,f140])).
% 1.57/0.60  fof(f132,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_12)),
% 1.57/0.60    inference(resolution,[],[f126,f72])).
% 1.57/0.60  fof(f138,plain,(
% 1.57/0.60    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) | spl2_14),
% 1.57/0.60    inference(avatar_component_clause,[],[f136])).
% 1.57/0.60  fof(f147,plain,(
% 1.57/0.60    spl2_15 | ~spl2_1 | ~spl2_12 | ~spl2_13),
% 1.57/0.60    inference(avatar_split_clause,[],[f142,f129,f125,f71,f145])).
% 1.57/0.60  fof(f139,plain,(
% 1.57/0.60    ~spl2_14 | ~spl2_1 | ~spl2_12),
% 1.57/0.60    inference(avatar_split_clause,[],[f134,f125,f71,f136])).
% 1.57/0.60  fof(f134,plain,(
% 1.57/0.60    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) | (~spl2_1 | ~spl2_12)),
% 1.57/0.60    inference(backward_demodulation,[],[f68,f132])).
% 1.57/0.60  fof(f68,plain,(
% 1.57/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.57/0.60    inference(definition_unfolding,[],[f44,f67])).
% 1.57/0.60  fof(f44,plain,(
% 1.57/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.57/0.60    inference(cnf_transformation,[],[f43])).
% 1.57/0.60  fof(f43,plain,(
% 1.57/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.57/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f42])).
% 1.57/0.60  fof(f42,plain,(
% 1.57/0.60    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.57/0.60    introduced(choice_axiom,[])).
% 1.57/0.60  fof(f24,plain,(
% 1.57/0.60    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.57/0.60    inference(ennf_transformation,[],[f21])).
% 1.57/0.60  fof(f21,negated_conjecture,(
% 1.57/0.60    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.57/0.60    inference(negated_conjecture,[],[f20])).
% 1.57/0.60  fof(f20,conjecture,(
% 1.57/0.60    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.57/0.60  fof(f131,plain,(
% 1.57/0.60    spl2_13),
% 1.57/0.60    inference(avatar_split_clause,[],[f59,f129])).
% 1.57/0.60  fof(f59,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f33])).
% 1.57/0.60  fof(f33,plain,(
% 1.57/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.57/0.60    inference(ennf_transformation,[],[f17])).
% 1.57/0.60  fof(f17,axiom,(
% 1.57/0.60    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.57/0.60  fof(f127,plain,(
% 1.57/0.60    spl2_12),
% 1.57/0.60    inference(avatar_split_clause,[],[f58,f125])).
% 1.57/0.60  fof(f58,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f32])).
% 1.57/0.60  fof(f32,plain,(
% 1.57/0.60    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.57/0.60    inference(ennf_transformation,[],[f7])).
% 1.57/0.60  fof(f7,axiom,(
% 1.57/0.60    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 1.57/0.60  fof(f109,plain,(
% 1.57/0.60    spl2_9 | ~spl2_1 | ~spl2_5 | ~spl2_8),
% 1.57/0.60    inference(avatar_split_clause,[],[f105,f101,f87,f71,f107])).
% 1.57/0.60  fof(f105,plain,(
% 1.57/0.60    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k6_relat_1(X0))) ) | (~spl2_1 | ~spl2_5 | ~spl2_8)),
% 1.57/0.60    inference(subsumption_resolution,[],[f104,f72])).
% 1.57/0.60  fof(f104,plain,(
% 1.57/0.60    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_5 | ~spl2_8)),
% 1.57/0.60    inference(superposition,[],[f88,f102])).
% 1.57/0.60  fof(f103,plain,(
% 1.57/0.60    spl2_8 | ~spl2_1 | ~spl2_2 | ~spl2_6),
% 1.57/0.60    inference(avatar_split_clause,[],[f99,f91,f75,f71,f101])).
% 1.57/0.60  fof(f99,plain,(
% 1.57/0.60    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_6)),
% 1.57/0.60    inference(forward_demodulation,[],[f98,f76])).
% 1.57/0.60  fof(f98,plain,(
% 1.57/0.60    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) ) | (~spl2_1 | ~spl2_6)),
% 1.57/0.60    inference(resolution,[],[f92,f72])).
% 1.57/0.60  fof(f97,plain,(
% 1.57/0.60    spl2_7),
% 1.57/0.60    inference(avatar_split_clause,[],[f61,f95])).
% 1.57/0.60  fof(f61,plain,(
% 1.57/0.60    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f37])).
% 1.57/0.60  fof(f37,plain,(
% 1.57/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.57/0.60    inference(flattening,[],[f36])).
% 1.57/0.60  fof(f36,plain,(
% 1.57/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f4])).
% 1.57/0.60  fof(f4,axiom,(
% 1.57/0.60    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.57/0.60  fof(f93,plain,(
% 1.57/0.60    spl2_6),
% 1.57/0.60    inference(avatar_split_clause,[],[f49,f91])).
% 1.57/0.60  fof(f49,plain,(
% 1.57/0.60    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f25])).
% 1.57/0.60  fof(f25,plain,(
% 1.57/0.60    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.57/0.60    inference(ennf_transformation,[],[f18])).
% 1.57/0.60  fof(f18,axiom,(
% 1.57/0.60    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 1.57/0.60  fof(f89,plain,(
% 1.57/0.60    spl2_5),
% 1.57/0.60    inference(avatar_split_clause,[],[f57,f87])).
% 1.57/0.60  fof(f57,plain,(
% 1.57/0.60    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f31])).
% 1.57/0.60  fof(f31,plain,(
% 1.57/0.60    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.57/0.60    inference(ennf_transformation,[],[f16])).
% 1.57/0.60  fof(f16,axiom,(
% 1.57/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 1.57/0.60  fof(f85,plain,(
% 1.57/0.60    spl2_4),
% 1.57/0.60    inference(avatar_split_clause,[],[f45,f83])).
% 1.57/0.60  fof(f45,plain,(
% 1.57/0.60    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f14])).
% 1.57/0.60  fof(f14,axiom,(
% 1.57/0.60    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 1.57/0.60  fof(f81,plain,(
% 1.57/0.60    spl2_3),
% 1.57/0.60    inference(avatar_split_clause,[],[f48,f79])).
% 1.57/0.60  fof(f48,plain,(
% 1.57/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.57/0.60    inference(cnf_transformation,[],[f13])).
% 1.57/0.60  fof(f13,axiom,(
% 1.57/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.57/0.60  fof(f77,plain,(
% 1.57/0.60    spl2_2),
% 1.57/0.60    inference(avatar_split_clause,[],[f47,f75])).
% 1.57/0.60  fof(f47,plain,(
% 1.57/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.57/0.60    inference(cnf_transformation,[],[f13])).
% 1.57/0.60  fof(f73,plain,(
% 1.57/0.60    spl2_1),
% 1.57/0.60    inference(avatar_split_clause,[],[f46,f71])).
% 1.57/0.60  fof(f46,plain,(
% 1.57/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f23])).
% 1.57/0.60  fof(f23,plain,(
% 1.57/0.60    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.57/0.60    inference(pure_predicate_removal,[],[f22])).
% 1.57/0.60  fof(f22,plain,(
% 1.57/0.60    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.57/0.60    inference(pure_predicate_removal,[],[f19])).
% 1.57/0.60  fof(f19,axiom,(
% 1.57/0.60    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 1.57/0.60  % SZS output end Proof for theBenchmark
% 1.57/0.60  % (11151)------------------------------
% 1.57/0.60  % (11151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.60  % (11151)Termination reason: Refutation
% 1.57/0.60  
% 1.57/0.60  % (11151)Memory used [KB]: 9338
% 1.57/0.60  % (11151)Time elapsed: 0.147 s
% 1.57/0.60  % (11151)------------------------------
% 1.57/0.60  % (11151)------------------------------
% 1.57/0.60  % (11135)Success in time 0.236 s
%------------------------------------------------------------------------------
