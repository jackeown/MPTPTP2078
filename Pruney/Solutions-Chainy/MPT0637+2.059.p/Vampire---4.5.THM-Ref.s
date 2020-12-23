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
% DateTime   : Thu Dec  3 12:52:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 416 expanded)
%              Number of leaves         :   57 ( 198 expanded)
%              Depth                    :   12
%              Number of atoms          :  606 (1048 expanded)
%              Number of equality atoms :  130 ( 249 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4297,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f89,f93,f97,f105,f109,f129,f133,f137,f148,f154,f158,f171,f188,f201,f208,f225,f242,f246,f301,f355,f426,f434,f438,f579,f996,f1384,f1584,f2333,f3090,f3094,f3132,f3632,f3677,f3993,f4220])).

fof(f4220,plain,
    ( ~ spl2_2
    | spl2_109
    | ~ spl2_198 ),
    inference(avatar_contradiction_clause,[],[f4219])).

fof(f4219,plain,
    ( $false
    | ~ spl2_2
    | spl2_109
    | ~ spl2_198 ),
    inference(subsumption_resolution,[],[f4199,f3992])).

fof(f3992,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k9_relat_1(k6_relat_1(X2),X3))
    | ~ spl2_198 ),
    inference(avatar_component_clause,[],[f3991])).

fof(f3991,plain,
    ( spl2_198
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_198])])).

fof(f4199,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k9_relat_1(k6_relat_1(sK0),sK1))
    | ~ spl2_2
    | spl2_109
    | ~ spl2_198 ),
    inference(backward_demodulation,[],[f1583,f4002])).

fof(f4002,plain,
    ( ! [X2,X3] : k9_relat_1(k6_relat_1(X2),X3) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))
    | ~ spl2_2
    | ~ spl2_198 ),
    inference(superposition,[],[f88,f3992])).

fof(f88,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_2
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1583,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | spl2_109 ),
    inference(avatar_component_clause,[],[f1581])).

fof(f1581,plain,
    ( spl2_109
  <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).

fof(f3993,plain,
    ( spl2_198
    | ~ spl2_34
    | ~ spl2_184
    | ~ spl2_195 ),
    inference(avatar_split_clause,[],[f3688,f3675,f3130,f299,f3991])).

fof(f299,plain,
    ( spl2_34
  <=> ! [X1,X0] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f3130,plain,
    ( spl2_184
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_184])])).

fof(f3675,plain,
    ( spl2_195
  <=> ! [X3,X2] : r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_195])])).

fof(f3688,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k9_relat_1(k6_relat_1(X2),X3))
    | ~ spl2_34
    | ~ spl2_184
    | ~ spl2_195 ),
    inference(forward_demodulation,[],[f3679,f3131])).

fof(f3131,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)
    | ~ spl2_184 ),
    inference(avatar_component_clause,[],[f3130])).

fof(f3679,plain,
    ( ! [X2,X3] : k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)
    | ~ spl2_34
    | ~ spl2_195 ),
    inference(resolution,[],[f3676,f300])).

fof(f300,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f299])).

fof(f3676,plain,
    ( ! [X2,X3] : r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X3)
    | ~ spl2_195 ),
    inference(avatar_component_clause,[],[f3675])).

fof(f3677,plain,
    ( spl2_195
    | ~ spl2_19
    | ~ spl2_194 ),
    inference(avatar_split_clause,[],[f3634,f3630,f186,f3675])).

fof(f186,plain,
    ( spl2_19
  <=> ! [X3,X4] : r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f3630,plain,
    ( spl2_194
  <=> ! [X5,X4,X6] :
        ( r1_tarski(k9_relat_1(k6_relat_1(X4),X5),X6)
        | ~ r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_194])])).

fof(f3634,plain,
    ( ! [X2,X3] : r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X3)
    | ~ spl2_19
    | ~ spl2_194 ),
    inference(resolution,[],[f3631,f187])).

fof(f187,plain,
    ( ! [X4,X3] : r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f186])).

fof(f3631,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X6))
        | r1_tarski(k9_relat_1(k6_relat_1(X4),X5),X6) )
    | ~ spl2_194 ),
    inference(avatar_component_clause,[],[f3630])).

fof(f3632,plain,
    ( spl2_194
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_183 ),
    inference(avatar_split_clause,[],[f3626,f3092,f91,f83,f3630])).

fof(f83,plain,
    ( spl2_1
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f91,plain,
    ( spl2_3
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f3092,plain,
    ( spl2_183
  <=> ! [X5,X7,X6] :
        ( r1_tarski(k9_relat_1(k6_relat_1(X5),X6),k2_relat_1(X7))
        | ~ r1_tarski(k7_relat_1(k6_relat_1(X5),X6),X7)
        | ~ v1_relat_1(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_183])])).

fof(f3626,plain,
    ( ! [X6,X4,X5] :
        ( r1_tarski(k9_relat_1(k6_relat_1(X4),X5),X6)
        | ~ r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X6)) )
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_183 ),
    inference(forward_demodulation,[],[f3623,f92])).

fof(f92,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f3623,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X6))
        | r1_tarski(k9_relat_1(k6_relat_1(X4),X5),k2_relat_1(k6_relat_1(X6))) )
    | ~ spl2_1
    | ~ spl2_183 ),
    inference(resolution,[],[f3093,f84])).

fof(f84,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f3093,plain,
    ( ! [X6,X7,X5] :
        ( ~ v1_relat_1(X7)
        | ~ r1_tarski(k7_relat_1(k6_relat_1(X5),X6),X7)
        | r1_tarski(k9_relat_1(k6_relat_1(X5),X6),k2_relat_1(X7)) )
    | ~ spl2_183 ),
    inference(avatar_component_clause,[],[f3092])).

fof(f3132,plain,
    ( spl2_184
    | ~ spl2_38
    | ~ spl2_143
    | ~ spl2_182 ),
    inference(avatar_split_clause,[],[f3127,f3088,f2331,f353,f3130])).

fof(f353,plain,
    ( spl2_38
  <=> ! [X11,X10] : k6_relat_1(k9_relat_1(k6_relat_1(X10),X11)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X10),X11)),X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f2331,plain,
    ( spl2_143
  <=> ! [X7,X8,X6] : k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_143])])).

fof(f3088,plain,
    ( spl2_182
  <=> ! [X9,X10] : k7_relat_1(k6_relat_1(X9),X10) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X10),k6_relat_1(k9_relat_1(k6_relat_1(X9),X10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_182])])).

fof(f3127,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)
    | ~ spl2_38
    | ~ spl2_143
    | ~ spl2_182 ),
    inference(forward_demodulation,[],[f3109,f354])).

fof(f354,plain,
    ( ! [X10,X11] : k6_relat_1(k9_relat_1(k6_relat_1(X10),X11)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X10),X11)),X10)
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f353])).

fof(f3109,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X2),X3)
    | ~ spl2_143
    | ~ spl2_182 ),
    inference(superposition,[],[f3089,f2332])).

fof(f2332,plain,
    ( ! [X6,X8,X7] : k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8)
    | ~ spl2_143 ),
    inference(avatar_component_clause,[],[f2331])).

fof(f3089,plain,
    ( ! [X10,X9] : k7_relat_1(k6_relat_1(X9),X10) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X10),k6_relat_1(k9_relat_1(k6_relat_1(X9),X10)))
    | ~ spl2_182 ),
    inference(avatar_component_clause,[],[f3088])).

fof(f3094,plain,
    ( spl2_183
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f281,f240,f169,f156,f3092])).

fof(f156,plain,
    ( spl2_15
  <=> ! [X1,X0] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f169,plain,
    ( spl2_16
  <=> ! [X5,X6] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f240,plain,
    ( spl2_27
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f281,plain,
    ( ! [X6,X7,X5] :
        ( r1_tarski(k9_relat_1(k6_relat_1(X5),X6),k2_relat_1(X7))
        | ~ r1_tarski(k7_relat_1(k6_relat_1(X5),X6),X7)
        | ~ v1_relat_1(X7) )
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f279,f157])).

fof(f157,plain,
    ( ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f279,plain,
    ( ! [X6,X7,X5] :
        ( ~ r1_tarski(k7_relat_1(k6_relat_1(X5),X6),X7)
        | ~ v1_relat_1(X7)
        | r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X5),X6)),k2_relat_1(X7)) )
    | ~ spl2_16
    | ~ spl2_27 ),
    inference(resolution,[],[f241,f170])).

fof(f170,plain,
    ( ! [X6,X5] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f240])).

fof(f3090,plain,
    ( spl2_182
    | ~ spl2_7
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f176,f169,f156,f107,f3088])).

fof(f107,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f176,plain,
    ( ! [X10,X9] : k7_relat_1(k6_relat_1(X9),X10) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X10),k6_relat_1(k9_relat_1(k6_relat_1(X9),X10)))
    | ~ spl2_7
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f175,f157])).

fof(f175,plain,
    ( ! [X10,X9] : k7_relat_1(k6_relat_1(X9),X10) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X10),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X9),X10))))
    | ~ spl2_7
    | ~ spl2_16 ),
    inference(resolution,[],[f170,f108])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f2333,plain,
    ( spl2_143
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_45
    | ~ spl2_46
    | ~ spl2_75 ),
    inference(avatar_split_clause,[],[f1096,f994,f436,f432,f152,f146,f83,f2331])).

fof(f146,plain,
    ( spl2_13
  <=> ! [X1,X0] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f152,plain,
    ( spl2_14
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f432,plain,
    ( spl2_45
  <=> ! [X3,X5,X4] : k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f436,plain,
    ( spl2_46
  <=> ! [X7,X8,X6] : k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8)) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f994,plain,
    ( spl2_75
  <=> ! [X5,X4,X6] :
        ( ~ v1_relat_1(X4)
        | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f1096,plain,
    ( ! [X6,X8,X7] : k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8)
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_45
    | ~ spl2_46
    | ~ spl2_75 ),
    inference(backward_demodulation,[],[f437,f1091])).

fof(f1091,plain,
    ( ! [X6,X4,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5) = k8_relat_1(X4,k7_relat_1(k6_relat_1(X6),X5))
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_45
    | ~ spl2_75 ),
    inference(forward_demodulation,[],[f1090,f153])).

fof(f153,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f1090,plain,
    ( ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5)
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_45
    | ~ spl2_75 ),
    inference(forward_demodulation,[],[f1089,f433])).

fof(f433,plain,
    ( ! [X4,X5,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f432])).

fof(f1089,plain,
    ( ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X4),X6))
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_75 ),
    inference(forward_demodulation,[],[f1085,f147])).

fof(f147,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f1085,plain,
    ( ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X4,k6_relat_1(X6)))
    | ~ spl2_1
    | ~ spl2_75 ),
    inference(resolution,[],[f995,f84])).

fof(f995,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_relat_1(X4)
        | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4)) )
    | ~ spl2_75 ),
    inference(avatar_component_clause,[],[f994])).

fof(f437,plain,
    ( ! [X6,X8,X7] : k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8)) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f436])).

fof(f1584,plain,
    ( ~ spl2_109
    | ~ spl2_1
    | ~ spl2_2
    | spl2_43
    | ~ spl2_98 ),
    inference(avatar_split_clause,[],[f1577,f1382,f423,f87,f83,f1581])).

fof(f423,plain,
    ( spl2_43
  <=> k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f1382,plain,
    ( spl2_98
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).

fof(f1577,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_43
    | ~ spl2_98 ),
    inference(backward_demodulation,[],[f425,f1576])).

fof(f1576,plain,
    ( ! [X4,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_98 ),
    inference(forward_demodulation,[],[f1573,f88])).

fof(f1573,plain,
    ( ! [X4,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),X4))
    | ~ spl2_1
    | ~ spl2_98 ),
    inference(resolution,[],[f1383,f84])).

fof(f1383,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) )
    | ~ spl2_98 ),
    inference(avatar_component_clause,[],[f1382])).

fof(f425,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_43 ),
    inference(avatar_component_clause,[],[f423])).

fof(f1384,plain,(
    spl2_98 ),
    inference(avatar_split_clause,[],[f81,f1382])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f61,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f996,plain,
    ( spl2_75
    | ~ spl2_1
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f980,f577,f83,f994])).

fof(f577,plain,
    ( spl2_56
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f980,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_relat_1(X4)
        | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4)) )
    | ~ spl2_1
    | ~ spl2_56 ),
    inference(resolution,[],[f578,f84])).

fof(f578,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) )
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f577])).

fof(f579,plain,(
    spl2_56 ),
    inference(avatar_split_clause,[],[f66,f577])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f438,plain,
    ( spl2_46
    | ~ spl2_10
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f174,f169,f127,f436])).

fof(f127,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f174,plain,
    ( ! [X6,X8,X7] : k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8)) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6))
    | ~ spl2_10
    | ~ spl2_16 ),
    inference(resolution,[],[f170,f128])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f434,plain,
    ( spl2_45
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f173,f169,f131,f432])).

fof(f131,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f173,plain,
    ( ! [X4,X5,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4))
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(resolution,[],[f170,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f426,plain,
    ( ~ spl2_43
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f144,f131,f127,f83,f423])).

fof(f144,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(backward_demodulation,[],[f140,f143])).

fof(f143,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(backward_demodulation,[],[f138,f141])).

fof(f141,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(resolution,[],[f132,f84])).

fof(f138,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(resolution,[],[f128,f84])).

fof(f140,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(backward_demodulation,[],[f80,f138])).

fof(f80,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f47,f79])).

fof(f47,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f45])).

fof(f45,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f355,plain,
    ( spl2_38
    | ~ spl2_24
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f308,f299,f223,f353])).

fof(f223,plain,
    ( spl2_24
  <=> ! [X1,X0] : r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f308,plain,
    ( ! [X10,X11] : k6_relat_1(k9_relat_1(k6_relat_1(X10),X11)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X10),X11)),X10)
    | ~ spl2_24
    | ~ spl2_34 ),
    inference(resolution,[],[f300,f224])).

fof(f224,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X1)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f223])).

fof(f301,plain,
    ( spl2_34
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f296,f244,f152,f87,f83,f299])).

fof(f244,plain,
    ( spl2_28
  <=> ! [X1,X0] :
        ( k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f296,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f295,f153])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f292,f88])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) )
    | ~ spl2_1
    | ~ spl2_28 ),
    inference(resolution,[],[f245,f84])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | k5_relat_1(k6_relat_1(X0),X1) = X1 )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f244])).

fof(f246,plain,(
    spl2_28 ),
    inference(avatar_split_clause,[],[f64,f244])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f242,plain,(
    spl2_27 ),
    inference(avatar_split_clause,[],[f54,f240])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f225,plain,
    ( spl2_24
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f218,f206,f156,f152,f91,f83,f223])).

fof(f206,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)),k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f218,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f217,f157])).

fof(f217,plain,
    ( ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_14
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f216,f153])).

fof(f216,plain,
    ( ! [X0,X1] : r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))),X1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f213,f92])).

fof(f213,plain,
    ( ! [X0,X1] : r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))),k2_relat_1(k6_relat_1(X1)))
    | ~ spl2_1
    | ~ spl2_22 ),
    inference(resolution,[],[f207,f84])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)),k2_relat_1(X0)) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f206])).

fof(f208,plain,
    ( spl2_22
    | ~ spl2_1
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f202,f199,f83,f206])).

fof(f199,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)),k2_relat_1(X0)) )
    | ~ spl2_1
    | ~ spl2_21 ),
    inference(resolution,[],[f200,f84])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f199])).

fof(f201,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f52,f199])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f188,plain,
    ( spl2_19
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f165,f152,f95,f83,f186])).

fof(f95,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f165,plain,
    ( ! [X4,X3] : r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f162,f84])).

fof(f162,plain,
    ( ! [X4,X3] :
        ( r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))
        | ~ v1_relat_1(k6_relat_1(X3)) )
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(superposition,[],[f96,f153])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f171,plain,
    ( spl2_16
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f167,f152,f103,f83,f169])).

fof(f103,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f167,plain,
    ( ! [X6,X5] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f166,f84])).

fof(f166,plain,
    ( ! [X6,X5] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
        | ~ v1_relat_1(k6_relat_1(X5)) )
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f163,f84])).

fof(f163,plain,
    ( ! [X6,X5] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
        | ~ v1_relat_1(k6_relat_1(X6))
        | ~ v1_relat_1(k6_relat_1(X5)) )
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(superposition,[],[f104,f153])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f158,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f149,f135,f83,f156])).

fof(f135,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f149,plain,
    ( ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(resolution,[],[f136,f84])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f154,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f141,f131,f83,f152])).

fof(f148,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f143,f131,f127,f83,f146])).

fof(f137,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f60,f135])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f133,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f59,f131])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f129,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f58,f127])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f109,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f51,f107])).

fof(f51,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f105,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f68,f103])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f97,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f62,f95])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f93,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f50,f91])).

fof(f50,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f89,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f49,f87])).

fof(f49,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f48,f83])).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.41  % (29501)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (29488)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (29502)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (29495)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (29494)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (29492)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (29489)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (29490)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (29497)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (29500)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (29496)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (29505)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (29499)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (29503)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (29493)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (29499)Refutation not found, incomplete strategy% (29499)------------------------------
% 0.20/0.50  % (29499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29499)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29499)Memory used [KB]: 10618
% 0.20/0.50  % (29499)Time elapsed: 0.091 s
% 0.20/0.50  % (29499)------------------------------
% 0.20/0.50  % (29499)------------------------------
% 0.20/0.50  % (29498)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.51  % (29491)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.52  % (29504)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.55  % (29495)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f4297,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f85,f89,f93,f97,f105,f109,f129,f133,f137,f148,f154,f158,f171,f188,f201,f208,f225,f242,f246,f301,f355,f426,f434,f438,f579,f996,f1384,f1584,f2333,f3090,f3094,f3132,f3632,f3677,f3993,f4220])).
% 0.20/0.55  fof(f4220,plain,(
% 0.20/0.55    ~spl2_2 | spl2_109 | ~spl2_198),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f4219])).
% 0.20/0.55  fof(f4219,plain,(
% 0.20/0.55    $false | (~spl2_2 | spl2_109 | ~spl2_198)),
% 0.20/0.55    inference(subsumption_resolution,[],[f4199,f3992])).
% 0.20/0.55  fof(f3992,plain,(
% 0.20/0.55    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k9_relat_1(k6_relat_1(X2),X3))) ) | ~spl2_198),
% 0.20/0.55    inference(avatar_component_clause,[],[f3991])).
% 0.20/0.55  fof(f3991,plain,(
% 0.20/0.55    spl2_198 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k9_relat_1(k6_relat_1(X2),X3))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_198])])).
% 0.20/0.55  fof(f4199,plain,(
% 0.20/0.55    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k9_relat_1(k6_relat_1(sK0),sK1)) | (~spl2_2 | spl2_109 | ~spl2_198)),
% 0.20/0.55    inference(backward_demodulation,[],[f1583,f4002])).
% 0.20/0.55  fof(f4002,plain,(
% 0.20/0.55    ( ! [X2,X3] : (k9_relat_1(k6_relat_1(X2),X3) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ) | (~spl2_2 | ~spl2_198)),
% 0.20/0.55    inference(superposition,[],[f88,f3992])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f87])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    spl2_2 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.55  fof(f1583,plain,(
% 0.20/0.55    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | spl2_109),
% 0.20/0.55    inference(avatar_component_clause,[],[f1581])).
% 0.20/0.55  fof(f1581,plain,(
% 0.20/0.55    spl2_109 <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).
% 0.20/0.55  fof(f3993,plain,(
% 0.20/0.55    spl2_198 | ~spl2_34 | ~spl2_184 | ~spl2_195),
% 0.20/0.55    inference(avatar_split_clause,[],[f3688,f3675,f3130,f299,f3991])).
% 0.20/0.55  fof(f299,plain,(
% 0.20/0.55    spl2_34 <=> ! [X1,X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.55  fof(f3130,plain,(
% 0.20/0.55    spl2_184 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_184])])).
% 0.20/0.55  fof(f3675,plain,(
% 0.20/0.55    spl2_195 <=> ! [X3,X2] : r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_195])])).
% 0.20/0.55  fof(f3688,plain,(
% 0.20/0.55    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k9_relat_1(k6_relat_1(X2),X3))) ) | (~spl2_34 | ~spl2_184 | ~spl2_195)),
% 0.20/0.55    inference(forward_demodulation,[],[f3679,f3131])).
% 0.20/0.55  fof(f3131,plain,(
% 0.20/0.55    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)) ) | ~spl2_184),
% 0.20/0.55    inference(avatar_component_clause,[],[f3130])).
% 0.20/0.55  fof(f3679,plain,(
% 0.20/0.55    ( ! [X2,X3] : (k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)) ) | (~spl2_34 | ~spl2_195)),
% 0.20/0.55    inference(resolution,[],[f3676,f300])).
% 0.20/0.55  fof(f300,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_34),
% 0.20/0.55    inference(avatar_component_clause,[],[f299])).
% 0.20/0.55  fof(f3676,plain,(
% 0.20/0.55    ( ! [X2,X3] : (r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X3)) ) | ~spl2_195),
% 0.20/0.55    inference(avatar_component_clause,[],[f3675])).
% 0.20/0.55  fof(f3677,plain,(
% 0.20/0.55    spl2_195 | ~spl2_19 | ~spl2_194),
% 0.20/0.55    inference(avatar_split_clause,[],[f3634,f3630,f186,f3675])).
% 0.20/0.55  fof(f186,plain,(
% 0.20/0.55    spl2_19 <=> ! [X3,X4] : r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.55  fof(f3630,plain,(
% 0.20/0.55    spl2_194 <=> ! [X5,X4,X6] : (r1_tarski(k9_relat_1(k6_relat_1(X4),X5),X6) | ~r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X6)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_194])])).
% 0.20/0.55  fof(f3634,plain,(
% 0.20/0.55    ( ! [X2,X3] : (r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X3)) ) | (~spl2_19 | ~spl2_194)),
% 0.20/0.55    inference(resolution,[],[f3631,f187])).
% 0.20/0.55  fof(f187,plain,(
% 0.20/0.55    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))) ) | ~spl2_19),
% 0.20/0.55    inference(avatar_component_clause,[],[f186])).
% 0.20/0.55  fof(f3631,plain,(
% 0.20/0.55    ( ! [X6,X4,X5] : (~r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X6)) | r1_tarski(k9_relat_1(k6_relat_1(X4),X5),X6)) ) | ~spl2_194),
% 0.20/0.55    inference(avatar_component_clause,[],[f3630])).
% 0.20/0.55  fof(f3632,plain,(
% 0.20/0.55    spl2_194 | ~spl2_1 | ~spl2_3 | ~spl2_183),
% 0.20/0.55    inference(avatar_split_clause,[],[f3626,f3092,f91,f83,f3630])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    spl2_1 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    spl2_3 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.55  fof(f3092,plain,(
% 0.20/0.55    spl2_183 <=> ! [X5,X7,X6] : (r1_tarski(k9_relat_1(k6_relat_1(X5),X6),k2_relat_1(X7)) | ~r1_tarski(k7_relat_1(k6_relat_1(X5),X6),X7) | ~v1_relat_1(X7))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_183])])).
% 0.20/0.55  fof(f3626,plain,(
% 0.20/0.55    ( ! [X6,X4,X5] : (r1_tarski(k9_relat_1(k6_relat_1(X4),X5),X6) | ~r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X6))) ) | (~spl2_1 | ~spl2_3 | ~spl2_183)),
% 0.20/0.55    inference(forward_demodulation,[],[f3623,f92])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f91])).
% 0.20/0.55  fof(f3623,plain,(
% 0.20/0.55    ( ! [X6,X4,X5] : (~r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X6)) | r1_tarski(k9_relat_1(k6_relat_1(X4),X5),k2_relat_1(k6_relat_1(X6)))) ) | (~spl2_1 | ~spl2_183)),
% 0.20/0.55    inference(resolution,[],[f3093,f84])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f83])).
% 0.20/0.55  fof(f3093,plain,(
% 0.20/0.55    ( ! [X6,X7,X5] : (~v1_relat_1(X7) | ~r1_tarski(k7_relat_1(k6_relat_1(X5),X6),X7) | r1_tarski(k9_relat_1(k6_relat_1(X5),X6),k2_relat_1(X7))) ) | ~spl2_183),
% 0.20/0.55    inference(avatar_component_clause,[],[f3092])).
% 0.20/0.55  fof(f3132,plain,(
% 0.20/0.55    spl2_184 | ~spl2_38 | ~spl2_143 | ~spl2_182),
% 0.20/0.55    inference(avatar_split_clause,[],[f3127,f3088,f2331,f353,f3130])).
% 0.20/0.55  fof(f353,plain,(
% 0.20/0.55    spl2_38 <=> ! [X11,X10] : k6_relat_1(k9_relat_1(k6_relat_1(X10),X11)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X10),X11)),X10)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.20/0.55  fof(f2331,plain,(
% 0.20/0.55    spl2_143 <=> ! [X7,X8,X6] : k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_143])])).
% 0.20/0.55  fof(f3088,plain,(
% 0.20/0.55    spl2_182 <=> ! [X9,X10] : k7_relat_1(k6_relat_1(X9),X10) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X10),k6_relat_1(k9_relat_1(k6_relat_1(X9),X10)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_182])])).
% 0.20/0.55  fof(f3127,plain,(
% 0.20/0.55    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X3)) ) | (~spl2_38 | ~spl2_143 | ~spl2_182)),
% 0.20/0.55    inference(forward_demodulation,[],[f3109,f354])).
% 0.20/0.55  fof(f354,plain,(
% 0.20/0.55    ( ! [X10,X11] : (k6_relat_1(k9_relat_1(k6_relat_1(X10),X11)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X10),X11)),X10)) ) | ~spl2_38),
% 0.20/0.55    inference(avatar_component_clause,[],[f353])).
% 0.20/0.55  fof(f3109,plain,(
% 0.20/0.55    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X2),X3)),X2),X3)) ) | (~spl2_143 | ~spl2_182)),
% 0.20/0.55    inference(superposition,[],[f3089,f2332])).
% 0.20/0.55  fof(f2332,plain,(
% 0.20/0.55    ( ! [X6,X8,X7] : (k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8)) ) | ~spl2_143),
% 0.20/0.55    inference(avatar_component_clause,[],[f2331])).
% 0.20/0.55  fof(f3089,plain,(
% 0.20/0.55    ( ! [X10,X9] : (k7_relat_1(k6_relat_1(X9),X10) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X10),k6_relat_1(k9_relat_1(k6_relat_1(X9),X10)))) ) | ~spl2_182),
% 0.20/0.55    inference(avatar_component_clause,[],[f3088])).
% 0.20/0.55  fof(f3094,plain,(
% 0.20/0.55    spl2_183 | ~spl2_15 | ~spl2_16 | ~spl2_27),
% 0.20/0.55    inference(avatar_split_clause,[],[f281,f240,f169,f156,f3092])).
% 0.20/0.55  fof(f156,plain,(
% 0.20/0.55    spl2_15 <=> ! [X1,X0] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.55  fof(f169,plain,(
% 0.20/0.55    spl2_16 <=> ! [X5,X6] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.55  fof(f240,plain,(
% 0.20/0.55    spl2_27 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.20/0.55  fof(f281,plain,(
% 0.20/0.55    ( ! [X6,X7,X5] : (r1_tarski(k9_relat_1(k6_relat_1(X5),X6),k2_relat_1(X7)) | ~r1_tarski(k7_relat_1(k6_relat_1(X5),X6),X7) | ~v1_relat_1(X7)) ) | (~spl2_15 | ~spl2_16 | ~spl2_27)),
% 0.20/0.55    inference(forward_demodulation,[],[f279,f157])).
% 0.20/0.55  fof(f157,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f156])).
% 0.20/0.55  fof(f279,plain,(
% 0.20/0.55    ( ! [X6,X7,X5] : (~r1_tarski(k7_relat_1(k6_relat_1(X5),X6),X7) | ~v1_relat_1(X7) | r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X5),X6)),k2_relat_1(X7))) ) | (~spl2_16 | ~spl2_27)),
% 0.20/0.55    inference(resolution,[],[f241,f170])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))) ) | ~spl2_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f169])).
% 0.20/0.55  fof(f241,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) ) | ~spl2_27),
% 0.20/0.55    inference(avatar_component_clause,[],[f240])).
% 0.20/0.55  fof(f3090,plain,(
% 0.20/0.55    spl2_182 | ~spl2_7 | ~spl2_15 | ~spl2_16),
% 0.20/0.55    inference(avatar_split_clause,[],[f176,f169,f156,f107,f3088])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    spl2_7 <=> ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.55  fof(f176,plain,(
% 0.20/0.55    ( ! [X10,X9] : (k7_relat_1(k6_relat_1(X9),X10) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X10),k6_relat_1(k9_relat_1(k6_relat_1(X9),X10)))) ) | (~spl2_7 | ~spl2_15 | ~spl2_16)),
% 0.20/0.55    inference(forward_demodulation,[],[f175,f157])).
% 0.20/0.55  fof(f175,plain,(
% 0.20/0.55    ( ! [X10,X9] : (k7_relat_1(k6_relat_1(X9),X10) = k5_relat_1(k7_relat_1(k6_relat_1(X9),X10),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X9),X10))))) ) | (~spl2_7 | ~spl2_16)),
% 0.20/0.55    inference(resolution,[],[f170,f108])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) ) | ~spl2_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f107])).
% 0.20/0.55  fof(f2333,plain,(
% 0.20/0.55    spl2_143 | ~spl2_1 | ~spl2_13 | ~spl2_14 | ~spl2_45 | ~spl2_46 | ~spl2_75),
% 0.20/0.55    inference(avatar_split_clause,[],[f1096,f994,f436,f432,f152,f146,f83,f2331])).
% 0.20/0.55  fof(f146,plain,(
% 0.20/0.55    spl2_13 <=> ! [X1,X0] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.55  fof(f152,plain,(
% 0.20/0.55    spl2_14 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.55  fof(f432,plain,(
% 0.20/0.55    spl2_45 <=> ! [X3,X5,X4] : k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.20/0.55  fof(f436,plain,(
% 0.20/0.55    spl2_46 <=> ! [X7,X8,X6] : k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8)) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.20/0.55  fof(f994,plain,(
% 0.20/0.55    spl2_75 <=> ! [X5,X4,X6] : (~v1_relat_1(X4) | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 0.20/0.55  fof(f1096,plain,(
% 0.20/0.55    ( ! [X6,X8,X7] : (k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8)) ) | (~spl2_1 | ~spl2_13 | ~spl2_14 | ~spl2_45 | ~spl2_46 | ~spl2_75)),
% 0.20/0.55    inference(backward_demodulation,[],[f437,f1091])).
% 0.20/0.55  fof(f1091,plain,(
% 0.20/0.55    ( ! [X6,X4,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5) = k8_relat_1(X4,k7_relat_1(k6_relat_1(X6),X5))) ) | (~spl2_1 | ~spl2_13 | ~spl2_14 | ~spl2_45 | ~spl2_75)),
% 0.20/0.55    inference(forward_demodulation,[],[f1090,f153])).
% 0.20/0.55  fof(f153,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f152])).
% 0.20/0.55  fof(f1090,plain,(
% 0.20/0.55    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5)) ) | (~spl2_1 | ~spl2_13 | ~spl2_45 | ~spl2_75)),
% 0.20/0.55    inference(forward_demodulation,[],[f1089,f433])).
% 0.20/0.55  fof(f433,plain,(
% 0.20/0.55    ( ! [X4,X5,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4))) ) | ~spl2_45),
% 0.20/0.55    inference(avatar_component_clause,[],[f432])).
% 0.20/0.55  fof(f1089,plain,(
% 0.20/0.55    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X4),X6))) ) | (~spl2_1 | ~spl2_13 | ~spl2_75)),
% 0.20/0.55    inference(forward_demodulation,[],[f1085,f147])).
% 0.20/0.55  fof(f147,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f146])).
% 0.20/0.55  fof(f1085,plain,(
% 0.20/0.55    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X4,k6_relat_1(X6)))) ) | (~spl2_1 | ~spl2_75)),
% 0.20/0.55    inference(resolution,[],[f995,f84])).
% 0.20/0.55  fof(f995,plain,(
% 0.20/0.55    ( ! [X6,X4,X5] : (~v1_relat_1(X4) | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4))) ) | ~spl2_75),
% 0.20/0.55    inference(avatar_component_clause,[],[f994])).
% 0.20/0.55  fof(f437,plain,(
% 0.20/0.55    ( ! [X6,X8,X7] : (k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8)) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6))) ) | ~spl2_46),
% 0.20/0.55    inference(avatar_component_clause,[],[f436])).
% 0.20/0.55  fof(f1584,plain,(
% 0.20/0.55    ~spl2_109 | ~spl2_1 | ~spl2_2 | spl2_43 | ~spl2_98),
% 0.20/0.55    inference(avatar_split_clause,[],[f1577,f1382,f423,f87,f83,f1581])).
% 0.20/0.55  fof(f423,plain,(
% 0.20/0.55    spl2_43 <=> k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.20/0.55  fof(f1382,plain,(
% 0.20/0.55    spl2_98 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).
% 0.20/0.55  fof(f1577,plain,(
% 0.20/0.55    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | (~spl2_1 | ~spl2_2 | spl2_43 | ~spl2_98)),
% 0.20/0.55    inference(backward_demodulation,[],[f425,f1576])).
% 0.20/0.55  fof(f1576,plain,(
% 0.20/0.55    ( ! [X4,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) ) | (~spl2_1 | ~spl2_2 | ~spl2_98)),
% 0.20/0.55    inference(forward_demodulation,[],[f1573,f88])).
% 0.20/0.55  fof(f1573,plain,(
% 0.20/0.55    ( ! [X4,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),X4))) ) | (~spl2_1 | ~spl2_98)),
% 0.20/0.55    inference(resolution,[],[f1383,f84])).
% 0.20/0.55  fof(f1383,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) ) | ~spl2_98),
% 0.20/0.55    inference(avatar_component_clause,[],[f1382])).
% 0.20/0.55  fof(f425,plain,(
% 0.20/0.55    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_43),
% 0.20/0.55    inference(avatar_component_clause,[],[f423])).
% 0.20/0.55  fof(f1384,plain,(
% 0.20/0.55    spl2_98),
% 0.20/0.55    inference(avatar_split_clause,[],[f81,f1382])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f61,f79])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f56,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f57,f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f69,f76])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f70,f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f71,f74])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f72,f73])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.55  fof(f996,plain,(
% 0.20/0.55    spl2_75 | ~spl2_1 | ~spl2_56),
% 0.20/0.55    inference(avatar_split_clause,[],[f980,f577,f83,f994])).
% 0.20/0.55  fof(f577,plain,(
% 0.20/0.55    spl2_56 <=> ! [X1,X0,X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 0.20/0.55  fof(f980,plain,(
% 0.20/0.55    ( ! [X6,X4,X5] : (~v1_relat_1(X4) | k8_relat_1(X5,k5_relat_1(k6_relat_1(X6),X4)) = k5_relat_1(k6_relat_1(X6),k8_relat_1(X5,X4))) ) | (~spl2_1 | ~spl2_56)),
% 0.20/0.55    inference(resolution,[],[f578,f84])).
% 0.20/0.55  fof(f578,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))) ) | ~spl2_56),
% 0.20/0.55    inference(avatar_component_clause,[],[f577])).
% 0.20/0.55  fof(f579,plain,(
% 0.20/0.55    spl2_56),
% 0.20/0.55    inference(avatar_split_clause,[],[f66,f577])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 0.20/0.55  fof(f438,plain,(
% 0.20/0.55    spl2_46 | ~spl2_10 | ~spl2_16),
% 0.20/0.55    inference(avatar_split_clause,[],[f174,f169,f127,f436])).
% 0.20/0.55  fof(f127,plain,(
% 0.20/0.55    spl2_10 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.55  fof(f174,plain,(
% 0.20/0.55    ( ! [X6,X8,X7] : (k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8)) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6))) ) | (~spl2_10 | ~spl2_16)),
% 0.20/0.55    inference(resolution,[],[f170,f128])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_10),
% 0.20/0.55    inference(avatar_component_clause,[],[f127])).
% 0.20/0.55  fof(f434,plain,(
% 0.20/0.55    spl2_45 | ~spl2_11 | ~spl2_16),
% 0.20/0.55    inference(avatar_split_clause,[],[f173,f169,f131,f432])).
% 0.20/0.55  fof(f131,plain,(
% 0.20/0.55    spl2_11 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.55  fof(f173,plain,(
% 0.20/0.55    ( ! [X4,X5,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4))) ) | (~spl2_11 | ~spl2_16)),
% 0.20/0.55    inference(resolution,[],[f170,f132])).
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f131])).
% 0.20/0.55  fof(f426,plain,(
% 0.20/0.55    ~spl2_43 | ~spl2_1 | ~spl2_10 | ~spl2_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f144,f131,f127,f83,f423])).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | (~spl2_1 | ~spl2_10 | ~spl2_11)),
% 0.20/0.55    inference(backward_demodulation,[],[f140,f143])).
% 0.20/0.55  fof(f143,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_10 | ~spl2_11)),
% 0.20/0.55    inference(backward_demodulation,[],[f138,f141])).
% 0.20/0.55  fof(f141,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_11)),
% 0.20/0.55    inference(resolution,[],[f132,f84])).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_10)),
% 0.20/0.55    inference(resolution,[],[f128,f84])).
% 0.20/0.55  fof(f140,plain,(
% 0.20/0.55    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) | (~spl2_1 | ~spl2_10)),
% 0.20/0.55    inference(backward_demodulation,[],[f80,f138])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 0.20/0.55    inference(definition_unfolding,[],[f47,f79])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f25])).
% 0.20/0.56  fof(f25,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.56    inference(negated_conjecture,[],[f24])).
% 0.20/0.56  fof(f24,conjecture,(
% 0.20/0.56    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.56  fof(f355,plain,(
% 0.20/0.56    spl2_38 | ~spl2_24 | ~spl2_34),
% 0.20/0.56    inference(avatar_split_clause,[],[f308,f299,f223,f353])).
% 0.20/0.56  fof(f223,plain,(
% 0.20/0.56    spl2_24 <=> ! [X1,X0] : r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.20/0.56  fof(f308,plain,(
% 0.20/0.56    ( ! [X10,X11] : (k6_relat_1(k9_relat_1(k6_relat_1(X10),X11)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X10),X11)),X10)) ) | (~spl2_24 | ~spl2_34)),
% 0.20/0.56    inference(resolution,[],[f300,f224])).
% 0.20/0.56  fof(f224,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X1)) ) | ~spl2_24),
% 0.20/0.56    inference(avatar_component_clause,[],[f223])).
% 0.20/0.56  fof(f301,plain,(
% 0.20/0.56    spl2_34 | ~spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_28),
% 0.20/0.56    inference(avatar_split_clause,[],[f296,f244,f152,f87,f83,f299])).
% 0.20/0.56  fof(f244,plain,(
% 0.20/0.56    spl2_28 <=> ! [X1,X0] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.20/0.56  fof(f296,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1)) ) | (~spl2_1 | ~spl2_2 | ~spl2_14 | ~spl2_28)),
% 0.20/0.56    inference(forward_demodulation,[],[f295,f153])).
% 0.20/0.56  fof(f295,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl2_1 | ~spl2_2 | ~spl2_28)),
% 0.20/0.56    inference(forward_demodulation,[],[f292,f88])).
% 0.20/0.56  fof(f292,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl2_1 | ~spl2_28)),
% 0.20/0.56    inference(resolution,[],[f245,f84])).
% 0.20/0.56  fof(f245,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) ) | ~spl2_28),
% 0.20/0.56    inference(avatar_component_clause,[],[f244])).
% 0.20/0.56  fof(f246,plain,(
% 0.20/0.56    spl2_28),
% 0.20/0.56    inference(avatar_split_clause,[],[f64,f244])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(flattening,[],[f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,axiom,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.20/0.56  fof(f242,plain,(
% 0.20/0.56    spl2_27),
% 0.20/0.56    inference(avatar_split_clause,[],[f54,f240])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.56  fof(f225,plain,(
% 0.20/0.56    spl2_24 | ~spl2_1 | ~spl2_3 | ~spl2_14 | ~spl2_15 | ~spl2_22),
% 0.20/0.56    inference(avatar_split_clause,[],[f218,f206,f156,f152,f91,f83,f223])).
% 0.20/0.56  fof(f206,plain,(
% 0.20/0.56    spl2_22 <=> ! [X1,X0] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)),k2_relat_1(X0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.20/0.56  fof(f218,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X1)) ) | (~spl2_1 | ~spl2_3 | ~spl2_14 | ~spl2_15 | ~spl2_22)),
% 0.20/0.56    inference(forward_demodulation,[],[f217,f157])).
% 0.20/0.56  fof(f217,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X1)) ) | (~spl2_1 | ~spl2_3 | ~spl2_14 | ~spl2_22)),
% 0.20/0.56    inference(forward_demodulation,[],[f216,f153])).
% 0.20/0.56  fof(f216,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))),X1)) ) | (~spl2_1 | ~spl2_3 | ~spl2_22)),
% 0.20/0.56    inference(forward_demodulation,[],[f213,f92])).
% 0.20/0.56  fof(f213,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))),k2_relat_1(k6_relat_1(X1)))) ) | (~spl2_1 | ~spl2_22)),
% 0.20/0.56    inference(resolution,[],[f207,f84])).
% 0.20/0.56  fof(f207,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)),k2_relat_1(X0))) ) | ~spl2_22),
% 0.20/0.56    inference(avatar_component_clause,[],[f206])).
% 0.20/0.56  fof(f208,plain,(
% 0.20/0.56    spl2_22 | ~spl2_1 | ~spl2_21),
% 0.20/0.56    inference(avatar_split_clause,[],[f202,f199,f83,f206])).
% 0.20/0.56  fof(f199,plain,(
% 0.20/0.56    spl2_21 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.56  fof(f202,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)),k2_relat_1(X0))) ) | (~spl2_1 | ~spl2_21)),
% 0.20/0.56    inference(resolution,[],[f200,f84])).
% 0.20/0.56  fof(f200,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))) ) | ~spl2_21),
% 0.20/0.56    inference(avatar_component_clause,[],[f199])).
% 0.20/0.56  fof(f201,plain,(
% 0.20/0.56    spl2_21),
% 0.20/0.56    inference(avatar_split_clause,[],[f52,f199])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 0.20/0.56  fof(f188,plain,(
% 0.20/0.56    spl2_19 | ~spl2_1 | ~spl2_4 | ~spl2_14),
% 0.20/0.56    inference(avatar_split_clause,[],[f165,f152,f95,f83,f186])).
% 0.20/0.56  fof(f95,plain,(
% 0.20/0.56    spl2_4 <=> ! [X1,X0] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.56  fof(f165,plain,(
% 0.20/0.56    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))) ) | (~spl2_1 | ~spl2_4 | ~spl2_14)),
% 0.20/0.56    inference(subsumption_resolution,[],[f162,f84])).
% 0.20/0.56  fof(f162,plain,(
% 0.20/0.56    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X3))) ) | (~spl2_4 | ~spl2_14)),
% 0.20/0.56    inference(superposition,[],[f96,f153])).
% 0.20/0.56  fof(f96,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) ) | ~spl2_4),
% 0.20/0.56    inference(avatar_component_clause,[],[f95])).
% 0.20/0.56  fof(f171,plain,(
% 0.20/0.56    spl2_16 | ~spl2_1 | ~spl2_6 | ~spl2_14),
% 0.20/0.56    inference(avatar_split_clause,[],[f167,f152,f103,f83,f169])).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    spl2_6 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.56  fof(f167,plain,(
% 0.20/0.56    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))) ) | (~spl2_1 | ~spl2_6 | ~spl2_14)),
% 0.20/0.56    inference(subsumption_resolution,[],[f166,f84])).
% 0.20/0.56  fof(f166,plain,(
% 0.20/0.56    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X5))) ) | (~spl2_1 | ~spl2_6 | ~spl2_14)),
% 0.20/0.56    inference(subsumption_resolution,[],[f163,f84])).
% 0.20/0.56  fof(f163,plain,(
% 0.20/0.56    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(k6_relat_1(X5))) ) | (~spl2_6 | ~spl2_14)),
% 0.20/0.56    inference(superposition,[],[f104,f153])).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_6),
% 0.20/0.56    inference(avatar_component_clause,[],[f103])).
% 0.20/0.56  fof(f158,plain,(
% 0.20/0.56    spl2_15 | ~spl2_1 | ~spl2_12),
% 0.20/0.56    inference(avatar_split_clause,[],[f149,f135,f83,f156])).
% 0.20/0.56  fof(f135,plain,(
% 0.20/0.56    spl2_12 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.56  fof(f149,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_12)),
% 0.20/0.56    inference(resolution,[],[f136,f84])).
% 0.20/0.56  fof(f136,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_12),
% 0.20/0.56    inference(avatar_component_clause,[],[f135])).
% 0.20/0.56  fof(f154,plain,(
% 0.20/0.56    spl2_14 | ~spl2_1 | ~spl2_11),
% 0.20/0.56    inference(avatar_split_clause,[],[f141,f131,f83,f152])).
% 0.20/0.56  fof(f148,plain,(
% 0.20/0.56    spl2_13 | ~spl2_1 | ~spl2_10 | ~spl2_11),
% 0.20/0.56    inference(avatar_split_clause,[],[f143,f131,f127,f83,f146])).
% 0.20/0.56  fof(f137,plain,(
% 0.20/0.56    spl2_12),
% 0.20/0.56    inference(avatar_split_clause,[],[f60,f135])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,axiom,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.56  fof(f133,plain,(
% 0.20/0.56    spl2_11),
% 0.20/0.56    inference(avatar_split_clause,[],[f59,f131])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f23])).
% 0.20/0.56  fof(f23,axiom,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.56  fof(f129,plain,(
% 0.20/0.56    spl2_10),
% 0.20/0.56    inference(avatar_split_clause,[],[f58,f127])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,axiom,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.56  fof(f109,plain,(
% 0.20/0.56    spl2_7),
% 0.20/0.56    inference(avatar_split_clause,[],[f51,f107])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f21])).
% 0.20/0.56  fof(f21,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    spl2_6),
% 0.20/0.56    inference(avatar_split_clause,[],[f68,f103])).
% 0.20/0.56  fof(f68,plain,(
% 0.20/0.56    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    spl2_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f62,f95])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,axiom,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    spl2_3),
% 0.20/0.56    inference(avatar_split_clause,[],[f50,f91])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,axiom,(
% 0.20/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.56  fof(f89,plain,(
% 0.20/0.56    spl2_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f49,f87])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    spl2_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f48,f83])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (29495)------------------------------
% 0.20/0.56  % (29495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (29495)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (29495)Memory used [KB]: 9338
% 0.20/0.56  % (29495)Time elapsed: 0.147 s
% 0.20/0.56  % (29495)------------------------------
% 0.20/0.56  % (29495)------------------------------
% 1.71/0.57  % (29487)Success in time 0.211 s
%------------------------------------------------------------------------------
