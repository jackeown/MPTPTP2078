%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:57 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 296 expanded)
%              Number of leaves         :   42 ( 147 expanded)
%              Depth                    :    9
%              Number of atoms          :  363 ( 647 expanded)
%              Number of equality atoms :  119 ( 246 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5638,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f49,f53,f66,f72,f80,f92,f113,f131,f157,f167,f191,f195,f199,f203,f287,f291,f334,f360,f586,f949,f953,f1294,f1397,f1859,f3910,f5486,f5604])).

fof(f5604,plain,
    ( ~ spl2_17
    | ~ spl2_23
    | ~ spl2_25
    | spl2_56
    | ~ spl2_64
    | ~ spl2_124 ),
    inference(avatar_contradiction_clause,[],[f5603])).

fof(f5603,plain,
    ( $false
    | ~ spl2_17
    | ~ spl2_23
    | ~ spl2_25
    | spl2_56
    | ~ spl2_64
    | ~ spl2_124 ),
    inference(subsumption_resolution,[],[f5602,f156])).

fof(f156,plain,
    ( ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl2_17
  <=> ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f5602,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_23
    | ~ spl2_25
    | spl2_56
    | ~ spl2_64
    | ~ spl2_124 ),
    inference(forward_demodulation,[],[f5601,f1858])).

fof(f1858,plain,
    ( ! [X6,X7,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k2_xboole_0(X5,X7)))
    | ~ spl2_64 ),
    inference(avatar_component_clause,[],[f1857])).

fof(f1857,plain,
    ( spl2_64
  <=> ! [X5,X7,X6] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k2_xboole_0(X5,X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f5601,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_23
    | ~ spl2_25
    | spl2_56
    | ~ spl2_124 ),
    inference(forward_demodulation,[],[f5596,f194])).

fof(f194,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl2_23
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f5596,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_25
    | spl2_56
    | ~ spl2_124 ),
    inference(backward_demodulation,[],[f1396,f5500])).

fof(f5500,plain,
    ( ! [X43,X41,X42] : k4_xboole_0(X43,k2_xboole_0(X41,X42)) = k4_xboole_0(k2_xboole_0(X43,k4_xboole_0(X42,X41)),k2_xboole_0(X41,X42))
    | ~ spl2_25
    | ~ spl2_124 ),
    inference(superposition,[],[f5485,f202])).

fof(f202,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl2_25
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f5485,plain,
    ( ! [X35,X36,X34] : k4_xboole_0(X36,X34) = k4_xboole_0(k2_xboole_0(X36,k4_xboole_0(X34,X35)),X34)
    | ~ spl2_124 ),
    inference(avatar_component_clause,[],[f5484])).

fof(f5484,plain,
    ( spl2_124
  <=> ! [X34,X36,X35] : k4_xboole_0(X36,X34) = k4_xboole_0(k2_xboole_0(X36,k4_xboole_0(X34,X35)),X34) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_124])])).

fof(f1396,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_56 ),
    inference(avatar_component_clause,[],[f1394])).

fof(f1394,plain,
    ( spl2_56
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f5486,plain,
    ( spl2_124
    | ~ spl2_46
    | ~ spl2_100 ),
    inference(avatar_split_clause,[],[f5363,f3908,f947,f5484])).

fof(f947,plain,
    ( spl2_46
  <=> ! [X11,X10] : k2_xboole_0(k4_xboole_0(X10,X11),X10) = X10 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f3908,plain,
    ( spl2_100
  <=> ! [X5,X4,X6] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).

fof(f5363,plain,
    ( ! [X35,X36,X34] : k4_xboole_0(X36,X34) = k4_xboole_0(k2_xboole_0(X36,k4_xboole_0(X34,X35)),X34)
    | ~ spl2_46
    | ~ spl2_100 ),
    inference(superposition,[],[f3909,f948])).

fof(f948,plain,
    ( ! [X10,X11] : k2_xboole_0(k4_xboole_0(X10,X11),X10) = X10
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f947])).

fof(f3909,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6))
    | ~ spl2_100 ),
    inference(avatar_component_clause,[],[f3908])).

fof(f3910,plain,
    ( spl2_100
    | ~ spl2_15
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f315,f193,f129,f3908])).

fof(f129,plain,
    ( spl2_15
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f315,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6))
    | ~ spl2_15
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f294,f194])).

fof(f294,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6)
    | ~ spl2_15
    | ~ spl2_23 ),
    inference(superposition,[],[f194,f130])).

fof(f130,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f1859,plain,
    ( spl2_64
    | ~ spl2_23
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f1463,f1292,f193,f1857])).

fof(f1292,plain,
    ( spl2_53
  <=> ! [X9,X11,X10] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f1463,plain,
    ( ! [X6,X7,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k2_xboole_0(X5,X7)))
    | ~ spl2_23
    | ~ spl2_53 ),
    inference(superposition,[],[f1293,f194])).

fof(f1293,plain,
    ( ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,X11))
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f1292])).

fof(f1397,plain,
    ( ~ spl2_56
    | ~ spl2_23
    | ~ spl2_29
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f750,f584,f285,f193,f1394])).

fof(f285,plain,
    ( spl2_29
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f584,plain,
    ( spl2_39
  <=> ! [X13,X12] : k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = X13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f750,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_23
    | ~ spl2_29
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f749,f286])).

fof(f286,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f285])).

fof(f749,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
    | ~ spl2_23
    | ~ spl2_39 ),
    inference(backward_demodulation,[],[f34,f720])).

fof(f720,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(k4_xboole_0(X4,X5),X6))
    | ~ spl2_23
    | ~ spl2_39 ),
    inference(superposition,[],[f194,f585])).

fof(f585,plain,
    ( ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = X13
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f584])).

fof(f34,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f20,f26,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f1294,plain,
    ( spl2_53
    | ~ spl2_1
    | ~ spl2_23
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f1026,f951,f193,f39,f1292])).

fof(f39,plain,
    ( spl2_1
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f951,plain,
    ( spl2_47
  <=> ! [X16,X15] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X16),X15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f1026,plain,
    ( ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,X11))
    | ~ spl2_1
    | ~ spl2_23
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f1008,f40])).

fof(f40,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f1008,plain,
    ( ! [X10,X11,X9] : k4_xboole_0(k1_xboole_0,X11) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,X11))
    | ~ spl2_23
    | ~ spl2_47 ),
    inference(superposition,[],[f194,f952])).

fof(f952,plain,
    ( ! [X15,X16] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X16),X15)
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f951])).

fof(f953,plain,
    ( spl2_47
    | ~ spl2_24
    | ~ spl2_29
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f900,f289,f285,f197,f951])).

fof(f197,plain,
    ( spl2_24
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f289,plain,
    ( spl2_30
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f900,plain,
    ( ! [X15,X16] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X16),X15)
    | ~ spl2_24
    | ~ spl2_29
    | ~ spl2_30 ),
    inference(backward_demodulation,[],[f440,f858])).

fof(f858,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_29
    | ~ spl2_30 ),
    inference(superposition,[],[f290,f286])).

fof(f290,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f289])).

fof(f440,plain,
    ( ! [X15,X16] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X16,k4_xboole_0(X16,X15))),X15)
    | ~ spl2_24
    | ~ spl2_29 ),
    inference(superposition,[],[f198,f286])).

fof(f198,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f197])).

fof(f949,plain,
    ( spl2_46
    | ~ spl2_22
    | ~ spl2_29
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f899,f289,f285,f189,f947])).

fof(f189,plain,
    ( spl2_22
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f899,plain,
    ( ! [X10,X11] : k2_xboole_0(k4_xboole_0(X10,X11),X10) = X10
    | ~ spl2_22
    | ~ spl2_29
    | ~ spl2_30 ),
    inference(backward_demodulation,[],[f438,f858])).

fof(f438,plain,
    ( ! [X10,X11] : k2_xboole_0(k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10))),X10) = X10
    | ~ spl2_22
    | ~ spl2_29 ),
    inference(superposition,[],[f190,f286])).

fof(f190,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f189])).

fof(f586,plain,
    ( spl2_39
    | ~ spl2_2
    | ~ spl2_15
    | ~ spl2_29
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f461,f358,f285,f129,f43,f584])).

fof(f43,plain,
    ( spl2_2
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f358,plain,
    ( spl2_32
  <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f461,plain,
    ( ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = X13
    | ~ spl2_2
    | ~ spl2_15
    | ~ spl2_29
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f460,f44])).

fof(f44,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f460,plain,
    ( ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = k4_xboole_0(X13,k1_xboole_0)
    | ~ spl2_15
    | ~ spl2_29
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f418,f359])).

fof(f359,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f358])).

fof(f418,plain,
    ( ! [X12,X13] : k4_xboole_0(X13,k4_xboole_0(X13,k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,X13))
    | ~ spl2_15
    | ~ spl2_29 ),
    inference(superposition,[],[f286,f130])).

fof(f360,plain,
    ( spl2_32
    | ~ spl2_3
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f336,f332,f47,f358])).

fof(f47,plain,
    ( spl2_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f332,plain,
    ( spl2_31
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f336,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl2_3
    | ~ spl2_31 ),
    inference(superposition,[],[f333,f48])).

fof(f48,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f333,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f332])).

fof(f334,plain,
    ( spl2_31
    | ~ spl2_1
    | ~ spl2_18
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f314,f193,f165,f39,f332])).

fof(f165,plain,
    ( spl2_18
  <=> ! [X5] : k1_xboole_0 = k4_xboole_0(X5,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f314,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_1
    | ~ spl2_18
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f293,f40])).

fof(f293,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)
    | ~ spl2_18
    | ~ spl2_23 ),
    inference(superposition,[],[f194,f166])).

fof(f166,plain,
    ( ! [X5] : k1_xboole_0 = k4_xboole_0(X5,X5)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f165])).

fof(f291,plain,(
    spl2_30 ),
    inference(avatar_split_clause,[],[f37,f289])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f287,plain,(
    spl2_29 ),
    inference(avatar_split_clause,[],[f36,f285])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f26,f26])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f203,plain,
    ( spl2_25
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f132,f129,f47,f201])).

fof(f132,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(superposition,[],[f130,f48])).

fof(f199,plain,
    ( spl2_24
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f106,f78,f51,f197])).

fof(f51,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f78,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f106,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(resolution,[],[f79,f52])).

fof(f52,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f195,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f33,f193])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f191,plain,
    ( spl2_22
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f81,f70,f51,f189])).

fof(f70,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f81,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(resolution,[],[f71,f52])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f167,plain,
    ( spl2_18
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f138,f129,f111,f90,f165])).

fof(f90,plain,
    ( spl2_11
  <=> ! [X2] : k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f111,plain,
    ( spl2_13
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X2),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f138,plain,
    ( ! [X5] : k1_xboole_0 = k4_xboole_0(X5,X5)
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f134,f112])).

fof(f112,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X2),X2)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f111])).

fof(f134,plain,
    ( ! [X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X5),X5)
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(superposition,[],[f130,f91])).

fof(f91,plain,
    ( ! [X2] : k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f157,plain,
    ( spl2_17
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f140,f129,f111,f90,f155])).

fof(f140,plain,
    ( ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f91,f138])).

fof(f131,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f28,f129])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f113,plain,
    ( spl2_13
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f107,f78,f64,f111])).

fof(f64,plain,
    ( spl2_6
  <=> ! [X1] : r1_tarski(k4_xboole_0(X1,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f107,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X2),X2)
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(resolution,[],[f79,f65])).

fof(f65,plain,
    ( ! [X1] : r1_tarski(k4_xboole_0(X1,X1),X1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f92,plain,
    ( spl2_11
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f82,f70,f64,f90])).

fof(f82,plain,
    ( ! [X2] : k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(resolution,[],[f71,f65])).

fof(f80,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f72,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f66,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f55,f51,f43,f64])).

fof(f55,plain,
    ( ! [X1] : r1_tarski(k4_xboole_0(X1,X1),X1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(superposition,[],[f52,f44])).

fof(f53,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f35,f51])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f49,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f25,f47])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f45,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f41,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:12:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (30654)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (30648)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (30650)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (30660)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (30661)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (30649)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (30646)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (30658)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (30652)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (30657)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (30657)Refutation not found, incomplete strategy% (30657)------------------------------
% 0.21/0.48  % (30657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (30657)Memory used [KB]: 10490
% 0.21/0.48  % (30657)Time elapsed: 0.058 s
% 0.21/0.48  % (30657)------------------------------
% 0.21/0.48  % (30657)------------------------------
% 0.21/0.49  % (30651)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (30656)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (30653)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (30659)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (30662)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (30655)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (30647)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (30663)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.13/0.65  % (30653)Refutation found. Thanks to Tanya!
% 2.13/0.65  % SZS status Theorem for theBenchmark
% 2.13/0.65  % SZS output start Proof for theBenchmark
% 2.13/0.65  fof(f5638,plain,(
% 2.13/0.65    $false),
% 2.13/0.65    inference(avatar_sat_refutation,[],[f41,f45,f49,f53,f66,f72,f80,f92,f113,f131,f157,f167,f191,f195,f199,f203,f287,f291,f334,f360,f586,f949,f953,f1294,f1397,f1859,f3910,f5486,f5604])).
% 2.13/0.65  fof(f5604,plain,(
% 2.13/0.65    ~spl2_17 | ~spl2_23 | ~spl2_25 | spl2_56 | ~spl2_64 | ~spl2_124),
% 2.13/0.65    inference(avatar_contradiction_clause,[],[f5603])).
% 2.13/0.65  fof(f5603,plain,(
% 2.13/0.65    $false | (~spl2_17 | ~spl2_23 | ~spl2_25 | spl2_56 | ~spl2_64 | ~spl2_124)),
% 2.13/0.65    inference(subsumption_resolution,[],[f5602,f156])).
% 2.13/0.65  fof(f156,plain,(
% 2.13/0.65    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) ) | ~spl2_17),
% 2.13/0.65    inference(avatar_component_clause,[],[f155])).
% 2.13/0.65  fof(f155,plain,(
% 2.13/0.65    spl2_17 <=> ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 2.13/0.65  fof(f5602,plain,(
% 2.13/0.65    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_23 | ~spl2_25 | spl2_56 | ~spl2_64 | ~spl2_124)),
% 2.13/0.65    inference(forward_demodulation,[],[f5601,f1858])).
% 2.13/0.65  fof(f1858,plain,(
% 2.13/0.65    ( ! [X6,X7,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k2_xboole_0(X5,X7)))) ) | ~spl2_64),
% 2.13/0.65    inference(avatar_component_clause,[],[f1857])).
% 2.13/0.65  fof(f1857,plain,(
% 2.13/0.65    spl2_64 <=> ! [X5,X7,X6] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k2_xboole_0(X5,X7)))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).
% 2.13/0.65  fof(f5601,plain,(
% 2.13/0.65    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_23 | ~spl2_25 | spl2_56 | ~spl2_124)),
% 2.13/0.65    inference(forward_demodulation,[],[f5596,f194])).
% 2.13/0.65  fof(f194,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_23),
% 2.13/0.65    inference(avatar_component_clause,[],[f193])).
% 2.13/0.65  fof(f193,plain,(
% 2.13/0.65    spl2_23 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 2.13/0.65  fof(f5596,plain,(
% 2.13/0.65    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_25 | spl2_56 | ~spl2_124)),
% 2.13/0.65    inference(backward_demodulation,[],[f1396,f5500])).
% 2.13/0.65  fof(f5500,plain,(
% 2.13/0.65    ( ! [X43,X41,X42] : (k4_xboole_0(X43,k2_xboole_0(X41,X42)) = k4_xboole_0(k2_xboole_0(X43,k4_xboole_0(X42,X41)),k2_xboole_0(X41,X42))) ) | (~spl2_25 | ~spl2_124)),
% 2.13/0.65    inference(superposition,[],[f5485,f202])).
% 2.13/0.65  fof(f202,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | ~spl2_25),
% 2.13/0.65    inference(avatar_component_clause,[],[f201])).
% 2.13/0.65  fof(f201,plain,(
% 2.13/0.65    spl2_25 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 2.13/0.65  fof(f5485,plain,(
% 2.13/0.65    ( ! [X35,X36,X34] : (k4_xboole_0(X36,X34) = k4_xboole_0(k2_xboole_0(X36,k4_xboole_0(X34,X35)),X34)) ) | ~spl2_124),
% 2.13/0.65    inference(avatar_component_clause,[],[f5484])).
% 2.13/0.65  fof(f5484,plain,(
% 2.13/0.65    spl2_124 <=> ! [X34,X36,X35] : k4_xboole_0(X36,X34) = k4_xboole_0(k2_xboole_0(X36,k4_xboole_0(X34,X35)),X34)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_124])])).
% 2.13/0.65  fof(f1396,plain,(
% 2.13/0.65    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_56),
% 2.13/0.65    inference(avatar_component_clause,[],[f1394])).
% 2.13/0.65  fof(f1394,plain,(
% 2.13/0.65    spl2_56 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 2.13/0.65  fof(f5486,plain,(
% 2.13/0.65    spl2_124 | ~spl2_46 | ~spl2_100),
% 2.13/0.65    inference(avatar_split_clause,[],[f5363,f3908,f947,f5484])).
% 2.13/0.65  fof(f947,plain,(
% 2.13/0.65    spl2_46 <=> ! [X11,X10] : k2_xboole_0(k4_xboole_0(X10,X11),X10) = X10),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 2.13/0.65  fof(f3908,plain,(
% 2.13/0.65    spl2_100 <=> ! [X5,X4,X6] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).
% 2.13/0.65  fof(f5363,plain,(
% 2.13/0.65    ( ! [X35,X36,X34] : (k4_xboole_0(X36,X34) = k4_xboole_0(k2_xboole_0(X36,k4_xboole_0(X34,X35)),X34)) ) | (~spl2_46 | ~spl2_100)),
% 2.13/0.65    inference(superposition,[],[f3909,f948])).
% 2.13/0.65  fof(f948,plain,(
% 2.13/0.65    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(X10,X11),X10) = X10) ) | ~spl2_46),
% 2.13/0.65    inference(avatar_component_clause,[],[f947])).
% 2.13/0.65  fof(f3909,plain,(
% 2.13/0.65    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6))) ) | ~spl2_100),
% 2.13/0.65    inference(avatar_component_clause,[],[f3908])).
% 2.13/0.65  fof(f3910,plain,(
% 2.13/0.65    spl2_100 | ~spl2_15 | ~spl2_23),
% 2.13/0.65    inference(avatar_split_clause,[],[f315,f193,f129,f3908])).
% 2.13/0.65  fof(f129,plain,(
% 2.13/0.65    spl2_15 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 2.13/0.65  fof(f315,plain,(
% 2.13/0.65    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6))) ) | (~spl2_15 | ~spl2_23)),
% 2.13/0.65    inference(forward_demodulation,[],[f294,f194])).
% 2.13/0.65  fof(f294,plain,(
% 2.13/0.65    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6)) ) | (~spl2_15 | ~spl2_23)),
% 2.13/0.65    inference(superposition,[],[f194,f130])).
% 2.13/0.65  fof(f130,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl2_15),
% 2.13/0.65    inference(avatar_component_clause,[],[f129])).
% 2.13/0.65  fof(f1859,plain,(
% 2.13/0.65    spl2_64 | ~spl2_23 | ~spl2_53),
% 2.13/0.65    inference(avatar_split_clause,[],[f1463,f1292,f193,f1857])).
% 2.13/0.65  fof(f1292,plain,(
% 2.13/0.65    spl2_53 <=> ! [X9,X11,X10] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,X11))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 2.13/0.65  fof(f1463,plain,(
% 2.13/0.65    ( ! [X6,X7,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k2_xboole_0(X5,X7)))) ) | (~spl2_23 | ~spl2_53)),
% 2.13/0.65    inference(superposition,[],[f1293,f194])).
% 2.13/0.65  fof(f1293,plain,(
% 2.13/0.65    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,X11))) ) | ~spl2_53),
% 2.13/0.65    inference(avatar_component_clause,[],[f1292])).
% 2.13/0.65  fof(f1397,plain,(
% 2.13/0.65    ~spl2_56 | ~spl2_23 | ~spl2_29 | ~spl2_39),
% 2.13/0.65    inference(avatar_split_clause,[],[f750,f584,f285,f193,f1394])).
% 2.13/0.65  fof(f285,plain,(
% 2.13/0.65    spl2_29 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 2.13/0.65  fof(f584,plain,(
% 2.13/0.65    spl2_39 <=> ! [X13,X12] : k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = X13),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 2.13/0.65  fof(f750,plain,(
% 2.13/0.65    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_23 | ~spl2_29 | ~spl2_39)),
% 2.13/0.65    inference(forward_demodulation,[],[f749,f286])).
% 2.13/0.65  fof(f286,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_29),
% 2.13/0.65    inference(avatar_component_clause,[],[f285])).
% 2.13/0.65  fof(f749,plain,(
% 2.13/0.65    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) | (~spl2_23 | ~spl2_39)),
% 2.13/0.65    inference(backward_demodulation,[],[f34,f720])).
% 2.13/0.65  fof(f720,plain,(
% 2.13/0.65    ( ! [X6,X4,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(k4_xboole_0(X4,X5),X6))) ) | (~spl2_23 | ~spl2_39)),
% 2.13/0.65    inference(superposition,[],[f194,f585])).
% 2.13/0.65  fof(f585,plain,(
% 2.13/0.65    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = X13) ) | ~spl2_39),
% 2.13/0.65    inference(avatar_component_clause,[],[f584])).
% 2.13/0.65  fof(f34,plain,(
% 2.13/0.65    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 2.13/0.65    inference(definition_unfolding,[],[f20,f26,f29,f29])).
% 2.13/0.65  fof(f29,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f3])).
% 2.13/0.65  fof(f3,axiom,(
% 2.13/0.65    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 2.13/0.65  fof(f26,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f11])).
% 2.13/0.65  fof(f11,axiom,(
% 2.13/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.13/0.65  fof(f20,plain,(
% 2.13/0.65    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 2.13/0.65    inference(cnf_transformation,[],[f18])).
% 2.13/0.65  fof(f18,plain,(
% 2.13/0.65    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 2.13/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 2.13/0.66  fof(f17,plain,(
% 2.13/0.66    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 2.13/0.66    introduced(choice_axiom,[])).
% 2.13/0.66  fof(f15,plain,(
% 2.13/0.66    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.13/0.66    inference(ennf_transformation,[],[f14])).
% 2.13/0.66  fof(f14,negated_conjecture,(
% 2.13/0.66    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.13/0.66    inference(negated_conjecture,[],[f13])).
% 2.13/0.66  fof(f13,conjecture,(
% 2.13/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.13/0.66  fof(f1294,plain,(
% 2.13/0.66    spl2_53 | ~spl2_1 | ~spl2_23 | ~spl2_47),
% 2.13/0.66    inference(avatar_split_clause,[],[f1026,f951,f193,f39,f1292])).
% 2.13/0.66  fof(f39,plain,(
% 2.13/0.66    spl2_1 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.13/0.66  fof(f951,plain,(
% 2.13/0.66    spl2_47 <=> ! [X16,X15] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X16),X15)),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 2.13/0.66  fof(f1026,plain,(
% 2.13/0.66    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,X11))) ) | (~spl2_1 | ~spl2_23 | ~spl2_47)),
% 2.13/0.66    inference(forward_demodulation,[],[f1008,f40])).
% 2.13/0.66  fof(f40,plain,(
% 2.13/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl2_1),
% 2.13/0.66    inference(avatar_component_clause,[],[f39])).
% 2.13/0.66  fof(f1008,plain,(
% 2.13/0.66    ( ! [X10,X11,X9] : (k4_xboole_0(k1_xboole_0,X11) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,X11))) ) | (~spl2_23 | ~spl2_47)),
% 2.13/0.66    inference(superposition,[],[f194,f952])).
% 2.13/0.66  fof(f952,plain,(
% 2.13/0.66    ( ! [X15,X16] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X16),X15)) ) | ~spl2_47),
% 2.13/0.66    inference(avatar_component_clause,[],[f951])).
% 2.13/0.66  fof(f953,plain,(
% 2.13/0.66    spl2_47 | ~spl2_24 | ~spl2_29 | ~spl2_30),
% 2.13/0.66    inference(avatar_split_clause,[],[f900,f289,f285,f197,f951])).
% 2.13/0.66  fof(f197,plain,(
% 2.13/0.66    spl2_24 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 2.13/0.66  fof(f289,plain,(
% 2.13/0.66    spl2_30 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 2.13/0.66  fof(f900,plain,(
% 2.13/0.66    ( ! [X15,X16] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X16),X15)) ) | (~spl2_24 | ~spl2_29 | ~spl2_30)),
% 2.13/0.66    inference(backward_demodulation,[],[f440,f858])).
% 2.13/0.66  fof(f858,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_29 | ~spl2_30)),
% 2.13/0.66    inference(superposition,[],[f290,f286])).
% 2.13/0.66  fof(f290,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_30),
% 2.13/0.66    inference(avatar_component_clause,[],[f289])).
% 2.13/0.66  fof(f440,plain,(
% 2.13/0.66    ( ! [X15,X16] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X16,k4_xboole_0(X16,X15))),X15)) ) | (~spl2_24 | ~spl2_29)),
% 2.13/0.66    inference(superposition,[],[f198,f286])).
% 2.13/0.66  fof(f198,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ) | ~spl2_24),
% 2.13/0.66    inference(avatar_component_clause,[],[f197])).
% 2.13/0.66  fof(f949,plain,(
% 2.13/0.66    spl2_46 | ~spl2_22 | ~spl2_29 | ~spl2_30),
% 2.13/0.66    inference(avatar_split_clause,[],[f899,f289,f285,f189,f947])).
% 2.13/0.66  fof(f189,plain,(
% 2.13/0.66    spl2_22 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 2.13/0.66  fof(f899,plain,(
% 2.13/0.66    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(X10,X11),X10) = X10) ) | (~spl2_22 | ~spl2_29 | ~spl2_30)),
% 2.13/0.66    inference(backward_demodulation,[],[f438,f858])).
% 2.13/0.66  fof(f438,plain,(
% 2.13/0.66    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10))),X10) = X10) ) | (~spl2_22 | ~spl2_29)),
% 2.13/0.66    inference(superposition,[],[f190,f286])).
% 2.13/0.66  fof(f190,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0) ) | ~spl2_22),
% 2.13/0.66    inference(avatar_component_clause,[],[f189])).
% 2.13/0.66  fof(f586,plain,(
% 2.13/0.66    spl2_39 | ~spl2_2 | ~spl2_15 | ~spl2_29 | ~spl2_32),
% 2.13/0.66    inference(avatar_split_clause,[],[f461,f358,f285,f129,f43,f584])).
% 2.13/0.66  fof(f43,plain,(
% 2.13/0.66    spl2_2 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.13/0.66  fof(f358,plain,(
% 2.13/0.66    spl2_32 <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 2.13/0.66  fof(f461,plain,(
% 2.13/0.66    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = X13) ) | (~spl2_2 | ~spl2_15 | ~spl2_29 | ~spl2_32)),
% 2.13/0.66    inference(forward_demodulation,[],[f460,f44])).
% 2.13/0.66  fof(f44,plain,(
% 2.13/0.66    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_2),
% 2.13/0.66    inference(avatar_component_clause,[],[f43])).
% 2.13/0.66  fof(f460,plain,(
% 2.13/0.66    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = k4_xboole_0(X13,k1_xboole_0)) ) | (~spl2_15 | ~spl2_29 | ~spl2_32)),
% 2.13/0.66    inference(forward_demodulation,[],[f418,f359])).
% 2.13/0.66  fof(f359,plain,(
% 2.13/0.66    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) ) | ~spl2_32),
% 2.13/0.66    inference(avatar_component_clause,[],[f358])).
% 2.13/0.66  fof(f418,plain,(
% 2.13/0.66    ( ! [X12,X13] : (k4_xboole_0(X13,k4_xboole_0(X13,k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,X13))) ) | (~spl2_15 | ~spl2_29)),
% 2.13/0.66    inference(superposition,[],[f286,f130])).
% 2.13/0.66  fof(f360,plain,(
% 2.13/0.66    spl2_32 | ~spl2_3 | ~spl2_31),
% 2.13/0.66    inference(avatar_split_clause,[],[f336,f332,f47,f358])).
% 2.13/0.66  fof(f47,plain,(
% 2.13/0.66    spl2_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.13/0.66  fof(f332,plain,(
% 2.13/0.66    spl2_31 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 2.13/0.66  fof(f336,plain,(
% 2.13/0.66    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) ) | (~spl2_3 | ~spl2_31)),
% 2.13/0.66    inference(superposition,[],[f333,f48])).
% 2.13/0.66  fof(f48,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_3),
% 2.13/0.66    inference(avatar_component_clause,[],[f47])).
% 2.13/0.66  fof(f333,plain,(
% 2.13/0.66    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) ) | ~spl2_31),
% 2.13/0.66    inference(avatar_component_clause,[],[f332])).
% 2.13/0.66  fof(f334,plain,(
% 2.13/0.66    spl2_31 | ~spl2_1 | ~spl2_18 | ~spl2_23),
% 2.13/0.66    inference(avatar_split_clause,[],[f314,f193,f165,f39,f332])).
% 2.13/0.66  fof(f165,plain,(
% 2.13/0.66    spl2_18 <=> ! [X5] : k1_xboole_0 = k4_xboole_0(X5,X5)),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 2.13/0.66  fof(f314,plain,(
% 2.13/0.66    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) ) | (~spl2_1 | ~spl2_18 | ~spl2_23)),
% 2.13/0.66    inference(forward_demodulation,[],[f293,f40])).
% 2.13/0.66  fof(f293,plain,(
% 2.13/0.66    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) ) | (~spl2_18 | ~spl2_23)),
% 2.13/0.66    inference(superposition,[],[f194,f166])).
% 2.13/0.66  fof(f166,plain,(
% 2.13/0.66    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(X5,X5)) ) | ~spl2_18),
% 2.13/0.66    inference(avatar_component_clause,[],[f165])).
% 2.13/0.66  fof(f291,plain,(
% 2.13/0.66    spl2_30),
% 2.13/0.66    inference(avatar_split_clause,[],[f37,f289])).
% 2.13/0.66  fof(f37,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.13/0.66    inference(definition_unfolding,[],[f27,f26])).
% 2.13/0.66  fof(f27,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.13/0.66    inference(cnf_transformation,[],[f10])).
% 2.13/0.66  fof(f10,axiom,(
% 2.13/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.13/0.66  fof(f287,plain,(
% 2.13/0.66    spl2_29),
% 2.13/0.66    inference(avatar_split_clause,[],[f36,f285])).
% 2.13/0.66  fof(f36,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.13/0.66    inference(definition_unfolding,[],[f24,f26,f26])).
% 2.13/0.66  fof(f24,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f2])).
% 2.13/0.66  fof(f2,axiom,(
% 2.13/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.13/0.66  fof(f203,plain,(
% 2.13/0.66    spl2_25 | ~spl2_3 | ~spl2_15),
% 2.13/0.66    inference(avatar_split_clause,[],[f132,f129,f47,f201])).
% 2.13/0.66  fof(f132,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | (~spl2_3 | ~spl2_15)),
% 2.13/0.66    inference(superposition,[],[f130,f48])).
% 2.13/0.66  fof(f199,plain,(
% 2.13/0.66    spl2_24 | ~spl2_4 | ~spl2_9),
% 2.13/0.66    inference(avatar_split_clause,[],[f106,f78,f51,f197])).
% 2.13/0.66  fof(f51,plain,(
% 2.13/0.66    spl2_4 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.13/0.66  fof(f78,plain,(
% 2.13/0.66    spl2_9 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 2.13/0.66  fof(f106,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ) | (~spl2_4 | ~spl2_9)),
% 2.13/0.66    inference(resolution,[],[f79,f52])).
% 2.13/0.66  fof(f52,plain,(
% 2.13/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ) | ~spl2_4),
% 2.13/0.66    inference(avatar_component_clause,[],[f51])).
% 2.13/0.66  fof(f79,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl2_9),
% 2.13/0.66    inference(avatar_component_clause,[],[f78])).
% 2.13/0.66  fof(f195,plain,(
% 2.13/0.66    spl2_23),
% 2.13/0.66    inference(avatar_split_clause,[],[f33,f193])).
% 2.13/0.66  fof(f33,plain,(
% 2.13/0.66    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.13/0.66    inference(cnf_transformation,[],[f9])).
% 2.13/0.66  fof(f9,axiom,(
% 2.13/0.66    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.13/0.66  fof(f191,plain,(
% 2.13/0.66    spl2_22 | ~spl2_4 | ~spl2_7),
% 2.13/0.66    inference(avatar_split_clause,[],[f81,f70,f51,f189])).
% 2.13/0.66  fof(f70,plain,(
% 2.13/0.66    spl2_7 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 2.13/0.66  fof(f81,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0) ) | (~spl2_4 | ~spl2_7)),
% 2.13/0.66    inference(resolution,[],[f71,f52])).
% 2.13/0.66  fof(f71,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl2_7),
% 2.13/0.66    inference(avatar_component_clause,[],[f70])).
% 2.13/0.66  fof(f167,plain,(
% 2.13/0.66    spl2_18 | ~spl2_11 | ~spl2_13 | ~spl2_15),
% 2.13/0.66    inference(avatar_split_clause,[],[f138,f129,f111,f90,f165])).
% 2.13/0.66  fof(f90,plain,(
% 2.13/0.66    spl2_11 <=> ! [X2] : k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 2.13/0.66  fof(f111,plain,(
% 2.13/0.66    spl2_13 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X2),X2)),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 2.13/0.66  fof(f138,plain,(
% 2.13/0.66    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(X5,X5)) ) | (~spl2_11 | ~spl2_13 | ~spl2_15)),
% 2.13/0.66    inference(forward_demodulation,[],[f134,f112])).
% 2.13/0.66  fof(f112,plain,(
% 2.13/0.66    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X2),X2)) ) | ~spl2_13),
% 2.13/0.66    inference(avatar_component_clause,[],[f111])).
% 2.13/0.66  fof(f134,plain,(
% 2.13/0.66    ( ! [X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X5),X5)) ) | (~spl2_11 | ~spl2_15)),
% 2.13/0.66    inference(superposition,[],[f130,f91])).
% 2.13/0.66  fof(f91,plain,(
% 2.13/0.66    ( ! [X2] : (k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2) ) | ~spl2_11),
% 2.13/0.66    inference(avatar_component_clause,[],[f90])).
% 2.13/0.66  fof(f157,plain,(
% 2.13/0.66    spl2_17 | ~spl2_11 | ~spl2_13 | ~spl2_15),
% 2.13/0.66    inference(avatar_split_clause,[],[f140,f129,f111,f90,f155])).
% 2.13/0.66  fof(f140,plain,(
% 2.13/0.66    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) ) | (~spl2_11 | ~spl2_13 | ~spl2_15)),
% 2.13/0.66    inference(backward_demodulation,[],[f91,f138])).
% 2.13/0.66  fof(f131,plain,(
% 2.13/0.66    spl2_15),
% 2.13/0.66    inference(avatar_split_clause,[],[f28,f129])).
% 2.13/0.66  fof(f28,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f8])).
% 2.13/0.66  fof(f8,axiom,(
% 2.13/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.13/0.66  fof(f113,plain,(
% 2.13/0.66    spl2_13 | ~spl2_6 | ~spl2_9),
% 2.13/0.66    inference(avatar_split_clause,[],[f107,f78,f64,f111])).
% 2.13/0.66  fof(f64,plain,(
% 2.13/0.66    spl2_6 <=> ! [X1] : r1_tarski(k4_xboole_0(X1,X1),X1)),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.13/0.66  fof(f107,plain,(
% 2.13/0.66    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X2),X2)) ) | (~spl2_6 | ~spl2_9)),
% 2.13/0.66    inference(resolution,[],[f79,f65])).
% 2.13/0.66  fof(f65,plain,(
% 2.13/0.66    ( ! [X1] : (r1_tarski(k4_xboole_0(X1,X1),X1)) ) | ~spl2_6),
% 2.13/0.66    inference(avatar_component_clause,[],[f64])).
% 2.13/0.66  fof(f92,plain,(
% 2.13/0.66    spl2_11 | ~spl2_6 | ~spl2_7),
% 2.13/0.66    inference(avatar_split_clause,[],[f82,f70,f64,f90])).
% 2.13/0.66  fof(f82,plain,(
% 2.13/0.66    ( ! [X2] : (k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2) ) | (~spl2_6 | ~spl2_7)),
% 2.13/0.66    inference(resolution,[],[f71,f65])).
% 2.13/0.66  fof(f80,plain,(
% 2.13/0.66    spl2_9),
% 2.13/0.66    inference(avatar_split_clause,[],[f32,f78])).
% 2.13/0.66  fof(f32,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f19])).
% 2.13/0.66  fof(f19,plain,(
% 2.13/0.66    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.13/0.66    inference(nnf_transformation,[],[f4])).
% 2.13/0.66  fof(f4,axiom,(
% 2.13/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.13/0.66  fof(f72,plain,(
% 2.13/0.66    spl2_7),
% 2.13/0.66    inference(avatar_split_clause,[],[f30,f70])).
% 2.13/0.66  fof(f30,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f16])).
% 2.13/0.66  fof(f16,plain,(
% 2.13/0.66    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.13/0.66    inference(ennf_transformation,[],[f5])).
% 2.13/0.66  fof(f5,axiom,(
% 2.13/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.13/0.66  fof(f66,plain,(
% 2.13/0.66    spl2_6 | ~spl2_2 | ~spl2_4),
% 2.13/0.66    inference(avatar_split_clause,[],[f55,f51,f43,f64])).
% 2.13/0.66  fof(f55,plain,(
% 2.13/0.66    ( ! [X1] : (r1_tarski(k4_xboole_0(X1,X1),X1)) ) | (~spl2_2 | ~spl2_4)),
% 2.13/0.66    inference(superposition,[],[f52,f44])).
% 2.13/0.66  fof(f53,plain,(
% 2.13/0.66    spl2_4),
% 2.13/0.66    inference(avatar_split_clause,[],[f35,f51])).
% 2.13/0.66  fof(f35,plain,(
% 2.13/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 2.13/0.66    inference(definition_unfolding,[],[f23,f26])).
% 2.13/0.66  fof(f23,plain,(
% 2.13/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f6])).
% 2.13/0.66  fof(f6,axiom,(
% 2.13/0.66    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.13/0.66  fof(f49,plain,(
% 2.13/0.66    spl2_3),
% 2.13/0.66    inference(avatar_split_clause,[],[f25,f47])).
% 2.13/0.66  fof(f25,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f1])).
% 2.13/0.66  fof(f1,axiom,(
% 2.13/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.13/0.66  fof(f45,plain,(
% 2.13/0.66    spl2_2),
% 2.13/0.66    inference(avatar_split_clause,[],[f22,f43])).
% 2.13/0.66  fof(f22,plain,(
% 2.13/0.66    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.13/0.66    inference(cnf_transformation,[],[f7])).
% 2.13/0.66  fof(f7,axiom,(
% 2.13/0.66    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.13/0.66  fof(f41,plain,(
% 2.13/0.66    spl2_1),
% 2.13/0.66    inference(avatar_split_clause,[],[f21,f39])).
% 2.13/0.66  fof(f21,plain,(
% 2.13/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f12])).
% 2.13/0.66  fof(f12,axiom,(
% 2.13/0.66    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 2.13/0.66  % SZS output end Proof for theBenchmark
% 2.13/0.66  % (30653)------------------------------
% 2.13/0.66  % (30653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.66  % (30653)Termination reason: Refutation
% 2.13/0.66  
% 2.13/0.66  % (30653)Memory used [KB]: 9722
% 2.13/0.66  % (30653)Time elapsed: 0.242 s
% 2.13/0.66  % (30653)------------------------------
% 2.13/0.66  % (30653)------------------------------
% 2.13/0.66  % (30645)Success in time 0.296 s
%------------------------------------------------------------------------------
