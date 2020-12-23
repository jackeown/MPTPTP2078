%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:06 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 249 expanded)
%              Number of leaves         :   38 ( 115 expanded)
%              Depth                    :    9
%              Number of atoms          :  323 ( 519 expanded)
%              Number of equality atoms :  113 ( 219 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f69,f78,f85,f99,f108,f114,f122,f131,f149,f157,f181,f185,f189,f238,f319,f516,f814,f924,f1825,f3177,f3278])).

fof(f3278,plain,
    ( ~ spl2_1
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_31
    | spl2_47
    | ~ spl2_73
    | ~ spl2_83 ),
    inference(avatar_contradiction_clause,[],[f3277])).

fof(f3277,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_31
    | spl2_47
    | ~ spl2_73
    | ~ spl2_83 ),
    inference(subsumption_resolution,[],[f923,f3276])).

fof(f3276,plain,
    ( ! [X52,X51] : k2_xboole_0(X52,X51) = k4_xboole_0(k2_xboole_0(X52,X51),k4_xboole_0(X52,k4_xboole_0(X52,k4_xboole_0(X51,X52))))
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_31
    | ~ spl2_73
    | ~ spl2_83 ),
    inference(backward_demodulation,[],[f3050,f3261])).

fof(f3261,plain,
    ( ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(k4_xboole_0(X4,X3),X3)
    | ~ spl2_12
    | ~ spl2_17
    | ~ spl2_31
    | ~ spl2_83 ),
    inference(backward_demodulation,[],[f173,f3196])).

fof(f3196,plain,
    ( ! [X19,X18] : k2_xboole_0(X18,X19) = k2_xboole_0(k4_xboole_0(X19,X18),k2_xboole_0(X18,X19))
    | ~ spl2_31
    | ~ spl2_83 ),
    inference(superposition,[],[f515,f3176])).

fof(f3176,plain,
    ( ! [X10,X11] : k4_xboole_0(X10,X11) = k4_xboole_0(k2_xboole_0(X11,X10),X11)
    | ~ spl2_83 ),
    inference(avatar_component_clause,[],[f3175])).

fof(f3175,plain,
    ( spl2_83
  <=> ! [X11,X10] : k4_xboole_0(X10,X11) = k4_xboole_0(k2_xboole_0(X11,X10),X11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).

fof(f515,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f514])).

fof(f514,plain,
    ( spl2_31
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f173,plain,
    ( ! [X4,X3] : k2_xboole_0(k4_xboole_0(X4,X3),X3) = k2_xboole_0(k4_xboole_0(X4,X3),k2_xboole_0(X3,X4))
    | ~ spl2_12
    | ~ spl2_17 ),
    inference(superposition,[],[f156,f121])).

fof(f121,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl2_12
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f156,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl2_17
  <=> ! [X1,X0] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f3050,plain,
    ( ! [X52,X51] : k2_xboole_0(k4_xboole_0(X51,X52),X52) = k4_xboole_0(k2_xboole_0(X52,X51),k4_xboole_0(X52,k4_xboole_0(X52,k4_xboole_0(X51,X52))))
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_73 ),
    inference(forward_demodulation,[],[f3049,f121])).

fof(f3049,plain,
    ( ! [X52,X51] : k2_xboole_0(k4_xboole_0(X51,X52),X52) = k4_xboole_0(k2_xboole_0(X52,k4_xboole_0(X51,X52)),k4_xboole_0(X52,k4_xboole_0(X52,k4_xboole_0(X51,X52))))
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_73 ),
    inference(forward_demodulation,[],[f3048,f60])).

fof(f60,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_1
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f3048,plain,
    ( ! [X52,X51] : k4_xboole_0(k2_xboole_0(X52,k4_xboole_0(X51,X52)),k4_xboole_0(X52,k4_xboole_0(X52,k4_xboole_0(X51,X52)))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X51,X52),X52),k1_xboole_0)
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_73 ),
    inference(forward_demodulation,[],[f2886,f84])).

fof(f84,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_6
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f2886,plain,
    ( ! [X52,X51] : k4_xboole_0(k2_xboole_0(X52,k4_xboole_0(X51,X52)),k4_xboole_0(X52,k4_xboole_0(X52,k4_xboole_0(X51,X52)))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X51,X52),X52),k4_xboole_0(k4_xboole_0(X51,X52),k4_xboole_0(X51,X52)))
    | ~ spl2_15
    | ~ spl2_73 ),
    inference(superposition,[],[f1824,f148])).

fof(f148,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl2_15
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f1824,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_73 ),
    inference(avatar_component_clause,[],[f1823])).

fof(f1823,plain,
    ( spl2_73
  <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).

fof(f923,plain,
    ( k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))))
    | spl2_47 ),
    inference(avatar_component_clause,[],[f921])).

fof(f921,plain,
    ( spl2_47
  <=> k2_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f3177,plain,
    ( spl2_83
    | ~ spl2_1
    | ~ spl2_14
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_22
    | ~ spl2_43
    | ~ spl2_73 ),
    inference(avatar_split_clause,[],[f2985,f1823,f812,f236,f183,f155,f129,f59,f3175])).

fof(f129,plain,
    ( spl2_14
  <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f183,plain,
    ( spl2_19
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f236,plain,
    ( spl2_22
  <=> ! [X11,X10] : k1_xboole_0 = k4_xboole_0(X10,k2_xboole_0(X11,X10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f812,plain,
    ( spl2_43
  <=> ! [X9,X8] : k2_xboole_0(X9,X8) = k2_xboole_0(k2_xboole_0(X9,X8),X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f2985,plain,
    ( ! [X10,X11] : k4_xboole_0(X10,X11) = k4_xboole_0(k2_xboole_0(X11,X10),X11)
    | ~ spl2_1
    | ~ spl2_14
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_22
    | ~ spl2_43
    | ~ spl2_73 ),
    inference(forward_demodulation,[],[f2984,f130])).

fof(f130,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f2984,plain,
    ( ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(k2_xboole_0(X11,X10),X11)
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_22
    | ~ spl2_43
    | ~ spl2_73 ),
    inference(forward_demodulation,[],[f2983,f156])).

fof(f2983,plain,
    ( ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(k2_xboole_0(X11,k2_xboole_0(X10,X11)),X11)
    | ~ spl2_1
    | ~ spl2_19
    | ~ spl2_22
    | ~ spl2_43
    | ~ spl2_73 ),
    inference(forward_demodulation,[],[f2982,f60])).

fof(f2982,plain,
    ( ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(k2_xboole_0(X11,k2_xboole_0(X10,X11)),k4_xboole_0(X11,k1_xboole_0))
    | ~ spl2_19
    | ~ spl2_22
    | ~ spl2_43
    | ~ spl2_73 ),
    inference(forward_demodulation,[],[f2981,f237])).

fof(f237,plain,
    ( ! [X10,X11] : k1_xboole_0 = k4_xboole_0(X10,k2_xboole_0(X11,X10))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f236])).

fof(f2981,plain,
    ( ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(k2_xboole_0(X11,k2_xboole_0(X10,X11)),k4_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,X11))))
    | ~ spl2_19
    | ~ spl2_43
    | ~ spl2_73 ),
    inference(forward_demodulation,[],[f2873,f184])).

fof(f184,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f183])).

fof(f2873,plain,
    ( ! [X10,X11] : k4_xboole_0(k2_xboole_0(X11,k2_xboole_0(X10,X11)),k4_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,X11)))) = k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(k2_xboole_0(X10,X11),X11)))
    | ~ spl2_43
    | ~ spl2_73 ),
    inference(superposition,[],[f1824,f813])).

fof(f813,plain,
    ( ! [X8,X9] : k2_xboole_0(X9,X8) = k2_xboole_0(k2_xboole_0(X9,X8),X8)
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f812])).

fof(f1825,plain,(
    spl2_73 ),
    inference(avatar_split_clause,[],[f46,f1823])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f31,f42,f42])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f924,plain,(
    ~ spl2_47 ),
    inference(avatar_split_clause,[],[f51,f921])).

fof(f51,plain,(
    k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f44,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f44,plain,(
    k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f25,f42])).

fof(f25,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).

fof(f23,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f814,plain,
    ( spl2_43
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f256,f236,f120,f106,f812])).

fof(f106,plain,
    ( spl2_10
  <=> ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f256,plain,
    ( ! [X8,X9] : k2_xboole_0(X9,X8) = k2_xboole_0(k2_xboole_0(X9,X8),X8)
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f252,f107])).

fof(f107,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f252,plain,
    ( ! [X8,X9] : k2_xboole_0(k2_xboole_0(X9,X8),X8) = k2_xboole_0(k2_xboole_0(X9,X8),k1_xboole_0)
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(superposition,[],[f121,f237])).

fof(f516,plain,
    ( spl2_31
    | ~ spl2_19
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f451,f317,f183,f514])).

fof(f317,plain,
    ( spl2_27
  <=> ! [X5,X6] : k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f451,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0
    | ~ spl2_19
    | ~ spl2_27 ),
    inference(superposition,[],[f318,f184])).

fof(f318,plain,
    ( ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f317])).

fof(f319,plain,
    ( spl2_27
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f288,f187,f183,f120,f317])).

fof(f187,plain,
    ( spl2_20
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f288,plain,
    ( ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f273,f188])).

fof(f188,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f187])).

fof(f273,plain,
    ( ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k4_xboole_0(X5,X6))
    | ~ spl2_12
    | ~ spl2_19 ),
    inference(superposition,[],[f121,f184])).

fof(f238,plain,
    ( spl2_22
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f215,f179,f120,f83,f236])).

fof(f179,plain,
    ( spl2_18
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f215,plain,
    ( ! [X10,X11] : k1_xboole_0 = k4_xboole_0(X10,k2_xboole_0(X11,X10))
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f200,f121])).

fof(f200,plain,
    ( ! [X10,X11] : k1_xboole_0 = k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(X10,X11)))
    | ~ spl2_6
    | ~ spl2_18 ),
    inference(superposition,[],[f180,f84])).

fof(f180,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f179])).

fof(f189,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f48,f187])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f36,f32])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f185,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f47,f183])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f181,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f41,f179])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f157,plain,
    ( spl2_17
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f144,f129,f120,f155])).

fof(f144,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f140,f121])).

fof(f140,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(superposition,[],[f121,f130])).

fof(f149,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f115,f112,f67,f147])).

fof(f67,plain,
    ( spl2_3
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f112,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f115,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(resolution,[],[f113,f68])).

fof(f68,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f131,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f35,f129])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f122,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f33,f120])).

fof(f114,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f39,f112])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f108,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f101,f97,f59,f106])).

fof(f97,plain,
    ( spl2_9
  <=> ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f101,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(superposition,[],[f98,f60])).

fof(f98,plain,
    ( ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f99,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f81,f76,f63,f97])).

fof(f63,plain,
    ( spl2_2
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f76,plain,
    ( spl2_5
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f81,plain,
    ( ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f50,f79])).

fof(f79,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f77,f64])).

fof(f64,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f77,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = X0 ),
    inference(backward_demodulation,[],[f45,f27])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f26,f42])).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f85,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f79,f76,f63,f83])).

fof(f78,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f30,f76])).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f69,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f65,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f61,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f27,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:36:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (6922)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (6931)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (6918)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (6921)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (6920)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (6932)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (6919)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (6923)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (6930)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (6917)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (6933)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (6925)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (6926)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (6934)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (6928)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (6928)Refutation not found, incomplete strategy% (6928)------------------------------
% 0.21/0.51  % (6928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6928)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6928)Memory used [KB]: 10490
% 0.21/0.51  % (6928)Time elapsed: 0.090 s
% 0.21/0.51  % (6928)------------------------------
% 0.21/0.51  % (6928)------------------------------
% 0.21/0.51  % (6924)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (6935)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (6927)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 2.16/0.64  % (6924)Refutation found. Thanks to Tanya!
% 2.16/0.64  % SZS status Theorem for theBenchmark
% 2.16/0.64  % SZS output start Proof for theBenchmark
% 2.16/0.64  fof(f3308,plain,(
% 2.16/0.64    $false),
% 2.16/0.64    inference(avatar_sat_refutation,[],[f61,f65,f69,f78,f85,f99,f108,f114,f122,f131,f149,f157,f181,f185,f189,f238,f319,f516,f814,f924,f1825,f3177,f3278])).
% 2.16/0.64  fof(f3278,plain,(
% 2.16/0.64    ~spl2_1 | ~spl2_6 | ~spl2_12 | ~spl2_15 | ~spl2_17 | ~spl2_31 | spl2_47 | ~spl2_73 | ~spl2_83),
% 2.16/0.64    inference(avatar_contradiction_clause,[],[f3277])).
% 2.16/0.64  fof(f3277,plain,(
% 2.16/0.64    $false | (~spl2_1 | ~spl2_6 | ~spl2_12 | ~spl2_15 | ~spl2_17 | ~spl2_31 | spl2_47 | ~spl2_73 | ~spl2_83)),
% 2.16/0.64    inference(subsumption_resolution,[],[f923,f3276])).
% 2.16/0.64  fof(f3276,plain,(
% 2.16/0.64    ( ! [X52,X51] : (k2_xboole_0(X52,X51) = k4_xboole_0(k2_xboole_0(X52,X51),k4_xboole_0(X52,k4_xboole_0(X52,k4_xboole_0(X51,X52))))) ) | (~spl2_1 | ~spl2_6 | ~spl2_12 | ~spl2_15 | ~spl2_17 | ~spl2_31 | ~spl2_73 | ~spl2_83)),
% 2.16/0.64    inference(backward_demodulation,[],[f3050,f3261])).
% 2.16/0.64  fof(f3261,plain,(
% 2.16/0.64    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(k4_xboole_0(X4,X3),X3)) ) | (~spl2_12 | ~spl2_17 | ~spl2_31 | ~spl2_83)),
% 2.16/0.64    inference(backward_demodulation,[],[f173,f3196])).
% 2.16/0.64  fof(f3196,plain,(
% 2.16/0.64    ( ! [X19,X18] : (k2_xboole_0(X18,X19) = k2_xboole_0(k4_xboole_0(X19,X18),k2_xboole_0(X18,X19))) ) | (~spl2_31 | ~spl2_83)),
% 2.16/0.64    inference(superposition,[],[f515,f3176])).
% 2.16/0.64  fof(f3176,plain,(
% 2.16/0.64    ( ! [X10,X11] : (k4_xboole_0(X10,X11) = k4_xboole_0(k2_xboole_0(X11,X10),X11)) ) | ~spl2_83),
% 2.16/0.64    inference(avatar_component_clause,[],[f3175])).
% 2.16/0.64  fof(f3175,plain,(
% 2.16/0.64    spl2_83 <=> ! [X11,X10] : k4_xboole_0(X10,X11) = k4_xboole_0(k2_xboole_0(X11,X10),X11)),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).
% 2.16/0.64  fof(f515,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) ) | ~spl2_31),
% 2.16/0.64    inference(avatar_component_clause,[],[f514])).
% 2.16/0.64  fof(f514,plain,(
% 2.16/0.64    spl2_31 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 2.16/0.64  fof(f173,plain,(
% 2.16/0.64    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X4,X3),X3) = k2_xboole_0(k4_xboole_0(X4,X3),k2_xboole_0(X3,X4))) ) | (~spl2_12 | ~spl2_17)),
% 2.16/0.64    inference(superposition,[],[f156,f121])).
% 2.16/0.64  fof(f121,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_12),
% 2.16/0.64    inference(avatar_component_clause,[],[f120])).
% 2.16/0.64  fof(f120,plain,(
% 2.16/0.64    spl2_12 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 2.16/0.64  fof(f156,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) ) | ~spl2_17),
% 2.16/0.64    inference(avatar_component_clause,[],[f155])).
% 2.16/0.64  fof(f155,plain,(
% 2.16/0.64    spl2_17 <=> ! [X1,X0] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 2.16/0.64  fof(f3050,plain,(
% 2.16/0.64    ( ! [X52,X51] : (k2_xboole_0(k4_xboole_0(X51,X52),X52) = k4_xboole_0(k2_xboole_0(X52,X51),k4_xboole_0(X52,k4_xboole_0(X52,k4_xboole_0(X51,X52))))) ) | (~spl2_1 | ~spl2_6 | ~spl2_12 | ~spl2_15 | ~spl2_73)),
% 2.16/0.64    inference(forward_demodulation,[],[f3049,f121])).
% 2.16/0.64  fof(f3049,plain,(
% 2.16/0.64    ( ! [X52,X51] : (k2_xboole_0(k4_xboole_0(X51,X52),X52) = k4_xboole_0(k2_xboole_0(X52,k4_xboole_0(X51,X52)),k4_xboole_0(X52,k4_xboole_0(X52,k4_xboole_0(X51,X52))))) ) | (~spl2_1 | ~spl2_6 | ~spl2_15 | ~spl2_73)),
% 2.16/0.64    inference(forward_demodulation,[],[f3048,f60])).
% 2.16/0.64  fof(f60,plain,(
% 2.16/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_1),
% 2.16/0.64    inference(avatar_component_clause,[],[f59])).
% 2.16/0.64  fof(f59,plain,(
% 2.16/0.64    spl2_1 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.16/0.64  fof(f3048,plain,(
% 2.16/0.64    ( ! [X52,X51] : (k4_xboole_0(k2_xboole_0(X52,k4_xboole_0(X51,X52)),k4_xboole_0(X52,k4_xboole_0(X52,k4_xboole_0(X51,X52)))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X51,X52),X52),k1_xboole_0)) ) | (~spl2_6 | ~spl2_15 | ~spl2_73)),
% 2.16/0.64    inference(forward_demodulation,[],[f2886,f84])).
% 2.16/0.64  fof(f84,plain,(
% 2.16/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_6),
% 2.16/0.64    inference(avatar_component_clause,[],[f83])).
% 2.16/0.64  fof(f83,plain,(
% 2.16/0.64    spl2_6 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.16/0.64  fof(f2886,plain,(
% 2.16/0.64    ( ! [X52,X51] : (k4_xboole_0(k2_xboole_0(X52,k4_xboole_0(X51,X52)),k4_xboole_0(X52,k4_xboole_0(X52,k4_xboole_0(X51,X52)))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X51,X52),X52),k4_xboole_0(k4_xboole_0(X51,X52),k4_xboole_0(X51,X52)))) ) | (~spl2_15 | ~spl2_73)),
% 2.16/0.64    inference(superposition,[],[f1824,f148])).
% 2.16/0.64  fof(f148,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl2_15),
% 2.16/0.64    inference(avatar_component_clause,[],[f147])).
% 2.16/0.64  fof(f147,plain,(
% 2.16/0.64    spl2_15 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 2.16/0.64  fof(f1824,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl2_73),
% 2.16/0.64    inference(avatar_component_clause,[],[f1823])).
% 2.16/0.64  fof(f1823,plain,(
% 2.16/0.64    spl2_73 <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).
% 2.16/0.64  fof(f923,plain,(
% 2.16/0.64    k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) | spl2_47),
% 2.16/0.64    inference(avatar_component_clause,[],[f921])).
% 2.16/0.64  fof(f921,plain,(
% 2.16/0.64    spl2_47 <=> k2_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))))),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 2.16/0.64  fof(f3177,plain,(
% 2.16/0.64    spl2_83 | ~spl2_1 | ~spl2_14 | ~spl2_17 | ~spl2_19 | ~spl2_22 | ~spl2_43 | ~spl2_73),
% 2.16/0.64    inference(avatar_split_clause,[],[f2985,f1823,f812,f236,f183,f155,f129,f59,f3175])).
% 2.16/0.64  fof(f129,plain,(
% 2.16/0.64    spl2_14 <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 2.16/0.64  fof(f183,plain,(
% 2.16/0.64    spl2_19 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 2.16/0.64  fof(f236,plain,(
% 2.16/0.64    spl2_22 <=> ! [X11,X10] : k1_xboole_0 = k4_xboole_0(X10,k2_xboole_0(X11,X10))),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 2.16/0.64  fof(f812,plain,(
% 2.16/0.64    spl2_43 <=> ! [X9,X8] : k2_xboole_0(X9,X8) = k2_xboole_0(k2_xboole_0(X9,X8),X8)),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 2.16/0.64  fof(f2985,plain,(
% 2.16/0.64    ( ! [X10,X11] : (k4_xboole_0(X10,X11) = k4_xboole_0(k2_xboole_0(X11,X10),X11)) ) | (~spl2_1 | ~spl2_14 | ~spl2_17 | ~spl2_19 | ~spl2_22 | ~spl2_43 | ~spl2_73)),
% 2.16/0.64    inference(forward_demodulation,[],[f2984,f130])).
% 2.16/0.64  fof(f130,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) ) | ~spl2_14),
% 2.16/0.64    inference(avatar_component_clause,[],[f129])).
% 2.16/0.64  fof(f2984,plain,(
% 2.16/0.64    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(k2_xboole_0(X11,X10),X11)) ) | (~spl2_1 | ~spl2_17 | ~spl2_19 | ~spl2_22 | ~spl2_43 | ~spl2_73)),
% 2.16/0.64    inference(forward_demodulation,[],[f2983,f156])).
% 2.16/0.64  fof(f2983,plain,(
% 2.16/0.64    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(k2_xboole_0(X11,k2_xboole_0(X10,X11)),X11)) ) | (~spl2_1 | ~spl2_19 | ~spl2_22 | ~spl2_43 | ~spl2_73)),
% 2.16/0.64    inference(forward_demodulation,[],[f2982,f60])).
% 2.16/0.64  fof(f2982,plain,(
% 2.16/0.64    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(k2_xboole_0(X11,k2_xboole_0(X10,X11)),k4_xboole_0(X11,k1_xboole_0))) ) | (~spl2_19 | ~spl2_22 | ~spl2_43 | ~spl2_73)),
% 2.16/0.64    inference(forward_demodulation,[],[f2981,f237])).
% 2.16/0.64  fof(f237,plain,(
% 2.16/0.64    ( ! [X10,X11] : (k1_xboole_0 = k4_xboole_0(X10,k2_xboole_0(X11,X10))) ) | ~spl2_22),
% 2.16/0.64    inference(avatar_component_clause,[],[f236])).
% 2.16/0.64  fof(f2981,plain,(
% 2.16/0.64    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(k2_xboole_0(X11,k2_xboole_0(X10,X11)),k4_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,X11))))) ) | (~spl2_19 | ~spl2_43 | ~spl2_73)),
% 2.16/0.64    inference(forward_demodulation,[],[f2873,f184])).
% 2.16/0.64  fof(f184,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_19),
% 2.16/0.64    inference(avatar_component_clause,[],[f183])).
% 2.16/0.64  fof(f2873,plain,(
% 2.16/0.64    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X11,k2_xboole_0(X10,X11)),k4_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,X11)))) = k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(k2_xboole_0(X10,X11),X11)))) ) | (~spl2_43 | ~spl2_73)),
% 2.16/0.64    inference(superposition,[],[f1824,f813])).
% 2.16/0.64  fof(f813,plain,(
% 2.16/0.64    ( ! [X8,X9] : (k2_xboole_0(X9,X8) = k2_xboole_0(k2_xboole_0(X9,X8),X8)) ) | ~spl2_43),
% 2.16/0.64    inference(avatar_component_clause,[],[f812])).
% 2.16/0.64  fof(f1825,plain,(
% 2.16/0.64    spl2_73),
% 2.16/0.64    inference(avatar_split_clause,[],[f46,f1823])).
% 2.16/0.64  fof(f46,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 2.16/0.64    inference(definition_unfolding,[],[f31,f42,f42])).
% 2.16/0.64  fof(f42,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.16/0.64    inference(definition_unfolding,[],[f38,f32])).
% 2.16/0.64  fof(f32,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f10])).
% 2.16/0.64  fof(f10,axiom,(
% 2.16/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.16/0.64  fof(f38,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f3])).
% 2.16/0.64  fof(f3,axiom,(
% 2.16/0.64    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.16/0.64  fof(f31,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f1])).
% 2.16/0.64  fof(f1,axiom,(
% 2.16/0.64    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.16/0.64  fof(f924,plain,(
% 2.16/0.64    ~spl2_47),
% 2.16/0.64    inference(avatar_split_clause,[],[f51,f921])).
% 2.16/0.64  fof(f51,plain,(
% 2.16/0.64    k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))))),
% 2.16/0.64    inference(backward_demodulation,[],[f44,f33])).
% 2.16/0.64  fof(f33,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f4])).
% 2.16/0.64  fof(f4,axiom,(
% 2.16/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.16/0.64  fof(f44,plain,(
% 2.16/0.64    k2_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))))),
% 2.16/0.64    inference(definition_unfolding,[],[f25,f42])).
% 2.16/0.64  fof(f25,plain,(
% 2.16/0.64    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 2.16/0.64    inference(cnf_transformation,[],[f24])).
% 2.16/0.64  fof(f24,plain,(
% 2.16/0.64    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 2.16/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).
% 2.16/0.64  fof(f23,plain,(
% 2.16/0.64    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 2.16/0.64    introduced(choice_axiom,[])).
% 2.16/0.64  fof(f21,plain,(
% 2.16/0.64    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.16/0.64    inference(ennf_transformation,[],[f18])).
% 2.16/0.64  fof(f18,negated_conjecture,(
% 2.16/0.64    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.16/0.64    inference(negated_conjecture,[],[f17])).
% 2.16/0.64  fof(f17,conjecture,(
% 2.16/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.16/0.64  fof(f814,plain,(
% 2.16/0.64    spl2_43 | ~spl2_10 | ~spl2_12 | ~spl2_22),
% 2.16/0.64    inference(avatar_split_clause,[],[f256,f236,f120,f106,f812])).
% 2.16/0.64  fof(f106,plain,(
% 2.16/0.64    spl2_10 <=> ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 2.16/0.64  fof(f256,plain,(
% 2.16/0.64    ( ! [X8,X9] : (k2_xboole_0(X9,X8) = k2_xboole_0(k2_xboole_0(X9,X8),X8)) ) | (~spl2_10 | ~spl2_12 | ~spl2_22)),
% 2.16/0.64    inference(forward_demodulation,[],[f252,f107])).
% 2.16/0.64  fof(f107,plain,(
% 2.16/0.64    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | ~spl2_10),
% 2.16/0.64    inference(avatar_component_clause,[],[f106])).
% 2.16/0.64  fof(f252,plain,(
% 2.16/0.64    ( ! [X8,X9] : (k2_xboole_0(k2_xboole_0(X9,X8),X8) = k2_xboole_0(k2_xboole_0(X9,X8),k1_xboole_0)) ) | (~spl2_12 | ~spl2_22)),
% 2.16/0.64    inference(superposition,[],[f121,f237])).
% 2.16/0.64  fof(f516,plain,(
% 2.16/0.64    spl2_31 | ~spl2_19 | ~spl2_27),
% 2.16/0.64    inference(avatar_split_clause,[],[f451,f317,f183,f514])).
% 2.16/0.64  fof(f317,plain,(
% 2.16/0.64    spl2_27 <=> ! [X5,X6] : k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 2.16/0.64  fof(f451,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) ) | (~spl2_19 | ~spl2_27)),
% 2.16/0.64    inference(superposition,[],[f318,f184])).
% 2.16/0.64  fof(f318,plain,(
% 2.16/0.64    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5) ) | ~spl2_27),
% 2.16/0.64    inference(avatar_component_clause,[],[f317])).
% 2.16/0.64  fof(f319,plain,(
% 2.16/0.64    spl2_27 | ~spl2_12 | ~spl2_19 | ~spl2_20),
% 2.16/0.64    inference(avatar_split_clause,[],[f288,f187,f183,f120,f317])).
% 2.16/0.64  fof(f187,plain,(
% 2.16/0.64    spl2_20 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 2.16/0.64  fof(f288,plain,(
% 2.16/0.64    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = X5) ) | (~spl2_12 | ~spl2_19 | ~spl2_20)),
% 2.16/0.64    inference(forward_demodulation,[],[f273,f188])).
% 2.16/0.64  fof(f188,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_20),
% 2.16/0.64    inference(avatar_component_clause,[],[f187])).
% 2.16/0.64  fof(f273,plain,(
% 2.16/0.64    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5) = k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k4_xboole_0(X5,X6))) ) | (~spl2_12 | ~spl2_19)),
% 2.16/0.64    inference(superposition,[],[f121,f184])).
% 2.16/0.64  fof(f238,plain,(
% 2.16/0.64    spl2_22 | ~spl2_6 | ~spl2_12 | ~spl2_18),
% 2.16/0.64    inference(avatar_split_clause,[],[f215,f179,f120,f83,f236])).
% 2.16/0.64  fof(f179,plain,(
% 2.16/0.64    spl2_18 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 2.16/0.64  fof(f215,plain,(
% 2.16/0.64    ( ! [X10,X11] : (k1_xboole_0 = k4_xboole_0(X10,k2_xboole_0(X11,X10))) ) | (~spl2_6 | ~spl2_12 | ~spl2_18)),
% 2.16/0.64    inference(forward_demodulation,[],[f200,f121])).
% 2.16/0.64  fof(f200,plain,(
% 2.16/0.64    ( ! [X10,X11] : (k1_xboole_0 = k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(X10,X11)))) ) | (~spl2_6 | ~spl2_18)),
% 2.16/0.64    inference(superposition,[],[f180,f84])).
% 2.16/0.64  fof(f180,plain,(
% 2.16/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_18),
% 2.16/0.64    inference(avatar_component_clause,[],[f179])).
% 2.16/0.64  fof(f189,plain,(
% 2.16/0.64    spl2_20),
% 2.16/0.64    inference(avatar_split_clause,[],[f48,f187])).
% 2.16/0.64  fof(f48,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.16/0.64    inference(definition_unfolding,[],[f36,f32])).
% 2.16/0.64  fof(f36,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.16/0.64    inference(cnf_transformation,[],[f11])).
% 2.16/0.64  fof(f11,axiom,(
% 2.16/0.64    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.16/0.64  fof(f185,plain,(
% 2.16/0.64    spl2_19),
% 2.16/0.64    inference(avatar_split_clause,[],[f47,f183])).
% 2.16/0.64  fof(f47,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.16/0.64    inference(definition_unfolding,[],[f34,f32])).
% 2.16/0.64  fof(f34,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f9])).
% 2.16/0.64  fof(f9,axiom,(
% 2.16/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.16/0.64  fof(f181,plain,(
% 2.16/0.64    spl2_18),
% 2.16/0.64    inference(avatar_split_clause,[],[f41,f179])).
% 2.16/0.64  fof(f41,plain,(
% 2.16/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f7])).
% 2.16/0.64  fof(f7,axiom,(
% 2.16/0.64    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.16/0.64  fof(f157,plain,(
% 2.16/0.64    spl2_17 | ~spl2_12 | ~spl2_14),
% 2.16/0.64    inference(avatar_split_clause,[],[f144,f129,f120,f155])).
% 2.16/0.64  fof(f144,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) ) | (~spl2_12 | ~spl2_14)),
% 2.16/0.64    inference(forward_demodulation,[],[f140,f121])).
% 2.16/0.64  fof(f140,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) ) | (~spl2_12 | ~spl2_14)),
% 2.16/0.64    inference(superposition,[],[f121,f130])).
% 2.16/0.64  fof(f149,plain,(
% 2.16/0.64    spl2_15 | ~spl2_3 | ~spl2_11),
% 2.16/0.64    inference(avatar_split_clause,[],[f115,f112,f67,f147])).
% 2.16/0.64  fof(f67,plain,(
% 2.16/0.64    spl2_3 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.16/0.64  fof(f112,plain,(
% 2.16/0.64    spl2_11 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 2.16/0.64  fof(f115,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)) ) | (~spl2_3 | ~spl2_11)),
% 2.16/0.64    inference(resolution,[],[f113,f68])).
% 2.16/0.64  fof(f68,plain,(
% 2.16/0.64    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl2_3),
% 2.16/0.64    inference(avatar_component_clause,[],[f67])).
% 2.16/0.64  fof(f113,plain,(
% 2.16/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl2_11),
% 2.16/0.64    inference(avatar_component_clause,[],[f112])).
% 2.16/0.64  fof(f131,plain,(
% 2.16/0.64    spl2_14),
% 2.16/0.64    inference(avatar_split_clause,[],[f35,f129])).
% 2.16/0.64  fof(f35,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f6])).
% 2.16/0.64  fof(f6,axiom,(
% 2.16/0.64    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.16/0.64  fof(f122,plain,(
% 2.16/0.64    spl2_12),
% 2.16/0.64    inference(avatar_split_clause,[],[f33,f120])).
% 2.16/0.64  fof(f114,plain,(
% 2.16/0.64    spl2_11),
% 2.16/0.64    inference(avatar_split_clause,[],[f39,f112])).
% 2.16/0.64  fof(f39,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f22])).
% 2.16/0.64  fof(f22,plain,(
% 2.16/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 2.16/0.64    inference(ennf_transformation,[],[f20])).
% 2.16/0.64  fof(f20,plain,(
% 2.16/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 2.16/0.64    inference(unused_predicate_definition_removal,[],[f14])).
% 2.16/0.64  fof(f14,axiom,(
% 2.16/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.16/0.64  fof(f108,plain,(
% 2.16/0.64    spl2_10 | ~spl2_1 | ~spl2_9),
% 2.16/0.64    inference(avatar_split_clause,[],[f101,f97,f59,f106])).
% 2.16/0.64  fof(f97,plain,(
% 2.16/0.64    spl2_9 <=> ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 2.16/0.64  fof(f101,plain,(
% 2.16/0.64    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | (~spl2_1 | ~spl2_9)),
% 2.16/0.64    inference(superposition,[],[f98,f60])).
% 2.16/0.64  fof(f98,plain,(
% 2.16/0.64    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) ) | ~spl2_9),
% 2.16/0.64    inference(avatar_component_clause,[],[f97])).
% 2.16/0.64  fof(f99,plain,(
% 2.16/0.64    spl2_9 | ~spl2_2 | ~spl2_5),
% 2.16/0.64    inference(avatar_split_clause,[],[f81,f76,f63,f97])).
% 2.16/0.64  fof(f63,plain,(
% 2.16/0.64    spl2_2 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.16/0.64  fof(f76,plain,(
% 2.16/0.64    spl2_5 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.16/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.16/0.64  fof(f81,plain,(
% 2.16/0.64    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) ) | (~spl2_2 | ~spl2_5)),
% 2.16/0.64    inference(backward_demodulation,[],[f50,f79])).
% 2.16/0.64  fof(f79,plain,(
% 2.16/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_2 | ~spl2_5)),
% 2.16/0.64    inference(superposition,[],[f77,f64])).
% 2.16/0.64  fof(f64,plain,(
% 2.16/0.64    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl2_2),
% 2.16/0.64    inference(avatar_component_clause,[],[f63])).
% 2.16/0.64  fof(f77,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl2_5),
% 2.16/0.64    inference(avatar_component_clause,[],[f76])).
% 2.16/0.64  fof(f50,plain,(
% 2.16/0.64    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = X0) )),
% 2.16/0.64    inference(backward_demodulation,[],[f45,f27])).
% 2.16/0.64  fof(f27,plain,(
% 2.16/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.16/0.64    inference(cnf_transformation,[],[f5])).
% 2.16/0.64  fof(f5,axiom,(
% 2.16/0.64    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.16/0.64  fof(f45,plain,(
% 2.16/0.64    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0) )),
% 2.16/0.64    inference(definition_unfolding,[],[f26,f42])).
% 2.16/0.64  fof(f26,plain,(
% 2.16/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.16/0.64    inference(cnf_transformation,[],[f12])).
% 2.16/0.64  fof(f12,axiom,(
% 2.16/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.16/0.64  fof(f85,plain,(
% 2.16/0.64    spl2_6 | ~spl2_2 | ~spl2_5),
% 2.16/0.64    inference(avatar_split_clause,[],[f79,f76,f63,f83])).
% 2.16/0.64  fof(f78,plain,(
% 2.16/0.64    spl2_5),
% 2.16/0.64    inference(avatar_split_clause,[],[f30,f76])).
% 2.16/0.64  fof(f30,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f8])).
% 2.16/0.64  fof(f8,axiom,(
% 2.16/0.64    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.16/0.64  fof(f69,plain,(
% 2.16/0.64    spl2_3),
% 2.16/0.64    inference(avatar_split_clause,[],[f29,f67])).
% 2.16/0.64  fof(f29,plain,(
% 2.16/0.64    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f13])).
% 2.16/0.64  fof(f13,axiom,(
% 2.16/0.64    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.16/0.64  fof(f65,plain,(
% 2.16/0.64    spl2_2),
% 2.16/0.64    inference(avatar_split_clause,[],[f28,f63])).
% 2.16/0.64  fof(f28,plain,(
% 2.16/0.64    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.16/0.64    inference(cnf_transformation,[],[f19])).
% 2.16/0.64  fof(f19,plain,(
% 2.16/0.64    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.16/0.64    inference(rectify,[],[f2])).
% 2.16/0.64  fof(f2,axiom,(
% 2.16/0.64    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.16/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.16/0.64  fof(f61,plain,(
% 2.16/0.64    spl2_1),
% 2.16/0.64    inference(avatar_split_clause,[],[f27,f59])).
% 2.16/0.64  % SZS output end Proof for theBenchmark
% 2.16/0.64  % (6924)------------------------------
% 2.16/0.64  % (6924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.64  % (6924)Termination reason: Refutation
% 2.16/0.64  
% 2.16/0.64  % (6924)Memory used [KB]: 8443
% 2.16/0.64  % (6924)Time elapsed: 0.193 s
% 2.16/0.64  % (6924)------------------------------
% 2.16/0.64  % (6924)------------------------------
% 2.16/0.65  % (6914)Success in time 0.28 s
%------------------------------------------------------------------------------
