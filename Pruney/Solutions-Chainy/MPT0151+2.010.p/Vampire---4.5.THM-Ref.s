%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  76 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :  106 ( 144 expanded)
%              Number of equality atoms :   45 (  64 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f734,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f55,f72,f108,f112,f126,f133,f217,f236,f720,f731])).

fof(f731,plain,
    ( spl8_1
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_39 ),
    inference(avatar_contradiction_clause,[],[f730])).

fof(f730,plain,
    ( $false
    | spl8_1
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f34,f729])).

fof(f729,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X7,X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k6_enumset1(X7,X0,X1,X2,X3,X4,X5,X6)
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_39 ),
    inference(forward_demodulation,[],[f721,f132])).

fof(f132,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl8_13
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f721,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X7,X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k2_xboole_0(k1_tarski(X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))
    | ~ spl8_18
    | ~ spl8_39 ),
    inference(superposition,[],[f235,f719])).

fof(f719,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X6,X0,X1,X2,X3),k2_tarski(X4,X5)) = k5_enumset1(X6,X0,X1,X2,X3,X4,X5)
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f718])).

fof(f718,plain,
    ( spl8_39
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k2_xboole_0(k3_enumset1(X6,X0,X1,X2,X3),k2_tarski(X4,X5)) = k5_enumset1(X6,X0,X1,X2,X3,X4,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f235,plain,
    ( ! [X14,X12,X10,X8,X13,X11,X9] : k2_xboole_0(k1_tarski(X8),k2_xboole_0(k3_enumset1(X9,X10,X11,X12,X13),X14)) = k2_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),X14)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl8_18
  <=> ! [X9,X11,X13,X8,X10,X12,X14] : k2_xboole_0(k1_tarski(X8),k2_xboole_0(k3_enumset1(X9,X10,X11,X12,X13),X14)) = k2_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),X14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f34,plain,
    ( k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl8_1
  <=> k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) = k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f720,plain,
    ( spl8_39
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f224,f215,f124,f110,f718])).

fof(f110,plain,
    ( spl8_10
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f124,plain,
    ( spl8_12
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f215,plain,
    ( spl8_17
  <=> ! [X1,X3,X5,X0,X2,X4] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f224,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X6,X0,X1,X2,X3),k2_tarski(X4,X5)) = k5_enumset1(X6,X0,X1,X2,X3,X4,X5)
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_17 ),
    inference(forward_demodulation,[],[f218,f125])).

fof(f125,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f218,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X6,X0,X1,X2,X3),k2_tarski(X4,X5)) = k2_xboole_0(k1_tarski(X6),k4_enumset1(X0,X1,X2,X3,X4,X5))
    | ~ spl8_10
    | ~ spl8_17 ),
    inference(superposition,[],[f216,f111])).

fof(f111,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f216,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f215])).

fof(f236,plain,
    ( spl8_18
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f114,f106,f53,f234])).

fof(f53,plain,
    ( spl8_6
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f106,plain,
    ( spl8_9
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f114,plain,
    ( ! [X14,X12,X10,X8,X13,X11,X9] : k2_xboole_0(k1_tarski(X8),k2_xboole_0(k3_enumset1(X9,X10,X11,X12,X13),X14)) = k2_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),X14)
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(superposition,[],[f54,f107])).

fof(f107,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f54,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f217,plain,
    ( spl8_17
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f77,f70,f53,f215])).

fof(f70,plain,
    ( spl8_7
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f77,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(superposition,[],[f54,f71])).

fof(f71,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f133,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f28,f131])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(f126,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f27,f124])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(f112,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f26,f110])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(f108,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f25,f106])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f72,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f24,f70])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f55,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f35,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f17,f32])).

fof(f17,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:27:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (20175)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.44  % (20175)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f734,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f35,f55,f72,f108,f112,f126,f133,f217,f236,f720,f731])).
% 0.21/0.44  fof(f731,plain,(
% 0.21/0.44    spl8_1 | ~spl8_13 | ~spl8_18 | ~spl8_39),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f730])).
% 0.21/0.44  fof(f730,plain,(
% 0.21/0.44    $false | (spl8_1 | ~spl8_13 | ~spl8_18 | ~spl8_39)),
% 0.21/0.44    inference(subsumption_resolution,[],[f34,f729])).
% 0.21/0.44  fof(f729,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X7,X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k6_enumset1(X7,X0,X1,X2,X3,X4,X5,X6)) ) | (~spl8_13 | ~spl8_18 | ~spl8_39)),
% 0.21/0.44    inference(forward_demodulation,[],[f721,f132])).
% 0.21/0.44  fof(f132,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) ) | ~spl8_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f131])).
% 0.21/0.44  fof(f131,plain,(
% 0.21/0.44    spl8_13 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.44  fof(f721,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X7,X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k2_xboole_0(k1_tarski(X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) ) | (~spl8_18 | ~spl8_39)),
% 0.21/0.44    inference(superposition,[],[f235,f719])).
% 0.21/0.44  fof(f719,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X6,X0,X1,X2,X3),k2_tarski(X4,X5)) = k5_enumset1(X6,X0,X1,X2,X3,X4,X5)) ) | ~spl8_39),
% 0.21/0.44    inference(avatar_component_clause,[],[f718])).
% 0.21/0.44  fof(f718,plain,(
% 0.21/0.44    spl8_39 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k2_xboole_0(k3_enumset1(X6,X0,X1,X2,X3),k2_tarski(X4,X5)) = k5_enumset1(X6,X0,X1,X2,X3,X4,X5)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.21/0.44  fof(f235,plain,(
% 0.21/0.44    ( ! [X14,X12,X10,X8,X13,X11,X9] : (k2_xboole_0(k1_tarski(X8),k2_xboole_0(k3_enumset1(X9,X10,X11,X12,X13),X14)) = k2_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),X14)) ) | ~spl8_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f234])).
% 0.21/0.44  fof(f234,plain,(
% 0.21/0.44    spl8_18 <=> ! [X9,X11,X13,X8,X10,X12,X14] : k2_xboole_0(k1_tarski(X8),k2_xboole_0(k3_enumset1(X9,X10,X11,X12,X13),X14)) = k2_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),X14)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) | spl8_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    spl8_1 <=> k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) = k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.44  fof(f720,plain,(
% 0.21/0.44    spl8_39 | ~spl8_10 | ~spl8_12 | ~spl8_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f224,f215,f124,f110,f718])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    spl8_10 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.44  fof(f124,plain,(
% 0.21/0.44    spl8_12 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.44  fof(f215,plain,(
% 0.21/0.44    spl8_17 <=> ! [X1,X3,X5,X0,X2,X4] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.44  fof(f224,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X6,X0,X1,X2,X3),k2_tarski(X4,X5)) = k5_enumset1(X6,X0,X1,X2,X3,X4,X5)) ) | (~spl8_10 | ~spl8_12 | ~spl8_17)),
% 0.21/0.44    inference(forward_demodulation,[],[f218,f125])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) ) | ~spl8_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f124])).
% 0.21/0.44  fof(f218,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X6,X0,X1,X2,X3),k2_tarski(X4,X5)) = k2_xboole_0(k1_tarski(X6),k4_enumset1(X0,X1,X2,X3,X4,X5))) ) | (~spl8_10 | ~spl8_17)),
% 0.21/0.44    inference(superposition,[],[f216,f111])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | ~spl8_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f110])).
% 0.21/0.44  fof(f216,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)) ) | ~spl8_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f215])).
% 0.21/0.44  fof(f236,plain,(
% 0.21/0.44    spl8_18 | ~spl8_6 | ~spl8_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f114,f106,f53,f234])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl8_6 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    spl8_9 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    ( ! [X14,X12,X10,X8,X13,X11,X9] : (k2_xboole_0(k1_tarski(X8),k2_xboole_0(k3_enumset1(X9,X10,X11,X12,X13),X14)) = k2_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),X14)) ) | (~spl8_6 | ~spl8_9)),
% 0.21/0.44    inference(superposition,[],[f54,f107])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) ) | ~spl8_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f106])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl8_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f53])).
% 0.21/0.44  fof(f217,plain,(
% 0.21/0.44    spl8_17 | ~spl8_6 | ~spl8_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f77,f70,f53,f215])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    spl8_7 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)) ) | (~spl8_6 | ~spl8_7)),
% 0.21/0.44    inference(superposition,[],[f54,f71])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) ) | ~spl8_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f70])).
% 0.21/0.44  fof(f133,plain,(
% 0.21/0.44    spl8_13),
% 0.21/0.44    inference(avatar_split_clause,[],[f28,f131])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).
% 0.21/0.44  fof(f126,plain,(
% 0.21/0.44    spl8_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f27,f124])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    spl8_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f26,f110])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    spl8_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f25,f106])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl8_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f24,f70])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl8_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f53])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ~spl8_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f32])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f14,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.21/0.44    inference(ennf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.21/0.44    inference(negated_conjecture,[],[f12])).
% 0.21/0.44  fof(f12,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (20175)------------------------------
% 0.21/0.44  % (20175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (20175)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (20175)Memory used [KB]: 7036
% 0.21/0.44  % (20175)Time elapsed: 0.031 s
% 0.21/0.44  % (20175)------------------------------
% 0.21/0.44  % (20175)------------------------------
% 0.21/0.44  % (20169)Success in time 0.089 s
%------------------------------------------------------------------------------
