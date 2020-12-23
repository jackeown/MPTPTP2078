%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 (  97 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :    6
%              Number of atoms          :  123 ( 196 expanded)
%              Number of equality atoms :   48 (  84 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f25,f29,f33,f42,f47,f51,f64,f73,f107,f232,f249])).

fof(f249,plain,
    ( spl7_1
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl7_1
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f20,f247])).

fof(f247,plain,
    ( ! [X39,X37,X41,X38,X36,X42,X40] : k2_xboole_0(k3_enumset1(X41,X42,X36,X37,X38),k2_tarski(X39,X40)) = k5_enumset1(X41,X42,X36,X37,X38,X39,X40)
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f237,f50])).

fof(f50,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl7_7
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f237,plain,
    ( ! [X39,X37,X41,X38,X36,X42,X40] : k2_xboole_0(k3_enumset1(X41,X42,X36,X37,X38),k2_tarski(X39,X40)) = k2_xboole_0(k2_tarski(X41,X42),k3_enumset1(X36,X37,X38,X39,X40))
    | ~ spl7_5
    | ~ spl7_23 ),
    inference(superposition,[],[f231,f41])).

fof(f41,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl7_5
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f231,plain,
    ( ! [X14,X19,X17,X15,X18,X16] : k2_xboole_0(k2_tarski(X18,X19),k2_xboole_0(k1_enumset1(X14,X15,X16),X17)) = k2_xboole_0(k3_enumset1(X18,X19,X14,X15,X16),X17)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl7_23
  <=> ! [X16,X18,X15,X17,X19,X14] : k2_xboole_0(k2_tarski(X18,X19),k2_xboole_0(k1_enumset1(X14,X15,X16),X17)) = k2_xboole_0(k3_enumset1(X18,X19,X14,X15,X16),X17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f20,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl7_1
  <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) = k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f232,plain,
    ( spl7_23
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f118,f105,f71,f62,f230])).

fof(f62,plain,
    ( spl7_8
  <=> ! [X3,X5,X4,X6] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f71,plain,
    ( spl7_9
  <=> ! [X1,X3,X5,X0,X2,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k2_tarski(X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f105,plain,
    ( spl7_13
  <=> ! [X9,X7,X8,X10] : k2_xboole_0(k2_tarski(X10,X7),k2_xboole_0(k1_tarski(X8),X9)) = k2_xboole_0(k1_enumset1(X10,X7,X8),X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f118,plain,
    ( ! [X14,X19,X17,X15,X18,X16] : k2_xboole_0(k2_tarski(X18,X19),k2_xboole_0(k1_enumset1(X14,X15,X16),X17)) = k2_xboole_0(k3_enumset1(X18,X19,X14,X15,X16),X17)
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f111,f72])).

fof(f72,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k2_tarski(X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f111,plain,
    ( ! [X14,X19,X17,X15,X18,X16] : k2_xboole_0(k1_enumset1(X18,X19,X14),k2_xboole_0(k2_tarski(X15,X16),X17)) = k2_xboole_0(k2_tarski(X18,X19),k2_xboole_0(k1_enumset1(X14,X15,X16),X17))
    | ~ spl7_8
    | ~ spl7_13 ),
    inference(superposition,[],[f106,f63])).

fof(f63,plain,
    ( ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f106,plain,
    ( ! [X10,X8,X7,X9] : k2_xboole_0(k2_tarski(X10,X7),k2_xboole_0(k1_tarski(X8),X9)) = k2_xboole_0(k1_enumset1(X10,X7,X8),X9)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( spl7_13
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f58,f45,f31,f27,f105])).

fof(f27,plain,
    ( spl7_3
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f31,plain,
    ( spl7_4
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f45,plain,
    ( spl7_6
  <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f58,plain,
    ( ! [X10,X8,X7,X9] : k2_xboole_0(k2_tarski(X10,X7),k2_xboole_0(k1_tarski(X8),X9)) = k2_xboole_0(k1_enumset1(X10,X7,X8),X9)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f55,f35])).

fof(f35,plain,
    ( ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(superposition,[],[f32,f28])).

fof(f28,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f32,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f55,plain,
    ( ! [X10,X8,X7,X9] : k2_xboole_0(k2_tarski(X10,X7),k2_xboole_0(k1_tarski(X8),X9)) = k2_xboole_0(k1_tarski(X10),k2_xboole_0(k2_tarski(X7,X8),X9))
    | ~ spl7_6 ),
    inference(superposition,[],[f46,f46])).

fof(f46,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f73,plain,
    ( spl7_9
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f43,f40,f31,f71])).

fof(f43,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k2_tarski(X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(superposition,[],[f32,f41])).

fof(f64,plain,
    ( spl7_8
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f35,f31,f27,f62])).

fof(f51,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f16,f49])).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

fof(f47,plain,
    ( spl7_6
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f34,f31,f23,f45])).

fof(f23,plain,
    ( spl7_2
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f34,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(superposition,[],[f32,f24])).

fof(f24,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f42,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f15,f40])).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(f33,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f29,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f25,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f12,f23])).

fof(f12,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f21,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f11,f18])).

fof(f11,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:51:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (10844)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.45  % (10853)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.45  % (10844)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f256,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f21,f25,f29,f33,f42,f47,f51,f64,f73,f107,f232,f249])).
% 0.22/0.45  fof(f249,plain,(
% 0.22/0.45    spl7_1 | ~spl7_5 | ~spl7_7 | ~spl7_23),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f248])).
% 0.22/0.45  fof(f248,plain,(
% 0.22/0.45    $false | (spl7_1 | ~spl7_5 | ~spl7_7 | ~spl7_23)),
% 0.22/0.45    inference(subsumption_resolution,[],[f20,f247])).
% 0.22/0.45  fof(f247,plain,(
% 0.22/0.45    ( ! [X39,X37,X41,X38,X36,X42,X40] : (k2_xboole_0(k3_enumset1(X41,X42,X36,X37,X38),k2_tarski(X39,X40)) = k5_enumset1(X41,X42,X36,X37,X38,X39,X40)) ) | (~spl7_5 | ~spl7_7 | ~spl7_23)),
% 0.22/0.45    inference(forward_demodulation,[],[f237,f50])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) ) | ~spl7_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f49])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    spl7_7 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.45  fof(f237,plain,(
% 0.22/0.45    ( ! [X39,X37,X41,X38,X36,X42,X40] : (k2_xboole_0(k3_enumset1(X41,X42,X36,X37,X38),k2_tarski(X39,X40)) = k2_xboole_0(k2_tarski(X41,X42),k3_enumset1(X36,X37,X38,X39,X40))) ) | (~spl7_5 | ~spl7_23)),
% 0.22/0.45    inference(superposition,[],[f231,f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) ) | ~spl7_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f40])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    spl7_5 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.45  fof(f231,plain,(
% 0.22/0.45    ( ! [X14,X19,X17,X15,X18,X16] : (k2_xboole_0(k2_tarski(X18,X19),k2_xboole_0(k1_enumset1(X14,X15,X16),X17)) = k2_xboole_0(k3_enumset1(X18,X19,X14,X15,X16),X17)) ) | ~spl7_23),
% 0.22/0.45    inference(avatar_component_clause,[],[f230])).
% 0.22/0.45  fof(f230,plain,(
% 0.22/0.45    spl7_23 <=> ! [X16,X18,X15,X17,X19,X14] : k2_xboole_0(k2_tarski(X18,X19),k2_xboole_0(k1_enumset1(X14,X15,X16),X17)) = k2_xboole_0(k3_enumset1(X18,X19,X14,X15,X16),X17)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) | spl7_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    spl7_1 <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) = k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.45  fof(f232,plain,(
% 0.22/0.45    spl7_23 | ~spl7_8 | ~spl7_9 | ~spl7_13),
% 0.22/0.45    inference(avatar_split_clause,[],[f118,f105,f71,f62,f230])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    spl7_8 <=> ! [X3,X5,X4,X6] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    spl7_9 <=> ! [X1,X3,X5,X0,X2,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k2_tarski(X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.45  fof(f105,plain,(
% 0.22/0.45    spl7_13 <=> ! [X9,X7,X8,X10] : k2_xboole_0(k2_tarski(X10,X7),k2_xboole_0(k1_tarski(X8),X9)) = k2_xboole_0(k1_enumset1(X10,X7,X8),X9)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.45  fof(f118,plain,(
% 0.22/0.45    ( ! [X14,X19,X17,X15,X18,X16] : (k2_xboole_0(k2_tarski(X18,X19),k2_xboole_0(k1_enumset1(X14,X15,X16),X17)) = k2_xboole_0(k3_enumset1(X18,X19,X14,X15,X16),X17)) ) | (~spl7_8 | ~spl7_9 | ~spl7_13)),
% 0.22/0.45    inference(forward_demodulation,[],[f111,f72])).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k2_tarski(X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)) ) | ~spl7_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f71])).
% 0.22/0.45  fof(f111,plain,(
% 0.22/0.45    ( ! [X14,X19,X17,X15,X18,X16] : (k2_xboole_0(k1_enumset1(X18,X19,X14),k2_xboole_0(k2_tarski(X15,X16),X17)) = k2_xboole_0(k2_tarski(X18,X19),k2_xboole_0(k1_enumset1(X14,X15,X16),X17))) ) | (~spl7_8 | ~spl7_13)),
% 0.22/0.45    inference(superposition,[],[f106,f63])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) ) | ~spl7_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f62])).
% 0.22/0.45  fof(f106,plain,(
% 0.22/0.45    ( ! [X10,X8,X7,X9] : (k2_xboole_0(k2_tarski(X10,X7),k2_xboole_0(k1_tarski(X8),X9)) = k2_xboole_0(k1_enumset1(X10,X7,X8),X9)) ) | ~spl7_13),
% 0.22/0.45    inference(avatar_component_clause,[],[f105])).
% 0.22/0.45  fof(f107,plain,(
% 0.22/0.45    spl7_13 | ~spl7_3 | ~spl7_4 | ~spl7_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f58,f45,f31,f27,f105])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    spl7_3 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    spl7_4 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    spl7_6 <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    ( ! [X10,X8,X7,X9] : (k2_xboole_0(k2_tarski(X10,X7),k2_xboole_0(k1_tarski(X8),X9)) = k2_xboole_0(k1_enumset1(X10,X7,X8),X9)) ) | (~spl7_3 | ~spl7_4 | ~spl7_6)),
% 0.22/0.45    inference(forward_demodulation,[],[f55,f35])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) ) | (~spl7_3 | ~spl7_4)),
% 0.22/0.45    inference(superposition,[],[f32,f28])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) ) | ~spl7_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f27])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl7_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f31])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    ( ! [X10,X8,X7,X9] : (k2_xboole_0(k2_tarski(X10,X7),k2_xboole_0(k1_tarski(X8),X9)) = k2_xboole_0(k1_tarski(X10),k2_xboole_0(k2_tarski(X7,X8),X9))) ) | ~spl7_6),
% 0.22/0.45    inference(superposition,[],[f46,f46])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | ~spl7_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f45])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    spl7_9 | ~spl7_4 | ~spl7_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f43,f40,f31,f71])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k2_tarski(X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)) ) | (~spl7_4 | ~spl7_5)),
% 0.22/0.45    inference(superposition,[],[f32,f41])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    spl7_8 | ~spl7_3 | ~spl7_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f35,f31,f27,f62])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    spl7_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f16,f49])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    spl7_6 | ~spl7_2 | ~spl7_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f34,f31,f23,f45])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    spl7_2 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | (~spl7_2 | ~spl7_4)),
% 0.22/0.45    inference(superposition,[],[f32,f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) | ~spl7_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f23])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    spl7_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f15,f40])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    spl7_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f14,f31])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    spl7_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f13,f27])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    spl7_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f12,f23])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ~spl7_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f11,f18])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.22/0.45    inference(cnf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f8,f9])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.22/0.45    inference(negated_conjecture,[],[f6])).
% 0.22/0.45  fof(f6,conjecture,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (10844)------------------------------
% 0.22/0.45  % (10844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (10844)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (10844)Memory used [KB]: 6268
% 0.22/0.45  % (10844)Time elapsed: 0.049 s
% 0.22/0.45  % (10844)------------------------------
% 0.22/0.45  % (10844)------------------------------
% 0.22/0.45  % (10838)Success in time 0.089 s
%------------------------------------------------------------------------------
