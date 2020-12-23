%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 (  83 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f56,f67,f73])).

fof(f73,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f26,f71])).

fof(f71,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f68,f38])).

fof(f38,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl2_4
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f68,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_enumset1(X0,X0,X1))
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(superposition,[],[f66,f30])).

fof(f30,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_2
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),k1_enumset1(X0,X1,X2))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] : k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),k1_enumset1(X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f26,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f67,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f62,f54,f33,f65])).

fof(f33,plain,
    ( spl2_3
  <=> ! [X1,X0] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f54,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f62,plain,
    ( ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),k1_enumset1(X0,X1,X2))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(superposition,[],[f34,f55])).

fof(f55,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f34,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f56,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f39,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f31,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f14,f24])).

fof(f14,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] : k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (25012)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (25021)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.45  % (25012)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f56,f67,f73])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_10),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f72])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    $false | (spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_10)),
% 0.21/0.45    inference(subsumption_resolution,[],[f26,f71])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) ) | (~spl2_2 | ~spl2_4 | ~spl2_10)),
% 0.21/0.45    inference(forward_demodulation,[],[f68,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) ) | ~spl2_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    spl2_4 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_enumset1(X0,X0,X1))) ) | (~spl2_2 | ~spl2_10)),
% 0.21/0.45    inference(superposition,[],[f66,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl2_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    spl2_2 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),k1_enumset1(X0,X1,X2))) ) | ~spl2_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f65])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl2_10 <=> ! [X1,X0,X2] : k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),k1_enumset1(X0,X1,X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) | spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    spl2_1 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    spl2_10 | ~spl2_3 | ~spl2_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f62,f54,f33,f65])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    spl2_3 <=> ! [X1,X0] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    spl2_8 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),k1_enumset1(X0,X1,X2))) ) | (~spl2_3 | ~spl2_8)),
% 0.21/0.45    inference(superposition,[],[f34,f55])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | ~spl2_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f54])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) ) | ~spl2_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f33])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    spl2_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f21,f54])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f17,f37])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f16,f33])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f15,f29])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ~spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f14,f24])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.45    inference(negated_conjecture,[],[f9])).
% 0.21/0.45  fof(f9,conjecture,(
% 0.21/0.45    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (25012)------------------------------
% 0.21/0.45  % (25012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (25012)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (25012)Memory used [KB]: 6140
% 0.21/0.45  % (25012)Time elapsed: 0.051 s
% 0.21/0.45  % (25012)------------------------------
% 0.21/0.45  % (25012)------------------------------
% 0.21/0.45  % (25019)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.45  % (25002)Success in time 0.096 s
%------------------------------------------------------------------------------
