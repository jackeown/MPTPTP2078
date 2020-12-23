%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   71 (  93 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f25,f33,f37,f41,f47,f63,f66])).

fof(f66,plain,
    ( spl2_1
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl2_1
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f20,f64])).

fof(f64,plain,
    ( ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(superposition,[],[f62,f32])).

fof(f32,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_4
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f62,plain,
    ( ! [X2,X0,X1] : r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] : r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f20,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl2_1
  <=> r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f63,plain,
    ( spl2_9
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f48,f45,f35,f61])).

fof(f35,plain,
    ( spl2_5
  <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f45,plain,
    ( spl2_7
  <=> ! [X1,X3,X0,X2] : r1_tarski(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f48,plain,
    ( ! [X2,X0,X1] : r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2))
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(superposition,[],[f46,f36])).

fof(f36,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f35])).

fof(f46,plain,
    ( ! [X2,X0,X3,X1] : r1_tarski(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f45])).

fof(f47,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f43,f39,f23,f45])).

fof(f23,plain,
    ( spl2_2
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f39,plain,
    ( spl2_6
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f43,plain,
    ( ! [X2,X0,X3,X1] : r1_tarski(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(superposition,[],[f24,f40])).

fof(f40,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f39])).

fof(f24,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f41,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f37,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f13,f23])).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f21,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f11,f18])).

fof(f11,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))
   => ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:12:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.45  % (7348)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.46  % (7343)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (7352)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (7340)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (7343)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f21,f25,f33,f37,f41,f47,f63,f66])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    spl2_1 | ~spl2_4 | ~spl2_9),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f65])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    $false | (spl2_1 | ~spl2_4 | ~spl2_9)),
% 0.22/0.47    inference(subsumption_resolution,[],[f20,f64])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) ) | (~spl2_4 | ~spl2_9)),
% 0.22/0.47    inference(superposition,[],[f62,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) ) | ~spl2_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    spl2_4 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2))) ) | ~spl2_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f61])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    spl2_9 <=> ! [X1,X0,X2] : r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) | spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    spl2_1 <=> r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    spl2_9 | ~spl2_5 | ~spl2_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f48,f45,f35,f61])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    spl2_5 <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    spl2_7 <=> ! [X1,X3,X0,X2] : r1_tarski(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2))) ) | (~spl2_5 | ~spl2_7)),
% 0.22/0.47    inference(superposition,[],[f46,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) ) | ~spl2_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f35])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (r1_tarski(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3))) ) | ~spl2_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f45])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    spl2_7 | ~spl2_2 | ~spl2_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f43,f39,f23,f45])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    spl2_2 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    spl2_6 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (r1_tarski(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3))) ) | (~spl2_2 | ~spl2_6)),
% 0.22/0.47    inference(superposition,[],[f24,f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | ~spl2_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f39])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f23])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    spl2_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f16,f39])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f15,f35])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    spl2_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f14,f31])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f13,f23])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ~spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f11,f18])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) => ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.47    inference(negated_conjecture,[],[f6])).
% 0.22/0.47  fof(f6,conjecture,(
% 0.22/0.47    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (7343)------------------------------
% 0.22/0.47  % (7343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (7343)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (7343)Memory used [KB]: 6140
% 0.22/0.47  % (7343)Time elapsed: 0.051 s
% 0.22/0.47  % (7343)------------------------------
% 0.22/0.47  % (7343)------------------------------
% 0.22/0.47  % (7337)Success in time 0.112 s
%------------------------------------------------------------------------------
