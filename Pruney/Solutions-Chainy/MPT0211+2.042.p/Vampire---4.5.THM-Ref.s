%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 (  78 expanded)
%              Number of equality atoms :   32 (  41 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f55,f75,f94,f102,f105])).

fof(f105,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl3_8 ),
    inference(trivial_inequality_removal,[],[f103])).

fof(f103,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | spl3_8 ),
    inference(superposition,[],[f100,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f100,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_8
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f102,plain,
    ( ~ spl3_8
    | spl3_7 ),
    inference(avatar_split_clause,[],[f96,f90,f98])).

fof(f90,plain,
    ( spl3_7
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f96,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)
    | spl3_7 ),
    inference(superposition,[],[f92,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

fof(f92,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f94,plain,
    ( ~ spl3_7
    | spl3_5 ),
    inference(avatar_split_clause,[],[f88,f71,f90])).

fof(f71,plain,
    ( spl3_5
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f88,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2)
    | spl3_5 ),
    inference(superposition,[],[f73,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f73,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK2,sK0,sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f75,plain,
    ( ~ spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f59,f52,f71])).

fof(f52,plain,
    ( spl3_2
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

% (22510)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% (22509)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% (22503)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f59,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK2,sK0,sK1)
    | spl3_2 ),
    inference(superposition,[],[f54,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f54,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f55,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f50,f46,f52])).

fof(f46,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_1 ),
    inference(superposition,[],[f48,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f48,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f49,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:11:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.42  % (22516)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.46  % (22501)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.46  % (22513)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.46  % (22502)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.46  % (22504)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.47  % (22500)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.47  % (22514)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.47  % (22512)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.47  % (22511)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.47  % (22508)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.48  % (22506)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.48  % (22511)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f106,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f49,f55,f75,f94,f102,f105])).
% 0.19/0.48  fof(f105,plain,(
% 0.19/0.48    spl3_8),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f104])).
% 0.19/0.48  fof(f104,plain,(
% 0.19/0.48    $false | spl3_8),
% 0.19/0.48    inference(trivial_inequality_removal,[],[f103])).
% 0.19/0.48  fof(f103,plain,(
% 0.19/0.48    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) | spl3_8),
% 0.19/0.48    inference(superposition,[],[f100,f32])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f17,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.48  fof(f100,plain,(
% 0.19/0.48    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) | spl3_8),
% 0.19/0.48    inference(avatar_component_clause,[],[f98])).
% 0.19/0.48  fof(f98,plain,(
% 0.19/0.48    spl3_8 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.48  fof(f102,plain,(
% 0.19/0.48    ~spl3_8 | spl3_7),
% 0.19/0.48    inference(avatar_split_clause,[],[f96,f90,f98])).
% 0.19/0.48  fof(f90,plain,(
% 0.19/0.48    spl3_7 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK1,sK0,sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.48  fof(f96,plain,(
% 0.19/0.48    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) | spl3_7),
% 0.19/0.48    inference(superposition,[],[f92,f34])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).
% 0.19/0.48  fof(f92,plain,(
% 0.19/0.48    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2) | spl3_7),
% 0.19/0.48    inference(avatar_component_clause,[],[f90])).
% 0.19/0.48  fof(f94,plain,(
% 0.19/0.48    ~spl3_7 | spl3_5),
% 0.19/0.48    inference(avatar_split_clause,[],[f88,f71,f90])).
% 0.19/0.48  fof(f71,plain,(
% 0.19/0.48    spl3_5 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK2,sK0,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.48  fof(f88,plain,(
% 0.19/0.48    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2) | spl3_5),
% 0.19/0.48    inference(superposition,[],[f73,f35])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.19/0.48  fof(f73,plain,(
% 0.19/0.48    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK2,sK0,sK1) | spl3_5),
% 0.19/0.48    inference(avatar_component_clause,[],[f71])).
% 0.19/0.48  fof(f75,plain,(
% 0.19/0.48    ~spl3_5 | spl3_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f59,f52,f71])).
% 0.19/0.48  fof(f52,plain,(
% 0.19/0.48    spl3_2 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.48  % (22510)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.49  % (22509)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.49  % (22503)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.49  fof(f59,plain,(
% 0.19/0.49    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK2,sK0,sK1) | spl3_2),
% 0.19/0.49    inference(superposition,[],[f54,f37])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 0.19/0.49  fof(f54,plain,(
% 0.19/0.49    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | spl3_2),
% 0.19/0.49    inference(avatar_component_clause,[],[f52])).
% 0.19/0.49  fof(f55,plain,(
% 0.19/0.49    ~spl3_2 | spl3_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f50,f46,f52])).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | spl3_1),
% 0.19/0.49    inference(superposition,[],[f48,f39])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) | spl3_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f46])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    ~spl3_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f25,f46])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.19/0.49    inference(cnf_transformation,[],[f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.19/0.49    inference(negated_conjecture,[],[f20])).
% 0.19/0.49  fof(f20,conjecture,(
% 0.19/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (22511)------------------------------
% 0.19/0.49  % (22511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (22511)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (22511)Memory used [KB]: 10618
% 0.19/0.49  % (22511)Time elapsed: 0.065 s
% 0.19/0.49  % (22511)------------------------------
% 0.19/0.49  % (22511)------------------------------
% 0.19/0.49  % (22499)Success in time 0.135 s
%------------------------------------------------------------------------------
