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
% DateTime   : Thu Dec  3 12:33:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 (  83 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f41,f51,f56,f61,f121,f132])).

fof(f132,plain,
    ( spl7_1
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl7_1
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f24,f130])).

fof(f130,plain,
    ( ! [X30,X28,X33,X31,X29,X27,X32] : k2_xboole_0(k4_enumset1(X31,X32,X33,X27,X28,X29),k1_tarski(X30)) = k5_enumset1(X31,X32,X33,X27,X28,X29,X30)
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f125,f60])).

fof(f60,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_8
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f125,plain,
    ( ! [X30,X28,X33,X31,X29,X27,X32] : k2_xboole_0(k4_enumset1(X31,X32,X33,X27,X28,X29),k1_tarski(X30)) = k2_xboole_0(k1_enumset1(X31,X32,X33),k2_enumset1(X27,X28,X29,X30))
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(superposition,[],[f120,f50])).

fof(f50,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl7_6
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f120,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl7_14
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f24,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl7_1
  <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) = k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f121,plain,
    ( spl7_14
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f57,f54,f39,f119])).

fof(f39,plain,
    ( spl7_5
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f54,plain,
    ( spl7_7
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f57,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6)
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(superposition,[],[f40,f55])).

fof(f55,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f40,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f61,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f20,f59])).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

fof(f56,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f19,f54])).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f51,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f18,f49])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f41,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f25,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f13,f22])).

fof(f13,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:24:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (9436)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (9435)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (9442)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (9432)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (9444)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (9434)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (9443)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (9436)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f25,f41,f51,f56,f61,f121,f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl7_1 | ~spl7_6 | ~spl7_8 | ~spl7_14),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    $false | (spl7_1 | ~spl7_6 | ~spl7_8 | ~spl7_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f24,f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X30,X28,X33,X31,X29,X27,X32] : (k2_xboole_0(k4_enumset1(X31,X32,X33,X27,X28,X29),k1_tarski(X30)) = k5_enumset1(X31,X32,X33,X27,X28,X29,X30)) ) | (~spl7_6 | ~spl7_8 | ~spl7_14)),
% 0.21/0.48    inference(forward_demodulation,[],[f125,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) ) | ~spl7_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl7_8 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ( ! [X30,X28,X33,X31,X29,X27,X32] : (k2_xboole_0(k4_enumset1(X31,X32,X33,X27,X28,X29),k1_tarski(X30)) = k2_xboole_0(k1_enumset1(X31,X32,X33),k2_enumset1(X27,X28,X29,X30))) ) | (~spl7_6 | ~spl7_14)),
% 0.21/0.48    inference(superposition,[],[f120,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | ~spl7_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl7_6 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6)) ) | ~spl7_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl7_14 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) | spl7_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    spl7_1 <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) = k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl7_14 | ~spl7_5 | ~spl7_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f57,f54,f39,f119])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl7_5 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl7_7 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6)) ) | (~spl7_5 | ~spl7_7)),
% 0.21/0.48    inference(superposition,[],[f40,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) ) | ~spl7_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f54])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl7_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f39])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl7_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f59])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl7_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f54])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl7_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f49])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl7_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f39])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ~spl7_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f22])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (9436)------------------------------
% 0.21/0.48  % (9436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9436)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (9436)Memory used [KB]: 6140
% 0.21/0.48  % (9436)Time elapsed: 0.055 s
% 0.21/0.48  % (9436)------------------------------
% 0.21/0.48  % (9436)------------------------------
% 0.21/0.49  % (9430)Success in time 0.121 s
%------------------------------------------------------------------------------
