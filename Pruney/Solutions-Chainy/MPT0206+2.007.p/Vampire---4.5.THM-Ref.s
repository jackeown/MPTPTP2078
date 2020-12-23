%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  42 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 (  78 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f29,f41,f50,f65,f73])).

fof(f73,plain,
    ( spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f20,f71])).

fof(f71,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X6,X7,X8,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k7_enumset1(X6,X7,X8,X0,X1,X2,X3,X4,X5)
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(forward_demodulation,[],[f66,f49])).

fof(f49,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl9_7
  <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f66,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X6,X7,X8,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k1_enumset1(X6,X7,X8),k4_enumset1(X0,X1,X2,X3,X4,X5))
    | ~ spl9_5
    | ~ spl9_8 ),
    inference(superposition,[],[f64,f40])).

fof(f40,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl9_5
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f64,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl9_8
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f20,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl9_1
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f65,plain,
    ( spl9_8
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f42,f39,f27,f63])).

fof(f27,plain,
    ( spl9_3
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f42,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(superposition,[],[f28,f40])).

fof(f28,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f50,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f16,f48])).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

fof(f41,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

fof(f29,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f21,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f11,f18])).

fof(f11,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:10:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (23435)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (23425)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (23429)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (23429)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f21,f29,f41,f50,f65,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f72])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    $false | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8)),
% 0.20/0.47    inference(subsumption_resolution,[],[f20,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X6,X7,X8,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k7_enumset1(X6,X7,X8,X0,X1,X2,X3,X4,X5)) ) | (~spl9_5 | ~spl9_7 | ~spl9_8)),
% 0.20/0.47    inference(forward_demodulation,[],[f66,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))) ) | ~spl9_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl9_7 <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X6,X7,X8,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k1_enumset1(X6,X7,X8),k4_enumset1(X0,X1,X2,X3,X4,X5))) ) | (~spl9_5 | ~spl9_8)),
% 0.20/0.47    inference(superposition,[],[f64,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) ) | ~spl9_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl9_5 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6)) ) | ~spl9_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl9_8 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) | spl9_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    spl9_1 <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl9_8 | ~spl9_3 | ~spl9_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f42,f39,f27,f63])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    spl9_3 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6)) ) | (~spl9_3 | ~spl9_5)),
% 0.20/0.47    inference(superposition,[],[f28,f40])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl9_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f27])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl9_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f16,f48])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    spl9_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f15,f39])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    spl9_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f13,f27])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ~spl9_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f11,f18])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f8,f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.20/0.47    inference(negated_conjecture,[],[f6])).
% 0.20/0.47  fof(f6,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (23429)------------------------------
% 0.20/0.47  % (23429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (23429)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (23429)Memory used [KB]: 6140
% 0.20/0.47  % (23429)Time elapsed: 0.051 s
% 0.20/0.47  % (23429)------------------------------
% 0.20/0.47  % (23429)------------------------------
% 0.20/0.47  % (23427)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (23423)Success in time 0.114 s
%------------------------------------------------------------------------------
