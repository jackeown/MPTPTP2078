%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  61 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f23,f27,f39,f46])).

fof(f46,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f44])).

fof(f44,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f42,f26])).

fof(f26,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_3
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f42,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | spl3_2
    | ~ spl3_5 ),
    inference(superposition,[],[f22,f38])).

fof(f38,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f22,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl3_2
  <=> k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f39,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f12,f37])).

fof(f12,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f27,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f10,f25])).

fof(f10,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

fof(f23,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f18,f14,f20])).

fof(f14,plain,
    ( spl3_1
  <=> k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f18,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f16,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f16,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f17,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f9,f14])).

fof(f9,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))
   => k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (28989)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (28989)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (28998)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (28997)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f17,f23,f27,f39,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl3_2 | ~spl3_3 | ~spl3_5),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    $false | (spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | (spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.21/0.47    inference(forward_demodulation,[],[f42,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    spl3_3 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) | (spl3_2 | ~spl3_5)),
% 0.21/0.47    inference(superposition,[],[f22,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl3_5 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    spl3_2 <=> k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f12,f37])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f10,f25])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ~spl3_2 | spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f18,f14,f20])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    spl3_1 <=> k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | spl3_1),
% 0.21/0.47    inference(forward_demodulation,[],[f16,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f14])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f9,f14])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) => k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_xboole_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (28989)------------------------------
% 0.21/0.47  % (28989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (28989)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (28989)Memory used [KB]: 6140
% 0.21/0.47  % (28989)Time elapsed: 0.042 s
% 0.21/0.47  % (28989)------------------------------
% 0.21/0.47  % (28989)------------------------------
% 0.21/0.47  % (28987)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (28983)Success in time 0.112 s
%------------------------------------------------------------------------------
