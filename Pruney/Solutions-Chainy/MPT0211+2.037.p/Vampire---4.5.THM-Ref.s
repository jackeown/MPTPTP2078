%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:47 EST 2020

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   33 (  40 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  64 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f57,f67,f101,f120])).

fof(f120,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl3_7 ),
    inference(trivial_inequality_removal,[],[f118])).

fof(f118,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | spl3_7 ),
    inference(superposition,[],[f93,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f93,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_7
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f101,plain,
    ( ~ spl3_7
    | spl3_3 ),
    inference(avatar_split_clause,[],[f87,f64,f91])).

fof(f64,plain,
    ( spl3_3
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f87,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)
    | spl3_3 ),
    inference(superposition,[],[f66,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

fof(f66,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK2,sK1,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f67,plain,
    ( ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f58,f54,f64])).

fof(f54,plain,
    ( spl3_2
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f58,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK2,sK1,sK0)
    | spl3_2 ),
    inference(superposition,[],[f56,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).

fof(f56,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f57,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f52,f48,f54])).

fof(f48,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f52,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_1 ),
    inference(superposition,[],[f50,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f50,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f51,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:34:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (739803137)
% 0.15/0.37  ipcrm: permission denied for id (739868677)
% 0.15/0.38  ipcrm: permission denied for id (739966990)
% 0.15/0.39  ipcrm: permission denied for id (739999764)
% 0.15/0.40  ipcrm: permission denied for id (740065305)
% 0.22/0.42  ipcrm: permission denied for id (740294699)
% 0.22/0.43  ipcrm: permission denied for id (740425785)
% 0.22/0.44  ipcrm: permission denied for id (740458555)
% 0.22/0.45  ipcrm: permission denied for id (740556868)
% 0.22/0.45  ipcrm: permission denied for id (740589640)
% 0.22/0.49  ipcrm: permission denied for id (740819047)
% 0.22/0.49  ipcrm: permission denied for id (740851816)
% 0.22/0.49  ipcrm: permission denied for id (740917355)
% 0.22/0.49  ipcrm: permission denied for id (740950124)
% 0.22/0.50  ipcrm: permission denied for id (740982899)
% 0.22/0.51  ipcrm: permission denied for id (741048440)
% 0.22/0.51  ipcrm: permission denied for id (741146747)
% 0.22/0.51  ipcrm: permission denied for id (741212284)
% 0.22/0.51  ipcrm: permission denied for id (741245053)
% 0.22/0.51  ipcrm: permission denied for id (741277822)
% 0.22/0.56  % (9221)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.73/0.59  % (9212)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.73/0.60  % (9219)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.73/0.60  % (9219)Refutation found. Thanks to Tanya!
% 0.73/0.60  % SZS status Theorem for theBenchmark
% 0.73/0.60  % SZS output start Proof for theBenchmark
% 0.73/0.60  fof(f121,plain,(
% 0.73/0.60    $false),
% 0.73/0.60    inference(avatar_sat_refutation,[],[f51,f57,f67,f101,f120])).
% 0.73/0.60  fof(f120,plain,(
% 0.73/0.60    spl3_7),
% 0.73/0.60    inference(avatar_contradiction_clause,[],[f119])).
% 0.73/0.60  fof(f119,plain,(
% 0.73/0.60    $false | spl3_7),
% 0.73/0.60    inference(trivial_inequality_removal,[],[f118])).
% 0.73/0.60  fof(f118,plain,(
% 0.73/0.60    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) | spl3_7),
% 0.73/0.60    inference(superposition,[],[f93,f33])).
% 0.73/0.60  fof(f33,plain,(
% 0.73/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.73/0.60    inference(cnf_transformation,[],[f18])).
% 0.73/0.60  fof(f18,axiom,(
% 0.73/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.73/0.60  fof(f93,plain,(
% 0.73/0.60    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) | spl3_7),
% 0.73/0.60    inference(avatar_component_clause,[],[f91])).
% 0.73/0.60  fof(f91,plain,(
% 0.73/0.60    spl3_7 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.73/0.60  fof(f101,plain,(
% 0.73/0.60    ~spl3_7 | spl3_3),
% 0.73/0.60    inference(avatar_split_clause,[],[f87,f64,f91])).
% 0.73/0.60  fof(f64,plain,(
% 0.73/0.60    spl3_3 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK2,sK1,sK0)),
% 0.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.73/0.60  fof(f87,plain,(
% 0.73/0.60    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) | spl3_3),
% 0.73/0.60    inference(superposition,[],[f66,f37])).
% 0.73/0.60  fof(f37,plain,(
% 0.73/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 0.73/0.60    inference(cnf_transformation,[],[f9])).
% 0.73/0.60  fof(f9,axiom,(
% 0.73/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
% 0.73/0.60  fof(f66,plain,(
% 0.73/0.60    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK2,sK1,sK0) | spl3_3),
% 0.73/0.60    inference(avatar_component_clause,[],[f64])).
% 0.73/0.60  fof(f67,plain,(
% 0.73/0.60    ~spl3_3 | spl3_2),
% 0.73/0.60    inference(avatar_split_clause,[],[f58,f54,f64])).
% 0.73/0.60  fof(f54,plain,(
% 0.73/0.60    spl3_2 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0)),
% 0.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.73/0.60  fof(f58,plain,(
% 0.73/0.60    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK2,sK1,sK0) | spl3_2),
% 0.73/0.60    inference(superposition,[],[f56,f36])).
% 0.73/0.60  fof(f36,plain,(
% 0.73/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)) )),
% 0.73/0.60    inference(cnf_transformation,[],[f10])).
% 0.73/0.60  fof(f10,axiom,(
% 0.73/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 0.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).
% 0.73/0.60  fof(f56,plain,(
% 0.73/0.60    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | spl3_2),
% 0.73/0.60    inference(avatar_component_clause,[],[f54])).
% 0.73/0.60  fof(f57,plain,(
% 0.73/0.60    ~spl3_2 | spl3_1),
% 0.73/0.60    inference(avatar_split_clause,[],[f52,f48,f54])).
% 0.73/0.60  fof(f48,plain,(
% 0.73/0.60    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.73/0.60  fof(f52,plain,(
% 0.73/0.60    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | spl3_1),
% 0.73/0.60    inference(superposition,[],[f50,f40])).
% 0.73/0.60  fof(f40,plain,(
% 0.73/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.73/0.60    inference(cnf_transformation,[],[f6])).
% 0.73/0.60  fof(f6,axiom,(
% 0.73/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.73/0.60  fof(f50,plain,(
% 0.73/0.60    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) | spl3_1),
% 0.73/0.60    inference(avatar_component_clause,[],[f48])).
% 0.73/0.60  fof(f51,plain,(
% 0.73/0.60    ~spl3_1),
% 0.73/0.60    inference(avatar_split_clause,[],[f26,f48])).
% 0.73/0.60  fof(f26,plain,(
% 0.73/0.60    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.73/0.60    inference(cnf_transformation,[],[f25])).
% 0.73/0.60  fof(f25,plain,(
% 0.73/0.60    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.73/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).
% 0.73/0.60  fof(f24,plain,(
% 0.73/0.60    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.73/0.60    introduced(choice_axiom,[])).
% 0.73/0.60  fof(f23,plain,(
% 0.73/0.60    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.73/0.60    inference(ennf_transformation,[],[f22])).
% 0.73/0.60  fof(f22,negated_conjecture,(
% 0.73/0.60    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.73/0.60    inference(negated_conjecture,[],[f21])).
% 0.73/0.60  fof(f21,conjecture,(
% 0.73/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 0.73/0.60  % SZS output end Proof for theBenchmark
% 0.73/0.60  % (9219)------------------------------
% 0.73/0.60  % (9219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.73/0.60  % (9219)Termination reason: Refutation
% 0.73/0.60  
% 0.73/0.60  % (9219)Memory used [KB]: 10618
% 0.73/0.60  % (9219)Time elapsed: 0.051 s
% 0.73/0.60  % (9219)------------------------------
% 0.73/0.60  % (9219)------------------------------
% 0.73/0.60  % (9074)Success in time 0.234 s
%------------------------------------------------------------------------------
