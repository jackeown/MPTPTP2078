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
% DateTime   : Thu Dec  3 12:36:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  34 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  44 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f39])).

fof(f39,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f34])).

fof(f34,plain,
    ( $false
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f23,f19,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f13,f17,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f17,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f12,f14])).

fof(f12,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f23,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f24,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f18,f21])).

fof(f18,plain,(
    k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f11,f17,f14])).

fof(f11,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1] : k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:02:30 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.45  % (7030)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.45  % (7030)Refutation not found, incomplete strategy% (7030)------------------------------
% 0.21/0.45  % (7030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (7030)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (7030)Memory used [KB]: 10490
% 0.21/0.45  % (7030)Time elapsed: 0.003 s
% 0.21/0.45  % (7030)------------------------------
% 0.21/0.45  % (7030)------------------------------
% 0.21/0.47  % (7029)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (7025)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (7025)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f24,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl2_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    $false | spl2_1),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f23,f19,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f13,f17,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f12,f14])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) | spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    spl2_1 <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ~spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f18,f21])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.47    inference(definition_unfolding,[],[f11,f17,f14])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (7025)------------------------------
% 0.21/0.47  % (7025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7025)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (7025)Memory used [KB]: 6140
% 0.21/0.47  % (7025)Time elapsed: 0.059 s
% 0.21/0.47  % (7025)------------------------------
% 0.21/0.47  % (7025)------------------------------
% 0.21/0.47  % (7018)Success in time 0.116 s
%------------------------------------------------------------------------------
