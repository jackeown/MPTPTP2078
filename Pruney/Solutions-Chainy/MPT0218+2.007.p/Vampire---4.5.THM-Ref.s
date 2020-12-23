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
% DateTime   : Thu Dec  3 12:35:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  41 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  58 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f39,f43,f46])).

fof(f46,plain,
    ( ~ spl2_2
    | spl2_4
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | ~ spl2_2
    | spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f38,f44])).

fof(f44,plain,
    ( ! [X2,X1] : r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f28,f42])).

fof(f42,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_5
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f28,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_2
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f38,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_4
  <=> r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f43,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f16,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f39,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f21,f36])).

fof(f21,plain,(
    ~ r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)) ),
    inference(forward_demodulation,[],[f20,f19])).

fof(f20,plain,(
    ~ r1_tarski(k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f12,f18])).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f13,f17])).

fof(f13,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f12,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))
   => ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f29,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f15,f27])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:31:30 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.48  % (18543)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (18542)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (18537)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (18542)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f29,f39,f43,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ~spl2_2 | spl2_4 | ~spl2_5),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    $false | (~spl2_2 | spl2_4 | ~spl2_5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f38,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))) ) | (~spl2_2 | ~spl2_5)),
% 0.22/0.49    inference(superposition,[],[f28,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) ) | ~spl2_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    spl2_5 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    spl2_2 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ~r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)) | spl2_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    spl2_4 <=> r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    spl2_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f19,f41])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f16,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ~spl2_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f21,f36])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ~r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))),
% 0.22/0.49    inference(forward_demodulation,[],[f20,f19])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ~r1_tarski(k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1))),
% 0.22/0.49    inference(definition_unfolding,[],[f12,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f13,f17])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) => ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.49    inference(negated_conjecture,[],[f6])).
% 0.22/0.49  fof(f6,conjecture,(
% 0.22/0.49    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f15,f27])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (18542)------------------------------
% 0.22/0.49  % (18542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (18542)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (18542)Memory used [KB]: 6012
% 0.22/0.49  % (18542)Time elapsed: 0.058 s
% 0.22/0.49  % (18542)------------------------------
% 0.22/0.49  % (18542)------------------------------
% 0.22/0.49  % (18541)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (18538)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (18534)Success in time 0.114 s
%------------------------------------------------------------------------------
