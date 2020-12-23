%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  48 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  59 expanded)
%              Number of equality atoms :   18 (  44 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f25,f32])).

fof(f32,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f28])).

fof(f28,plain,
    ( $false
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f12,f24])).

fof(f24,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl3_2
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f12,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f10,f9,f9,f9])).

fof(f9,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f10,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f25,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f18,f14,f22])).

fof(f14,plain,
    ( spl3_1
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f18,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))
    | spl3_1 ),
    inference(backward_demodulation,[],[f16,f12])).

fof(f16,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f17,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f11,f14])).

fof(f11,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f8,f9,f9,f9,f9,f9])).

fof(f8,plain,(
    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:21:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (31019)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (31023)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (31029)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (31023)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f17,f25,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    $false | spl3_2),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f12,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) | spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    spl3_2 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f10,f9,f9,f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ~spl3_2 | spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f18,f14,f22])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    spl3_1 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) | spl3_1),
% 0.21/0.47    inference(backward_demodulation,[],[f16,f12])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f14])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f11,f14])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))))),
% 0.21/0.47    inference(definition_unfolding,[],[f8,f9,f9,f9,f9,f9])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.47    inference(negated_conjecture,[],[f3])).
% 0.21/0.47  fof(f3,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_xboole_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (31023)------------------------------
% 0.21/0.47  % (31023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (31023)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (31023)Memory used [KB]: 6140
% 0.21/0.47  % (31023)Time elapsed: 0.061 s
% 0.21/0.47  % (31023)------------------------------
% 0.21/0.47  % (31023)------------------------------
% 0.21/0.47  % (31027)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (31016)Success in time 0.113 s
%------------------------------------------------------------------------------
