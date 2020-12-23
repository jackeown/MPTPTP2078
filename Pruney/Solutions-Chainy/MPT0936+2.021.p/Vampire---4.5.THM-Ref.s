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
% DateTime   : Thu Dec  3 12:59:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  29 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  50 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f21,f30,f34])).

fof(f34,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f33])).

fof(f33,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f16,f32])).

fof(f32,plain,
    ( ! [X2,X0,X1] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f31,f20])).

fof(f20,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl3_2
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f31,plain,
    ( ! [X2,X0,X1] : k2_tarski(X0,X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(superposition,[],[f29,f20])).

fof(f29,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_4
  <=> ! [X1,X3,X5,X0,X2,X4] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f16,plain,
    ( k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f14,plain,
    ( spl3_1
  <=> k1_tarski(sK0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f30,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f12,f28])).

fof(f12,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_mcart_1)).

fof(f21,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f10,f19])).

fof(f10,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f17,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f9,f14])).

fof(f9,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))
   => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:14:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (17373)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (17379)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (17376)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (17376)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f17,f21,f30,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl3_1 | ~spl3_2 | ~spl3_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    $false | (spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f16,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))) ) | (~spl3_2 | ~spl3_4)),
% 0.21/0.47    inference(forward_demodulation,[],[f31,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    spl3_2 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))) ) | (~spl3_2 | ~spl3_4)),
% 0.21/0.47    inference(superposition,[],[f29,f20])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3)) ) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    spl3_4 <=> ! [X1,X3,X5,X0,X2,X4] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    spl3_1 <=> k1_tarski(sK0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f12,f28])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_mcart_1)).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f10,f19])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f9,f14])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (17376)------------------------------
% 0.21/0.47  % (17376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (17376)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (17376)Memory used [KB]: 6140
% 0.21/0.47  % (17376)Time elapsed: 0.052 s
% 0.21/0.47  % (17376)------------------------------
% 0.21/0.47  % (17376)------------------------------
% 0.21/0.47  % (17370)Success in time 0.11 s
%------------------------------------------------------------------------------
