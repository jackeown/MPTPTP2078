%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   18 (  19 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f16,f19])).

fof(f19,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f18])).

fof(f18,plain,
    ( $false
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f17])).

fof(f17,plain,
    ( k4_mcart_1(sK0,sK1,sK2,sK3) != k4_mcart_1(sK0,sK1,sK2,sK3)
    | spl4_1 ),
    inference(superposition,[],[f15,f10])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f15,plain,
    ( k4_mcart_1(sK0,sK1,sK2,sK3) != k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f13])).

fof(f13,plain,
    ( spl4_1
  <=> k4_mcart_1(sK0,sK1,sK2,sK3) = k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f16,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f11,f13])).

fof(f11,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) ),
    inference(forward_demodulation,[],[f8,f9])).

fof(f9,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f8,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)
   => k4_mcart_1(sK0,sK1,sK2,sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (31624)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.41  % (31624)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f16,f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    spl4_1),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    $false | spl4_1),
% 0.20/0.41    inference(trivial_inequality_removal,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    k4_mcart_1(sK0,sK1,sK2,sK3) != k4_mcart_1(sK0,sK1,sK2,sK3) | spl4_1),
% 0.20/0.41    inference(superposition,[],[f15,f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    k4_mcart_1(sK0,sK1,sK2,sK3) != k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) | spl4_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    spl4_1 <=> k4_mcart_1(sK0,sK1,sK2,sK3) = k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ~spl4_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f11,f13])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    k4_mcart_1(sK0,sK1,sK2,sK3) != k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3)),
% 0.20/0.41    inference(forward_demodulation,[],[f8,f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    k4_mcart_1(sK0,sK1,sK2,sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)),
% 0.20/0.41    inference(cnf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,plain,(
% 0.20/0.41    k4_mcart_1(sK0,sK1,sK2,sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).
% 0.20/0.41  fof(f6,plain,(
% 0.20/0.41    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) => k4_mcart_1(sK0,sK1,sK2,sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f5,plain,(
% 0.20/0.41    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.20/0.41    inference(negated_conjecture,[],[f3])).
% 0.20/0.41  fof(f3,conjecture,(
% 0.20/0.41    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (31624)------------------------------
% 0.20/0.41  % (31624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (31624)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (31624)Memory used [KB]: 10490
% 0.20/0.41  % (31624)Time elapsed: 0.003 s
% 0.20/0.41  % (31624)------------------------------
% 0.20/0.41  % (31624)------------------------------
% 0.20/0.41  % (31612)Success in time 0.057 s
%------------------------------------------------------------------------------
