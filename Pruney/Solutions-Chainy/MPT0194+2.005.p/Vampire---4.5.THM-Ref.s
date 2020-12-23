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
% DateTime   : Thu Dec  3 12:34:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  24 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f39,f55])).

fof(f55,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | spl4_4 ),
    inference(trivial_inequality_removal,[],[f53])).

fof(f53,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)
    | spl4_4 ),
    inference(superposition,[],[f38,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

fof(f38,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK0,sK3)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_4
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f39,plain,
    ( ~ spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f23,f16,f36])).

fof(f16,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK3,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f23,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK0,sK3)
    | spl4_1 ),
    inference(superposition,[],[f18,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f18,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f19,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f10,f16])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:31:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (23801)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (23802)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (23802)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f19,f39,f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    spl4_4),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    $false | spl4_4),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3) | spl4_4),
% 0.20/0.46    inference(superposition,[],[f38,f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK0,sK3) | spl4_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    spl4_4 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK2,sK0,sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ~spl4_4 | spl4_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f16,f36])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK0,sK3) | spl4_1),
% 0.20/0.46    inference(superposition,[],[f18,f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) | spl4_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f16])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ~spl4_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f10,f16])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (23802)------------------------------
% 0.20/0.46  % (23802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (23802)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (23802)Memory used [KB]: 10618
% 0.20/0.46  % (23802)Time elapsed: 0.048 s
% 0.20/0.46  % (23802)------------------------------
% 0.20/0.46  % (23802)------------------------------
% 0.20/0.46  % (23794)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (23786)Success in time 0.107 s
%------------------------------------------------------------------------------
