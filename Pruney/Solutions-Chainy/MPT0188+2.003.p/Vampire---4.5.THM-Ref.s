%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  32 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f27,f41,f55])).

fof(f55,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | spl4_4 ),
    inference(trivial_inequality_removal,[],[f50])).

fof(f50,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)
    | spl4_4 ),
    inference(superposition,[],[f39,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

fof(f39,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl4_4
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f41,plain,
    ( ~ spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f35,f23,f37])).

fof(f23,plain,
    ( spl4_2
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f35,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)
    | spl4_2 ),
    inference(superposition,[],[f25,f10])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f25,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f27,plain,
    ( ~ spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f19,f14,f23])).

fof(f14,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f19,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1)
    | spl4_1 ),
    inference(superposition,[],[f16,f11])).

fof(f16,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f17,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f9,f14])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:19:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (4838)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (4838)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f17,f27,f41,f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl4_4),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    $false | spl4_4),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3) | spl4_4),
% 0.21/0.46    inference(superposition,[],[f39,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) | spl4_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    spl4_4 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ~spl4_4 | spl4_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f35,f23,f37])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    spl4_2 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK3,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) | spl4_2),
% 0.21/0.46    inference(superposition,[],[f25,f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1) | spl4_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f23])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ~spl4_2 | spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f14,f23])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK3,sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1) | spl4_1),
% 0.21/0.47    inference(superposition,[],[f16,f11])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) | spl4_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f14])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ~spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f9,f14])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (4838)------------------------------
% 0.21/0.47  % (4838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (4838)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (4838)Memory used [KB]: 10618
% 0.21/0.47  % (4838)Time elapsed: 0.007 s
% 0.21/0.47  % (4838)------------------------------
% 0.21/0.47  % (4838)------------------------------
% 0.21/0.47  % (4821)Success in time 0.106 s
%------------------------------------------------------------------------------
