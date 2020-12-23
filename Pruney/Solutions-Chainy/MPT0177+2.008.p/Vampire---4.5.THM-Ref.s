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
% DateTime   : Thu Dec  3 12:34:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  18 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f15,f18])).

fof(f18,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f17])).

fof(f17,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f16,f9])).

fof(f9,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f16,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)
    | spl3_1 ),
    inference(superposition,[],[f14,f10])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).

fof(f14,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f12])).

fof(f12,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f15,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f8,f12])).

fof(f8,plain,(
    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:10:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.41  % (32136)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (32136)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f15,f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    spl3_1),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    $false | spl3_1),
% 0.22/0.46    inference(subsumption_resolution,[],[f16,f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) | spl3_1),
% 0.22/0.46    inference(superposition,[],[f14,f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) | spl3_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ~spl3_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f8,f12])).
% 0.22/0.46  fof(f8,plain,(
% 0.22/0.46    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,plain,(
% 0.22/0.46    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).
% 0.22/0.46  fof(f6,plain,(
% 0.22/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f5,plain,(
% 0.22/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)),
% 0.22/0.46    inference(negated_conjecture,[],[f3])).
% 0.22/0.46  fof(f3,conjecture,(
% 0.22/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (32136)------------------------------
% 0.22/0.46  % (32136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (32136)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (32136)Memory used [KB]: 6012
% 0.22/0.47  % (32136)Time elapsed: 0.056 s
% 0.22/0.47  % (32136)------------------------------
% 0.22/0.47  % (32136)------------------------------
% 0.22/0.47  % (32135)Success in time 0.111 s
%------------------------------------------------------------------------------
