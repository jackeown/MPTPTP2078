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
% DateTime   : Thu Dec  3 12:34:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   18 (  21 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   23 (  27 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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
    ( k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3))
    | spl4_1 ),
    inference(backward_demodulation,[],[f15,f9])).

fof(f9,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

fof(f15,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) != k2_xboole_0(k1_enumset1(sK1,sK0,sK2),k1_tarski(sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f13])).

fof(f13,plain,
    ( spl4_1
  <=> k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) = k2_xboole_0(k1_enumset1(sK1,sK0,sK2),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f16,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f11,f13])).

fof(f11,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) != k2_xboole_0(k1_enumset1(sK1,sK0,sK2),k1_tarski(sK3)) ),
    inference(definition_unfolding,[],[f8,f10,f10])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:37:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (30685)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (30681)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (30687)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (30687)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f16,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    spl4_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    $false | spl4_1),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) | spl4_1),
% 0.21/0.47    inference(backward_demodulation,[],[f15,f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) != k2_xboole_0(k1_enumset1(sK1,sK0,sK2),k1_tarski(sK3)) | spl4_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    spl4_1 <=> k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) = k2_xboole_0(k1_enumset1(sK1,sK0,sK2),k1_tarski(sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ~spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f11,f13])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) != k2_xboole_0(k1_enumset1(sK1,sK0,sK2),k1_tarski(sK3))),
% 0.21/0.47    inference(definition_unfolding,[],[f8,f10,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.21/0.47    inference(negated_conjecture,[],[f3])).
% 0.21/0.47  fof(f3,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (30687)------------------------------
% 0.21/0.47  % (30687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30687)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (30687)Memory used [KB]: 6140
% 0.21/0.47  % (30687)Time elapsed: 0.062 s
% 0.21/0.47  % (30687)------------------------------
% 0.21/0.47  % (30687)------------------------------
% 0.21/0.48  % (30678)Success in time 0.112 s
%------------------------------------------------------------------------------
