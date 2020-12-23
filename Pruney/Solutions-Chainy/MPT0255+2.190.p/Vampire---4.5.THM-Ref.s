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
% DateTime   : Thu Dec  3 12:39:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f28])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f27])).

fof(f27,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f22,f10])).

fof(f10,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f22,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),sK2))
    | ~ spl3_1 ),
    inference(superposition,[],[f17,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f17,plain,
    ( k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl3_1
  <=> k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f18,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f13,f15])).

fof(f13,plain,(
    k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f9,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f9,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:37:06 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.45  % (2352)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.46  % (2352)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f18,f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ~spl3_1),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    $false | ~spl3_1),
% 0.22/0.46    inference(subsumption_resolution,[],[f22,f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),sK2)) | ~spl3_1),
% 0.22/0.46    inference(superposition,[],[f17,f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) | ~spl3_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    spl3_1 <=> k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    spl3_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f13,f15])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 0.22/0.46    inference(definition_unfolding,[],[f9,f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,plain,(
% 0.22/0.46    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).
% 0.22/0.46  fof(f7,plain,(
% 0.22/0.46    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f6,plain,(
% 0.22/0.46    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.22/0.46    inference(negated_conjecture,[],[f4])).
% 0.22/0.46  fof(f4,conjecture,(
% 0.22/0.46    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (2352)------------------------------
% 0.22/0.46  % (2352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (2352)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (2352)Memory used [KB]: 10618
% 0.22/0.46  % (2352)Time elapsed: 0.007 s
% 0.22/0.46  % (2352)------------------------------
% 0.22/0.46  % (2352)------------------------------
% 0.22/0.46  % (2334)Success in time 0.099 s
%------------------------------------------------------------------------------
