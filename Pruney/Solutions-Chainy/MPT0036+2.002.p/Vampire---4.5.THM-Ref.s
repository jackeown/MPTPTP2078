%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   43 (  53 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f26,f39,f49])).

fof(f49,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f48])).

fof(f48,plain,
    ( $false
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f41,f10])).

fof(f10,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f41,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK2))
    | ~ spl3_4 ),
    inference(superposition,[],[f37,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f37,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(X0,k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_4
  <=> ! [X0] : ~ r1_tarski(k2_xboole_0(X0,k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f39,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f29,f24,f36])).

fof(f24,plain,
    ( spl3_2
  <=> ! [X0] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X0),k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f29,plain,
    ( ! [X1] : ~ r1_tarski(k2_xboole_0(X1,k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK2))
    | ~ spl3_2 ),
    inference(superposition,[],[f25,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f25,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X0),k2_xboole_0(sK0,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f26,plain,
    ( spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f22,f15,f24])).

fof(f15,plain,
    ( spl3_1
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f22,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X0),k2_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(resolution,[],[f13,f17])).

fof(f17,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f18,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f9,f15])).

fof(f9,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] : ~ r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (2458)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.41  % (2463)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.41  % (2464)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (2458)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f18,f26,f39,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    ~spl3_4),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f48])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    $false | ~spl3_4),
% 0.21/0.42    inference(subsumption_resolution,[],[f41,f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    ~r1_tarski(sK0,k2_xboole_0(sK0,sK2)) | ~spl3_4),
% 0.21/0.42    inference(superposition,[],[f37,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK2))) ) | ~spl3_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl3_4 <=> ! [X0] : ~r1_tarski(k2_xboole_0(X0,k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    spl3_4 | ~spl3_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f24,f36])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    spl3_2 <=> ! [X0] : ~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X0),k2_xboole_0(sK0,sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X1] : (~r1_tarski(k2_xboole_0(X1,k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK2))) ) | ~spl3_2),
% 0.21/0.42    inference(superposition,[],[f25,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X0),k2_xboole_0(sK0,sK2))) ) | ~spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f24])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    spl3_2 | spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f15,f24])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    spl3_1 <=> r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X0),k2_xboole_0(sK0,sK2))) ) | spl3_1),
% 0.21/0.42    inference(resolution,[],[f13,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ~r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) | spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f15])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ~spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f9,f15])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ~r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0,X1,X2] : ~r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.42    inference(negated_conjecture,[],[f5])).
% 0.21/0.42  fof(f5,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (2458)------------------------------
% 0.21/0.42  % (2458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (2458)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (2458)Memory used [KB]: 10618
% 0.21/0.42  % (2458)Time elapsed: 0.006 s
% 0.21/0.42  % (2458)------------------------------
% 0.21/0.42  % (2458)------------------------------
% 0.21/0.42  % (2454)Success in time 0.063 s
%------------------------------------------------------------------------------
