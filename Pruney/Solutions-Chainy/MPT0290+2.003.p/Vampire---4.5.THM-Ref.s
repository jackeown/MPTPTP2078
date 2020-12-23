%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  62 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f34,f37])).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f36])).

fof(f36,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f35,f16])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f12,f13])).

fof(f13,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f12,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f35,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | spl2_2 ),
    inference(resolution,[],[f30,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f30,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_2
  <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f34,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f33])).

fof(f33,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f32,f12])).

fof(f32,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl2_1 ),
    inference(resolution,[],[f26,f14])).

fof(f26,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_1
  <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f31,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f20,f28,f24])).

% (9742)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f20,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1))
    | ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0)) ),
    inference(resolution,[],[f15,f11])).

fof(f11,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:58:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.41  % (9743)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.19/0.41  % (9736)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.19/0.41  % (9738)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.19/0.42  % (9736)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f31,f34,f37])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    spl2_2),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f36])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    $false | spl2_2),
% 0.19/0.42    inference(subsumption_resolution,[],[f35,f16])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.19/0.42    inference(superposition,[],[f12,f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.19/0.42  fof(f35,plain,(
% 0.19/0.42    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | spl2_2),
% 0.19/0.42    inference(resolution,[],[f30,f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1)) | spl2_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f28])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    spl2_2 <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    spl2_1),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f33])).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    $false | spl2_1),
% 0.19/0.42    inference(subsumption_resolution,[],[f32,f12])).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | spl2_1),
% 0.19/0.42    inference(resolution,[],[f26,f14])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0)) | spl2_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    spl2_1 <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    ~spl2_1 | ~spl2_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f20,f28,f24])).
% 0.19/0.42  % (9742)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1)) | ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0))),
% 0.19/0.42    inference(resolution,[],[f15,f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.19/0.42    inference(cnf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,plain,(
% 0.19/0.42    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.19/0.42    inference(ennf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.19/0.42    inference(negated_conjecture,[],[f5])).
% 0.19/0.42  fof(f5,conjecture,(
% 0.19/0.42    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.42    inference(flattening,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.42    inference(ennf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (9736)------------------------------
% 0.19/0.42  % (9736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (9736)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (9736)Memory used [KB]: 10490
% 0.19/0.42  % (9736)Time elapsed: 0.005 s
% 0.19/0.42  % (9736)------------------------------
% 0.19/0.42  % (9736)------------------------------
% 0.20/0.42  % (9735)Success in time 0.074 s
%------------------------------------------------------------------------------
