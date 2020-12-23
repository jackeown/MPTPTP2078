%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  42 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  76 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f25,f33,f40,f44])).

fof(f44,plain,
    ( ~ spl2_2
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f43])).

fof(f43,plain,
    ( $false
    | ~ spl2_2
    | spl2_4 ),
    inference(subsumption_resolution,[],[f41,f39])).

fof(f39,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f37])).

% (18902)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
fof(f37,plain,
    ( spl2_4
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f41,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f34,f24])).

fof(f24,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(resolution,[],[f13,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f40,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f35,f29,f37])).

fof(f29,plain,
    ( spl2_3
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f35,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    | spl2_3 ),
    inference(superposition,[],[f31,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f31,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f33,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f27,f17,f29])).

fof(f17,plain,
    ( spl2_1
  <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f27,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl2_1 ),
    inference(superposition,[],[f19,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f19,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f25,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f9,f22])).

fof(f9,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f20,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f10,f17])).

fof(f10,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:21:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (18900)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (18894)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (18894)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f20,f25,f33,f40,f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ~spl2_2 | spl2_4),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    $false | (~spl2_2 | spl2_4)),
% 0.21/0.43    inference(subsumption_resolution,[],[f41,f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) | spl2_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f37])).
% 0.21/0.43  % (18902)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    spl2_4 <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | ~spl2_2),
% 0.21/0.43    inference(resolution,[],[f34,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    r2_hidden(sK0,sK1) | ~spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    spl2_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 0.21/0.43    inference(resolution,[],[f13,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ~spl2_4 | spl2_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f35,f29,f37])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    spl2_3 <=> sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) | spl2_3),
% 0.21/0.43    inference(superposition,[],[f31,f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | spl2_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f29])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ~spl2_3 | spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f17,f29])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    spl2_1 <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | spl2_1),
% 0.21/0.43    inference(superposition,[],[f19,f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f17])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f9,f22])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    r2_hidden(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.43    inference(negated_conjecture,[],[f5])).
% 0.21/0.43  fof(f5,conjecture,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ~spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f10,f17])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (18894)------------------------------
% 0.21/0.43  % (18894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (18894)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (18894)Memory used [KB]: 10618
% 0.21/0.43  % (18894)Time elapsed: 0.005 s
% 0.21/0.43  % (18894)------------------------------
% 0.21/0.43  % (18894)------------------------------
% 0.21/0.43  % (18892)Success in time 0.073 s
%------------------------------------------------------------------------------
