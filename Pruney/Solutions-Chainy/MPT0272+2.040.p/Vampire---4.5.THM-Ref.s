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
% DateTime   : Thu Dec  3 12:41:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  26 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  49 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f16,f21,f37])).

fof(f37,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f36])).

fof(f36,plain,
    ( $false
    | spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f29,f15])).

fof(f15,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f13])).

fof(f13,plain,
    ( spl2_1
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f29,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
    | spl2_2 ),
    inference(trivial_inequality_removal,[],[f24])).

fof(f24,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
    | spl2_2 ),
    inference(superposition,[],[f20,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f10,f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f20,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl2_2
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f21,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f6,f18])).

fof(f6,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f16,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f7,f13])).

fof(f7,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (3195)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.41  % (3193)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (3192)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (3187)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (3187)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f16,f21,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    spl2_1 | spl2_2),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    $false | (spl2_1 | spl2_2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f29,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    spl2_1 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) | spl2_2),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) | spl2_2),
% 0.21/0.43    inference(superposition,[],[f20,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.43    inference(resolution,[],[f10,f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    spl2_2 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ~spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f6,f18])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,plain,(
% 0.21/0.43    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0)),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)),
% 0.21/0.43    inference(negated_conjecture,[],[f3])).
% 0.21/0.43  fof(f3,conjecture,(
% 0.21/0.43    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ~spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f7,f13])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (3187)------------------------------
% 0.21/0.43  % (3187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (3187)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (3187)Memory used [KB]: 10490
% 0.21/0.43  % (3187)Time elapsed: 0.005 s
% 0.21/0.43  % (3187)------------------------------
% 0.21/0.43  % (3187)------------------------------
% 0.21/0.43  % (3185)Success in time 0.079 s
%------------------------------------------------------------------------------
