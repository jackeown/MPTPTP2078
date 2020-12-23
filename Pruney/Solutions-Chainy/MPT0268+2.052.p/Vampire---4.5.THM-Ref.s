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
% DateTime   : Thu Dec  3 12:40:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   59 (  99 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 166 expanded)
%              Number of equality atoms :   45 (  82 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f104,f151,f193])).

fof(f193,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f84,f72,f176])).

fof(f176,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) )
    | ~ spl4_1 ),
    inference(superposition,[],[f75,f79])).

fof(f79,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_1
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f72,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f26,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f84,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f151,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f44,f126])).

fof(f126,plain,
    ( sK0 != k5_xboole_0(sK0,k1_xboole_0)
    | spl4_1
    | spl4_2 ),
    inference(backward_demodulation,[],[f80,f122])).

fof(f122,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f118,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f118,plain,
    ( r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f105,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f105,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f83,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f47])).

% (2184)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f46])).

% (2175)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f83,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f80,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f104,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f50,f82,f78])).

fof(f50,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f19,f36,f48])).

fof(f19,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f85,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f49,f82,f78])).

fof(f49,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f20,f36,f48])).

fof(f20,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (2161)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (2170)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (2159)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (2177)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (2171)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (2168)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (2161)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (2179)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (2163)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (2169)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (2172)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.53  % (2160)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.53  % (2177)Refutation not found, incomplete strategy% (2177)------------------------------
% 1.36/0.53  % (2177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (2177)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (2177)Memory used [KB]: 10746
% 1.36/0.53  % (2177)Time elapsed: 0.119 s
% 1.36/0.53  % (2177)------------------------------
% 1.36/0.53  % (2177)------------------------------
% 1.36/0.53  % (2185)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.53  % (2164)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f194,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(avatar_sat_refutation,[],[f85,f104,f151,f193])).
% 1.36/0.54  fof(f193,plain,(
% 1.36/0.54    ~spl4_1 | ~spl4_2),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f188])).
% 1.36/0.54  fof(f188,plain,(
% 1.36/0.54    $false | (~spl4_1 | ~spl4_2)),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f84,f72,f176])).
% 1.36/0.54  fof(f176,plain,(
% 1.36/0.54    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ) | ~spl4_1),
% 1.36/0.54    inference(superposition,[],[f75,f79])).
% 1.36/0.54  fof(f79,plain,(
% 1.36/0.54    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~spl4_1),
% 1.36/0.54    inference(avatar_component_clause,[],[f78])).
% 1.36/0.54  fof(f78,plain,(
% 1.36/0.54    spl4_1 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.36/0.54  fof(f75,plain,(
% 1.36/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.36/0.54    inference(equality_resolution,[],[f60])).
% 1.36/0.54  fof(f60,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.36/0.54    inference(definition_unfolding,[],[f33,f36])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.36/0.54  fof(f33,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.36/0.54    inference(cnf_transformation,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.36/0.54  fof(f72,plain,(
% 1.36/0.54    ( ! [X4,X2,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2))) )),
% 1.36/0.54    inference(equality_resolution,[],[f71])).
% 1.36/0.54  fof(f71,plain,(
% 1.36/0.54    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X4,X4,X4,X1,X2) != X3) )),
% 1.36/0.54    inference(equality_resolution,[],[f53])).
% 1.36/0.54  fof(f53,plain,(
% 1.36/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.36/0.54    inference(definition_unfolding,[],[f26,f46])).
% 1.36/0.54  fof(f46,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f39,f45])).
% 1.36/0.54  fof(f45,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f11])).
% 1.36/0.54  fof(f11,axiom,(
% 1.36/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.36/0.54  fof(f39,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f10])).
% 1.36/0.54  fof(f10,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.54  fof(f26,plain,(
% 1.36/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.36/0.54    inference(cnf_transformation,[],[f16])).
% 1.36/0.54  fof(f16,plain,(
% 1.36/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.36/0.54    inference(ennf_transformation,[],[f7])).
% 1.36/0.54  fof(f7,axiom,(
% 1.36/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.36/0.54  fof(f84,plain,(
% 1.36/0.54    r2_hidden(sK1,sK0) | ~spl4_2),
% 1.36/0.54    inference(avatar_component_clause,[],[f82])).
% 1.36/0.54  fof(f82,plain,(
% 1.36/0.54    spl4_2 <=> r2_hidden(sK1,sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.36/0.54  fof(f151,plain,(
% 1.36/0.54    spl4_1 | spl4_2),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f129])).
% 1.36/0.54  fof(f129,plain,(
% 1.36/0.54    $false | (spl4_1 | spl4_2)),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f44,f126])).
% 1.36/0.54  fof(f126,plain,(
% 1.36/0.54    sK0 != k5_xboole_0(sK0,k1_xboole_0) | (spl4_1 | spl4_2)),
% 1.36/0.54    inference(backward_demodulation,[],[f80,f122])).
% 1.36/0.54  fof(f122,plain,(
% 1.36/0.54    k1_xboole_0 = k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl4_2),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f118,f42])).
% 1.36/0.54  fof(f42,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f2])).
% 1.36/0.54  fof(f2,axiom,(
% 1.36/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.36/0.54  fof(f118,plain,(
% 1.36/0.54    r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl4_2),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f105,f43])).
% 1.36/0.54  fof(f43,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f18])).
% 1.36/0.54  fof(f18,plain,(
% 1.36/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.36/0.54  fof(f105,plain,(
% 1.36/0.54    r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | spl4_2),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f83,f65])).
% 1.36/0.54  fof(f65,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f35,f48])).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f38,f47])).
% 1.36/0.54  % (2184)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  fof(f47,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f40,f46])).
% 1.36/0.54  % (2175)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.54  fof(f40,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f9])).
% 1.36/0.54  fof(f9,axiom,(
% 1.36/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.54  fof(f38,plain,(
% 1.36/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f8])).
% 1.36/0.54  fof(f8,axiom,(
% 1.36/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f17])).
% 1.36/0.54  fof(f17,plain,(
% 1.36/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f12])).
% 1.36/0.54  fof(f12,axiom,(
% 1.36/0.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.36/0.54  fof(f83,plain,(
% 1.36/0.54    ~r2_hidden(sK1,sK0) | spl4_2),
% 1.36/0.54    inference(avatar_component_clause,[],[f82])).
% 1.36/0.54  fof(f80,plain,(
% 1.36/0.54    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | spl4_1),
% 1.36/0.54    inference(avatar_component_clause,[],[f78])).
% 1.36/0.54  fof(f44,plain,(
% 1.36/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.36/0.54  fof(f104,plain,(
% 1.36/0.54    spl4_1 | ~spl4_2),
% 1.36/0.54    inference(avatar_split_clause,[],[f50,f82,f78])).
% 1.36/0.54  fof(f50,plain,(
% 1.36/0.54    ~r2_hidden(sK1,sK0) | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.36/0.54    inference(definition_unfolding,[],[f19,f36,f48])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.36/0.54    inference(cnf_transformation,[],[f15])).
% 1.36/0.54  fof(f15,plain,(
% 1.36/0.54    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,negated_conjecture,(
% 1.36/0.54    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.36/0.54    inference(negated_conjecture,[],[f13])).
% 1.36/0.54  fof(f13,conjecture,(
% 1.36/0.54    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.36/0.54  fof(f85,plain,(
% 1.36/0.54    ~spl4_1 | spl4_2),
% 1.36/0.54    inference(avatar_split_clause,[],[f49,f82,f78])).
% 1.36/0.54  fof(f49,plain,(
% 1.36/0.54    r2_hidden(sK1,sK0) | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.36/0.54    inference(definition_unfolding,[],[f20,f36,f48])).
% 1.36/0.54  fof(f20,plain,(
% 1.36/0.54    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.36/0.54    inference(cnf_transformation,[],[f15])).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (2161)------------------------------
% 1.36/0.54  % (2161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (2161)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (2161)Memory used [KB]: 6268
% 1.36/0.54  % (2161)Time elapsed: 0.108 s
% 1.36/0.54  % (2161)------------------------------
% 1.36/0.54  % (2161)------------------------------
% 1.36/0.54  % (2162)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.54  % (2174)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.54  % (2156)Success in time 0.18 s
%------------------------------------------------------------------------------
