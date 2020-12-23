%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:54 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 207 expanded)
%              Number of leaves         :    9 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  117 ( 444 expanded)
%              Number of equality atoms :   30 ( 137 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4386,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f225,f4112,f4385])).

fof(f4385,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f4377])).

fof(f4377,plain,
    ( $false
    | spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f38,f4376])).

fof(f4376,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_1
    | spl4_2 ),
    inference(backward_demodulation,[],[f220,f4365])).

fof(f4365,plain,
    ( sK0 = sK2(k1_tarski(sK0),sK0)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f4255,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

% (8165)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f4255,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f223,f99,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f99,plain,(
    ~ r1_tarski(sK0,k1_setfam_1(k1_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f17,f92,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f92,plain,(
    r1_tarski(k1_setfam_1(k1_tarski(sK0)),sK0) ),
    inference(backward_demodulation,[],[f90,f84])).

fof(f84,plain,(
    sK0 = sK3(k1_tarski(sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f63,f34])).

fof(f63,plain,(
    r2_hidden(sK3(k1_tarski(sK0),k1_xboole_0),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f61,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f61,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f36,f57,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f40,f42,f28])).

fof(f42,plain,(
    ~ r2_hidden(sK0,k1_tarski(k1_setfam_1(k1_tarski(sK0)))) ),
    inference(unit_resulting_resolution,[],[f17,f34])).

fof(f40,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f36,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f90,plain,(
    r1_tarski(k1_setfam_1(k1_tarski(sK0)),sK3(k1_tarski(sK0),k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f37,f63,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f17,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f223,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl4_2
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

% (8165)Refutation not found, incomplete strategy% (8165)------------------------------
% (8165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8165)Termination reason: Refutation not found, incomplete strategy

% (8165)Memory used [KB]: 10618
% (8165)Time elapsed: 0.164 s
% (8165)------------------------------
% (8165)------------------------------
fof(f220,plain,
    ( ~ r1_tarski(sK0,sK2(k1_tarski(sK0),sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK2(k1_tarski(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f4112,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f4104])).

fof(f4104,plain,
    ( $false
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f38,f3966])).

fof(f3966,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f61,f224])).

fof(f224,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f222])).

fof(f225,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f110,f222,f218])).

fof(f110,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ r1_tarski(sK0,sK2(k1_tarski(sK0),sK0)) ),
    inference(resolution,[],[f99,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:12:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (8158)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (8172)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (8179)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (8179)Refutation not found, incomplete strategy% (8179)------------------------------
% 0.22/0.53  % (8179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8179)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8179)Memory used [KB]: 1663
% 0.22/0.53  % (8179)Time elapsed: 0.108 s
% 0.22/0.53  % (8179)------------------------------
% 0.22/0.53  % (8179)------------------------------
% 0.22/0.55  % (8181)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (8162)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (8162)Refutation not found, incomplete strategy% (8162)------------------------------
% 0.22/0.55  % (8162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8162)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8162)Memory used [KB]: 10618
% 0.22/0.55  % (8162)Time elapsed: 0.125 s
% 0.22/0.55  % (8162)------------------------------
% 0.22/0.55  % (8162)------------------------------
% 0.22/0.57  % (8157)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.58  % (8175)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.58  % (8176)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.58  % (8166)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.58  % (8161)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.59  % (8167)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.59  % (8184)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.59  % (8153)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.59  % (8153)Refutation not found, incomplete strategy% (8153)------------------------------
% 0.22/0.59  % (8153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (8153)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (8153)Memory used [KB]: 1663
% 0.22/0.59  % (8153)Time elapsed: 0.170 s
% 0.22/0.59  % (8153)------------------------------
% 0.22/0.59  % (8153)------------------------------
% 0.22/0.59  % (8160)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.59  % (8178)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.59  % (8178)Refutation not found, incomplete strategy% (8178)------------------------------
% 0.22/0.59  % (8178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (8178)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (8178)Memory used [KB]: 10618
% 0.22/0.59  % (8178)Time elapsed: 0.147 s
% 0.22/0.59  % (8178)------------------------------
% 0.22/0.59  % (8178)------------------------------
% 0.22/0.60  % (8170)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.60  % (8177)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.60  % (8177)Refutation not found, incomplete strategy% (8177)------------------------------
% 0.22/0.60  % (8177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (8177)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (8177)Memory used [KB]: 1663
% 0.22/0.60  % (8177)Time elapsed: 0.172 s
% 0.22/0.60  % (8177)------------------------------
% 0.22/0.60  % (8177)------------------------------
% 0.22/0.60  % (8185)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.60  % (8183)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.91/0.61  % (8159)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.91/0.61  % (8166)Refutation not found, incomplete strategy% (8166)------------------------------
% 1.91/0.61  % (8166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.61  % (8166)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.61  
% 1.91/0.61  % (8166)Memory used [KB]: 10746
% 1.91/0.61  % (8166)Time elapsed: 0.198 s
% 1.91/0.61  % (8166)------------------------------
% 1.91/0.61  % (8166)------------------------------
% 1.91/0.61  % (8169)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.91/0.61  % (8168)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.91/0.61  % (8180)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.91/0.61  % (8176)Refutation not found, incomplete strategy% (8176)------------------------------
% 1.91/0.61  % (8176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.61  % (8176)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.61  
% 1.91/0.61  % (8176)Memory used [KB]: 10618
% 1.91/0.61  % (8176)Time elapsed: 0.197 s
% 1.91/0.61  % (8176)------------------------------
% 1.91/0.61  % (8176)------------------------------
% 1.91/0.62  % (8182)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.91/0.62  % (8173)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.91/0.62  % (8154)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.03/0.62  % (8158)Refutation found. Thanks to Tanya!
% 2.03/0.62  % SZS status Theorem for theBenchmark
% 2.03/0.62  % SZS output start Proof for theBenchmark
% 2.03/0.62  fof(f4386,plain,(
% 2.03/0.62    $false),
% 2.03/0.62    inference(avatar_sat_refutation,[],[f225,f4112,f4385])).
% 2.03/0.62  fof(f4385,plain,(
% 2.03/0.62    spl4_1 | spl4_2),
% 2.03/0.62    inference(avatar_contradiction_clause,[],[f4377])).
% 2.03/0.62  fof(f4377,plain,(
% 2.03/0.62    $false | (spl4_1 | spl4_2)),
% 2.03/0.62    inference(unit_resulting_resolution,[],[f38,f4376])).
% 2.03/0.62  fof(f4376,plain,(
% 2.03/0.62    ~r1_tarski(sK0,sK0) | (spl4_1 | spl4_2)),
% 2.03/0.62    inference(backward_demodulation,[],[f220,f4365])).
% 2.03/0.62  fof(f4365,plain,(
% 2.03/0.62    sK0 = sK2(k1_tarski(sK0),sK0) | spl4_2),
% 2.03/0.62    inference(unit_resulting_resolution,[],[f4255,f34])).
% 2.03/0.62  fof(f34,plain,(
% 2.03/0.62    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 2.03/0.62    inference(equality_resolution,[],[f19])).
% 2.03/0.62  fof(f19,plain,(
% 2.03/0.62    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.03/0.62    inference(cnf_transformation,[],[f3])).
% 2.03/0.63  % (8165)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 2.03/0.63  fof(f3,axiom,(
% 2.03/0.63    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.03/0.63  fof(f4255,plain,(
% 2.03/0.63    r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0)) | spl4_2),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f223,f99,f26])).
% 2.03/0.63  fof(f26,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f15])).
% 2.03/0.63  fof(f15,plain,(
% 2.03/0.63    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.03/0.63    inference(flattening,[],[f14])).
% 2.03/0.63  fof(f14,plain,(
% 2.03/0.63    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.03/0.63    inference(ennf_transformation,[],[f7])).
% 2.03/0.63  fof(f7,axiom,(
% 2.03/0.63    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).
% 2.03/0.63  fof(f99,plain,(
% 2.03/0.63    ~r1_tarski(sK0,k1_setfam_1(k1_tarski(sK0)))),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f17,f92,f24])).
% 2.03/0.63  fof(f24,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f2])).
% 2.03/0.63  fof(f2,axiom,(
% 2.03/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.03/0.63  fof(f92,plain,(
% 2.03/0.63    r1_tarski(k1_setfam_1(k1_tarski(sK0)),sK0)),
% 2.03/0.63    inference(backward_demodulation,[],[f90,f84])).
% 2.03/0.63  fof(f84,plain,(
% 2.03/0.63    sK0 = sK3(k1_tarski(sK0),k1_xboole_0)),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f63,f34])).
% 2.03/0.63  fof(f63,plain,(
% 2.03/0.63    r2_hidden(sK3(k1_tarski(sK0),k1_xboole_0),k1_tarski(sK0))),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f61,f29])).
% 2.03/0.63  fof(f29,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f16])).
% 2.03/0.63  fof(f16,plain,(
% 2.03/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.03/0.63    inference(ennf_transformation,[],[f1])).
% 2.03/0.63  fof(f1,axiom,(
% 2.03/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.03/0.63  fof(f61,plain,(
% 2.03/0.63    ~r1_tarski(k1_tarski(sK0),k1_xboole_0)),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f36,f57,f28])).
% 2.03/0.63  fof(f28,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f16])).
% 2.03/0.63  fof(f57,plain,(
% 2.03/0.63    ~r2_hidden(sK0,k1_xboole_0)),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f40,f42,f28])).
% 2.03/0.63  fof(f42,plain,(
% 2.03/0.63    ~r2_hidden(sK0,k1_tarski(k1_setfam_1(k1_tarski(sK0))))),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f17,f34])).
% 2.03/0.63  fof(f40,plain,(
% 2.03/0.63    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 2.03/0.63    inference(equality_resolution,[],[f32])).
% 2.03/0.63  fof(f32,plain,(
% 2.03/0.63    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f5])).
% 2.03/0.63  fof(f5,axiom,(
% 2.03/0.63    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.03/0.63  fof(f36,plain,(
% 2.03/0.63    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 2.03/0.63    inference(equality_resolution,[],[f35])).
% 2.03/0.63  fof(f35,plain,(
% 2.03/0.63    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 2.03/0.63    inference(equality_resolution,[],[f18])).
% 2.03/0.63  fof(f18,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f3])).
% 2.03/0.63  fof(f90,plain,(
% 2.03/0.63    r1_tarski(k1_setfam_1(k1_tarski(sK0)),sK3(k1_tarski(sK0),k1_xboole_0))),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f37,f63,f25])).
% 2.03/0.63  fof(f25,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f13])).
% 2.03/0.63  fof(f13,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 2.03/0.63    inference(flattening,[],[f12])).
% 2.03/0.63  fof(f12,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 2.03/0.63    inference(ennf_transformation,[],[f8])).
% 2.03/0.63  fof(f8,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).
% 2.03/0.63  fof(f37,plain,(
% 2.03/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.03/0.63    inference(equality_resolution,[],[f23])).
% 2.03/0.63  fof(f23,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f2])).
% 2.03/0.63  fof(f17,plain,(
% 2.03/0.63    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 2.03/0.63    inference(cnf_transformation,[],[f11])).
% 2.03/0.63  fof(f11,plain,(
% 2.03/0.63    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 2.03/0.63    inference(ennf_transformation,[],[f10])).
% 2.03/0.63  fof(f10,negated_conjecture,(
% 2.03/0.63    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.03/0.63    inference(negated_conjecture,[],[f9])).
% 2.03/0.63  fof(f9,conjecture,(
% 2.03/0.63    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 2.03/0.63  fof(f223,plain,(
% 2.03/0.63    k1_xboole_0 != k1_tarski(sK0) | spl4_2),
% 2.03/0.63    inference(avatar_component_clause,[],[f222])).
% 2.03/0.63  fof(f222,plain,(
% 2.03/0.63    spl4_2 <=> k1_xboole_0 = k1_tarski(sK0)),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.03/0.63  % (8165)Refutation not found, incomplete strategy% (8165)------------------------------
% 2.03/0.63  % (8165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.63  % (8165)Termination reason: Refutation not found, incomplete strategy
% 2.03/0.63  
% 2.03/0.63  % (8165)Memory used [KB]: 10618
% 2.03/0.63  % (8165)Time elapsed: 0.164 s
% 2.03/0.63  % (8165)------------------------------
% 2.03/0.63  % (8165)------------------------------
% 2.03/0.63  fof(f220,plain,(
% 2.03/0.63    ~r1_tarski(sK0,sK2(k1_tarski(sK0),sK0)) | spl4_1),
% 2.03/0.63    inference(avatar_component_clause,[],[f218])).
% 2.03/0.63  fof(f218,plain,(
% 2.03/0.63    spl4_1 <=> r1_tarski(sK0,sK2(k1_tarski(sK0),sK0))),
% 2.03/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.03/0.63  fof(f38,plain,(
% 2.03/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.03/0.63    inference(equality_resolution,[],[f22])).
% 2.03/0.63  fof(f22,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f2])).
% 2.03/0.63  fof(f4112,plain,(
% 2.03/0.63    ~spl4_2),
% 2.03/0.63    inference(avatar_contradiction_clause,[],[f4104])).
% 2.03/0.63  fof(f4104,plain,(
% 2.03/0.63    $false | ~spl4_2),
% 2.03/0.63    inference(unit_resulting_resolution,[],[f38,f3966])).
% 2.03/0.63  fof(f3966,plain,(
% 2.03/0.63    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl4_2),
% 2.03/0.63    inference(backward_demodulation,[],[f61,f224])).
% 2.03/0.63  fof(f224,plain,(
% 2.03/0.63    k1_xboole_0 = k1_tarski(sK0) | ~spl4_2),
% 2.03/0.63    inference(avatar_component_clause,[],[f222])).
% 2.03/0.63  fof(f225,plain,(
% 2.03/0.63    ~spl4_1 | spl4_2),
% 2.03/0.63    inference(avatar_split_clause,[],[f110,f222,f218])).
% 2.03/0.63  fof(f110,plain,(
% 2.03/0.63    k1_xboole_0 = k1_tarski(sK0) | ~r1_tarski(sK0,sK2(k1_tarski(sK0),sK0))),
% 2.03/0.63    inference(resolution,[],[f99,f27])).
% 2.03/0.63  fof(f27,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK2(X0,X1))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f15])).
% 2.03/0.63  % SZS output end Proof for theBenchmark
% 2.03/0.63  % (8158)------------------------------
% 2.03/0.63  % (8158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.63  % (8158)Termination reason: Refutation
% 2.03/0.63  
% 2.03/0.63  % (8158)Memory used [KB]: 7164
% 2.03/0.63  % (8158)Time elapsed: 0.191 s
% 2.03/0.63  % (8158)------------------------------
% 2.03/0.63  % (8158)------------------------------
% 2.05/0.63  % (8148)Success in time 0.261 s
%------------------------------------------------------------------------------
