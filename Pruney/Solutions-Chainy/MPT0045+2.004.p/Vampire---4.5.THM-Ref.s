%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  45 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 (  96 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f93,f132])).

fof(f132,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f11,f51])).

fof(f51,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f11,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != X0
      & r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k4_xboole_0(X1,X0))
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f93,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f55,f59,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f59,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0),k4_xboole_0(sK1,sK0))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f10,f55,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f10,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0),sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_2
  <=> r2_hidden(sK3(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f56,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f44,f53,f49])).

fof(f44,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0),sK0)
    | k1_xboole_0 = sK0 ),
    inference(factoring,[],[f38])).

fof(f38,plain,(
    ! [X2] :
      ( r2_hidden(sK3(X2,k1_xboole_0),sK0)
      | r2_hidden(sK3(X2,k1_xboole_0),X2)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f33,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f33,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f27,f28])).

fof(f28,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f10,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.51  % (1260)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (1264)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (1263)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (1258)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.51  % (1259)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (1278)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.51  % (1280)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (1274)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.52  % (1262)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.52  % (1279)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.52  % (1281)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (1277)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.52  % (1262)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f133,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f56,f93,f132])).
% 0.19/0.52  fof(f132,plain,(
% 0.19/0.52    ~spl5_1),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f128])).
% 0.19/0.52  fof(f128,plain,(
% 0.19/0.52    $false | ~spl5_1),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f11,f51])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    k1_xboole_0 = sK0 | ~spl5_1),
% 0.19/0.52    inference(avatar_component_clause,[],[f49])).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    spl5_1 <=> k1_xboole_0 = sK0),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.52  fof(f11,plain,(
% 0.19/0.52    k1_xboole_0 != sK0),
% 0.19/0.52    inference(cnf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,plain,(
% 0.19/0.52    ? [X0,X1] : (k1_xboole_0 != X0 & r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.19/0.52    inference(negated_conjecture,[],[f5])).
% 0.19/0.52  fof(f5,conjecture,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.19/0.52  fof(f93,plain,(
% 0.19/0.52    ~spl5_2),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f87])).
% 0.19/0.52  fof(f87,plain,(
% 0.19/0.52    $false | ~spl5_2),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f55,f59,f26])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.19/0.52    inference(equality_resolution,[],[f16])).
% 0.19/0.52  fof(f16,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.19/0.52    inference(cnf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.19/0.52  fof(f59,plain,(
% 0.19/0.52    r2_hidden(sK3(sK0,k1_xboole_0),k4_xboole_0(sK1,sK0)) | ~spl5_2),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f10,f55,f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f9])).
% 0.19/0.52  fof(f9,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.52  fof(f10,plain,(
% 0.19/0.52    r1_tarski(sK0,k4_xboole_0(sK1,sK0))),
% 0.19/0.52    inference(cnf_transformation,[],[f7])).
% 0.19/0.52  fof(f55,plain,(
% 0.19/0.52    r2_hidden(sK3(sK0,k1_xboole_0),sK0) | ~spl5_2),
% 0.19/0.52    inference(avatar_component_clause,[],[f53])).
% 0.19/0.52  fof(f53,plain,(
% 0.19/0.52    spl5_2 <=> r2_hidden(sK3(sK0,k1_xboole_0),sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.52  fof(f56,plain,(
% 0.19/0.52    spl5_1 | spl5_2),
% 0.19/0.52    inference(avatar_split_clause,[],[f44,f53,f49])).
% 0.19/0.52  fof(f44,plain,(
% 0.19/0.52    r2_hidden(sK3(sK0,k1_xboole_0),sK0) | k1_xboole_0 = sK0),
% 0.19/0.52    inference(factoring,[],[f38])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ( ! [X2] : (r2_hidden(sK3(X2,k1_xboole_0),sK0) | r2_hidden(sK3(X2,k1_xboole_0),X2) | k1_xboole_0 = X2) )),
% 0.19/0.52    inference(resolution,[],[f33,f20])).
% 0.19/0.52  fof(f20,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,plain,(
% 0.19/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.19/0.52    inference(ennf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,sK0)) )),
% 0.19/0.52    inference(superposition,[],[f27,f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f10,f18])).
% 0.19/0.52  fof(f18,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 0.19/0.52    inference(equality_resolution,[],[f15])).
% 0.19/0.52  fof(f15,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.19/0.52    inference(cnf_transformation,[],[f2])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (1270)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (1262)------------------------------
% 0.19/0.52  % (1262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (1262)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (1262)Memory used [KB]: 6268
% 0.19/0.52  % (1262)Time elapsed: 0.109 s
% 0.19/0.52  % (1262)------------------------------
% 0.19/0.52  % (1262)------------------------------
% 0.19/0.52  % (1273)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (1261)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  % (1267)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.52  % (1272)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (1282)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.52  % (1271)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.52  % (1268)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.52  % (1286)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.53  % (1265)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.53  % (1284)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.53  % (1283)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.53  % (1285)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.53  % (1280)Refutation not found, incomplete strategy% (1280)------------------------------
% 0.19/0.53  % (1280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (1280)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (1280)Memory used [KB]: 10618
% 0.19/0.53  % (1280)Time elapsed: 0.111 s
% 0.19/0.53  % (1280)------------------------------
% 0.19/0.53  % (1280)------------------------------
% 0.19/0.53  % (1257)Success in time 0.173 s
%------------------------------------------------------------------------------
