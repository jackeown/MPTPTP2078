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
% DateTime   : Thu Dec  3 12:55:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  90 expanded)
%              Number of leaves         :   10 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 215 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f292,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f79,f80,f89,f115,f281,f282,f291])).

fof(f291,plain,
    ( ~ spl4_25
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f285,f278,f278])).

fof(f278,plain,
    ( spl4_25
  <=> r2_hidden(sK2(sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f285,plain,
    ( ~ r2_hidden(sK2(sK0),sK2(sK0))
    | ~ spl4_25 ),
    inference(resolution,[],[f280,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f280,plain,
    ( r2_hidden(sK2(sK0),sK2(sK0))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f278])).

fof(f282,plain,
    ( spl4_8
    | spl4_25
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f275,f49,f278,f82])).

fof(f82,plain,
    ( spl4_8
  <=> r2_hidden(sK1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f49,plain,
    ( spl4_3
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f275,plain,
    ( r2_hidden(sK2(sK0),sK2(sK0))
    | r2_hidden(sK1(sK0),sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f109,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK2(X0))
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_tarski(X0,X1)
          & v3_ordinal1(X1) )
      | ? [X2] :
          ( ~ v3_ordinal1(X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

% (18026)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f11,plain,(
    ! [X0] :
      ~ ( ! [X1] :
            ( v3_ordinal1(X1)
           => ~ r1_tarski(X0,X1) )
        & ! [X2] :
            ( r2_hidden(X2,X0)
           => v3_ordinal1(X2) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ( v3_ordinal1(X1)
           => ~ r1_tarski(X0,X1) )
        & ! [X1] :
            ( r2_hidden(X1,X0)
           => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_ordinal1)).

fof(f109,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK0,X2)
        | r2_hidden(sK2(sK0),X2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f30,f51])).

fof(f51,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f281,plain,
    ( spl4_25
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f274,f76,f49,f278])).

fof(f76,plain,
    ( spl4_7
  <=> r1_tarski(sK0,sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f274,plain,
    ( r2_hidden(sK2(sK0),sK2(sK0))
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f109,f78])).

fof(f78,plain,
    ( r1_tarski(sK0,sK2(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f115,plain,
    ( spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f111,f82,f38])).

fof(f38,plain,
    ( spl4_1
  <=> v3_ordinal1(sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f111,plain,
    ( v3_ordinal1(sK1(sK0))
    | ~ spl4_8 ),
    inference(resolution,[],[f84,f20])).

fof(f20,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
    <=> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( r2_hidden(X1,X0)
          <=> v3_ordinal1(X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).

fof(f84,plain,
    ( r2_hidden(sK1(sK0),sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f89,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f88,f42,f49])).

fof(f42,plain,
    ( spl4_2
  <=> v3_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f88,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f44,f19])).

fof(f19,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,
    ( v3_ordinal1(sK2(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f80,plain,
    ( spl4_2
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f73,f38,f42])).

fof(f73,plain,
    ( v3_ordinal1(sK2(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f40,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(X0))
      | v3_ordinal1(sK2(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,
    ( v3_ordinal1(sK1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f79,plain,
    ( spl4_7
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f72,f38,f76])).

fof(f72,plain,
    ( r1_tarski(sK0,sK2(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f40,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(X0))
      | r1_tarski(X0,sK2(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f35,f42,f38])).

fof(f35,plain,
    ( v3_ordinal1(sK2(sK0))
    | v3_ordinal1(sK1(sK0)) ),
    inference(resolution,[],[f25,f20])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v3_ordinal1(sK2(X0)) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:44:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (18025)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (18018)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (18021)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (18025)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (18017)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (18017)Refutation not found, incomplete strategy% (18017)------------------------------
% 0.21/0.54  % (18017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18017)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18017)Memory used [KB]: 10618
% 0.21/0.54  % (18017)Time elapsed: 0.122 s
% 0.21/0.54  % (18017)------------------------------
% 0.21/0.54  % (18017)------------------------------
% 0.21/0.54  % (18016)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (18013)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (18035)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (18010)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (18014)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (18012)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (18027)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (18011)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f292,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f45,f79,f80,f89,f115,f281,f282,f291])).
% 0.21/0.54  fof(f291,plain,(
% 0.21/0.54    ~spl4_25 | ~spl4_25),
% 0.21/0.54    inference(avatar_split_clause,[],[f285,f278,f278])).
% 0.21/0.54  fof(f278,plain,(
% 0.21/0.54    spl4_25 <=> r2_hidden(sK2(sK0),sK2(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.54  fof(f285,plain,(
% 0.21/0.54    ~r2_hidden(sK2(sK0),sK2(sK0)) | ~spl4_25),
% 0.21/0.54    inference(resolution,[],[f280,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.54  fof(f280,plain,(
% 0.21/0.54    r2_hidden(sK2(sK0),sK2(sK0)) | ~spl4_25),
% 0.21/0.54    inference(avatar_component_clause,[],[f278])).
% 0.21/0.54  fof(f282,plain,(
% 0.21/0.54    spl4_8 | spl4_25 | ~spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f275,f49,f278,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    spl4_8 <=> r2_hidden(sK1(sK0),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    spl4_3 <=> r2_hidden(sK2(sK0),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    r2_hidden(sK2(sK0),sK2(sK0)) | r2_hidden(sK1(sK0),sK0) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f109,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,sK2(X0)) | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (r1_tarski(X0,X1) & v3_ordinal1(X1)) | ? [X2] : (~v3_ordinal1(X2) & r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  % (18026)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0] : ~(! [X1] : (v3_ordinal1(X1) => ~r1_tarski(X0,X1)) & ! [X2] : (r2_hidden(X2,X0) => v3_ordinal1(X2)))),
% 0.21/0.54    inference(rectify,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ~(! [X1] : (v3_ordinal1(X1) => ~r1_tarski(X0,X1)) & ! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_ordinal1)).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X2] : (~r1_tarski(sK0,X2) | r2_hidden(sK2(sK0),X2)) ) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f30,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    r2_hidden(sK2(sK0),sK0) | ~spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f49])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f281,plain,(
% 0.21/0.54    spl4_25 | ~spl4_3 | ~spl4_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f274,f76,f49,f278])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    spl4_7 <=> r1_tarski(sK0,sK2(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.54  fof(f274,plain,(
% 0.21/0.54    r2_hidden(sK2(sK0),sK2(sK0)) | (~spl4_3 | ~spl4_7)),
% 0.21/0.54    inference(resolution,[],[f109,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    r1_tarski(sK0,sK2(sK0)) | ~spl4_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f76])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    spl4_1 | ~spl4_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f111,f82,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    spl4_1 <=> v3_ordinal1(sK1(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    v3_ordinal1(sK1(sK0)) | ~spl4_8),
% 0.21/0.54    inference(resolution,[],[f84,f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,sK0) | v3_ordinal1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0] : ! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ~! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f9])).
% 0.21/0.54  fof(f9,conjecture,(
% 0.21/0.54    ! [X0] : ~! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    r2_hidden(sK1(sK0),sK0) | ~spl4_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f82])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    spl4_3 | ~spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f88,f42,f49])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    spl4_2 <=> v3_ordinal1(sK2(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    r2_hidden(sK2(sK0),sK0) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f44,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ( ! [X1] : (~v3_ordinal1(X1) | r2_hidden(X1,sK0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    v3_ordinal1(sK2(sK0)) | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f42])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    spl4_2 | ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f73,f38,f42])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    v3_ordinal1(sK2(sK0)) | ~spl4_1),
% 0.21/0.54    inference(resolution,[],[f40,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0] : (~v3_ordinal1(sK1(X0)) | v3_ordinal1(sK2(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    v3_ordinal1(sK1(sK0)) | ~spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f38])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    spl4_7 | ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f72,f38,f76])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    r1_tarski(sK0,sK2(sK0)) | ~spl4_1),
% 0.21/0.54    inference(resolution,[],[f40,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0] : (~v3_ordinal1(sK1(X0)) | r1_tarski(X0,sK2(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    spl4_1 | spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f35,f42,f38])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    v3_ordinal1(sK2(sK0)) | v3_ordinal1(sK1(sK0))),
% 0.21/0.54    inference(resolution,[],[f25,f20])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v3_ordinal1(sK2(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (18025)------------------------------
% 0.21/0.54  % (18025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18025)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (18025)Memory used [KB]: 10874
% 0.21/0.54  % (18025)Time elapsed: 0.118 s
% 0.21/0.54  % (18025)------------------------------
% 0.21/0.54  % (18025)------------------------------
% 0.21/0.54  % (18011)Refutation not found, incomplete strategy% (18011)------------------------------
% 0.21/0.54  % (18011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18011)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18011)Memory used [KB]: 10618
% 0.21/0.54  % (18011)Time elapsed: 0.132 s
% 0.21/0.54  % (18011)------------------------------
% 0.21/0.54  % (18011)------------------------------
% 0.21/0.54  % (18037)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (18006)Success in time 0.182 s
%------------------------------------------------------------------------------
