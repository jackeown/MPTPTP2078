%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 105 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 201 expanded)
%              Number of equality atoms :   37 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f57,f63,f72,f78])).

fof(f78,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f54,f54,f71,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_enumset1(X0,X0,X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f14,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f15,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f71,plain,
    ( r2_hidden(sK0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f46,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f46,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl5_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f54,plain,
    ( sK0 != sK2
    | spl5_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_3
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f72,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f49,f46,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f63,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f50,f39,f58,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK3))
    | spl5_1
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f45,f55])).

fof(f55,plain,
    ( sK0 = sK2
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f45,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f39,plain,(
    ! [X0,X3] : r2_hidden(X3,k4_enumset1(X0,X0,X0,X0,X0,X3)) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f50,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f57,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f31,f53,f48,f44])).

fof(f31,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f10,f28])).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f26])).

fof(f13,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(f10,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <~> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      <=> ( r2_hidden(X1,X3)
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f56,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f30,f53,f44])).

fof(f30,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f11,f28])).

fof(f11,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f29,f48,f44])).

fof(f29,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f12,f28])).

fof(f12,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (1221)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (1222)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (1196)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (1214)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (1202)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (1212)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (1201)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (1220)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (1203)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (1200)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (1200)Refutation not found, incomplete strategy% (1200)------------------------------
% 0.22/0.53  % (1200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (1200)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (1200)Memory used [KB]: 1663
% 0.22/0.53  % (1200)Time elapsed: 0.112 s
% 0.22/0.53  % (1200)------------------------------
% 0.22/0.53  % (1200)------------------------------
% 0.22/0.53  % (1212)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (1226)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (1218)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (1213)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f51,f56,f57,f63,f72,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ~spl5_1 | spl5_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    $false | (~spl5_1 | spl5_3)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f54,f54,f71,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_enumset1(X0,X0,X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.22/0.54    inference(equality_resolution,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 0.22/0.54    inference(definition_unfolding,[],[f19,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f14,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f15,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    r2_hidden(sK0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_1),
% 0.22/0.54    inference(resolution,[],[f46,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3)) | ~spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    spl5_1 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    sK0 != sK2 | spl5_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    spl5_3 <=> sK0 = sK2),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ~spl5_1 | spl5_2),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    $false | (~spl5_1 | spl5_2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f49,f46,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ~r2_hidden(sK1,sK3) | spl5_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    spl5_2 <=> r2_hidden(sK1,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    spl5_1 | ~spl5_2 | ~spl5_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    $false | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f50,f39,f58,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK3)) | (spl5_1 | ~spl5_3)),
% 0.22/0.54    inference(forward_demodulation,[],[f45,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    sK0 = sK2 | ~spl5_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f53])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3)) | spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f44])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X3] : (r2_hidden(X3,k4_enumset1(X0,X0,X0,X0,X0,X3))) )),
% 0.22/0.54    inference(equality_resolution,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k4_enumset1(X0,X0,X0,X0,X0,X3) != X2) )),
% 0.22/0.54    inference(equality_resolution,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 0.22/0.54    inference(definition_unfolding,[],[f21,f27])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    r2_hidden(sK1,sK3) | ~spl5_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f48])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f31,f53,f48,f44])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    sK0 != sK2 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3))),
% 0.22/0.54    inference(definition_unfolding,[],[f10,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f13,f26])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    sK0 != sK2 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <~> (r2_hidden(X1,X3) & X0 = X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.22/0.54    inference(negated_conjecture,[],[f7])).
% 0.22/0.54  fof(f7,conjecture,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    spl5_1 | spl5_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f30,f53,f44])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3))),
% 0.22/0.54    inference(definition_unfolding,[],[f11,f28])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    spl5_1 | spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f29,f48,f44])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    r2_hidden(sK1,sK3) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3))),
% 0.22/0.54    inference(definition_unfolding,[],[f12,f28])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    r2_hidden(sK1,sK3) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (1212)------------------------------
% 0.22/0.54  % (1212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1212)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (1212)Memory used [KB]: 6268
% 0.22/0.54  % (1212)Time elapsed: 0.134 s
% 0.22/0.54  % (1212)------------------------------
% 0.22/0.54  % (1212)------------------------------
% 0.22/0.54  % (1205)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (1195)Success in time 0.177 s
%------------------------------------------------------------------------------
