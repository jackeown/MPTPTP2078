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
% DateTime   : Thu Dec  3 12:38:36 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   53 (  78 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   99 ( 147 expanded)
%              Number of equality atoms :   34 (  55 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f65,f69,f84,f113,f127,f132,f137,f152])).

fof(f152,plain,
    ( spl3_3
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl3_3
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f150,f68])).

fof(f68,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_3
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f150,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f147,f135])).

fof(f135,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl3_10
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f147,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) = k2_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl3_9 ),
    inference(superposition,[],[f30,f131])).

fof(f131,plain,
    ( k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_9
  <=> k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f137,plain,
    ( spl3_10
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f128,f125,f111,f134])).

fof(f111,plain,
    ( spl3_7
  <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f125,plain,
    ( spl3_8
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f128,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f126,f119])).

fof(f119,plain,
    ( k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl3_7 ),
    inference(superposition,[],[f43,f112])).

fof(f112,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f126,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f132,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f119,f111,f130])).

fof(f127,plain,
    ( spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f118,f111,f125])).

fof(f118,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl3_7 ),
    inference(superposition,[],[f29,f112])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f113,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f94,f82,f111])).

fof(f82,plain,
    ( spl3_4
  <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f94,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl3_4 ),
    inference(superposition,[],[f83,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f83,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f72,f63,f82])).

fof(f63,plain,
    ( spl3_2
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f72,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f64,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f69,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f65,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f61,f55,f63])).

fof(f55,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f61,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f56,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f56,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f57,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:35:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (32337)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (32336)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (32354)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.29/0.52  % (32344)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.29/0.53  % (32348)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.29/0.53  % (32334)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.29/0.53  % (32358)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.29/0.53  % (32339)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.29/0.53  % (32349)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.29/0.53  % (32349)Refutation not found, incomplete strategy% (32349)------------------------------
% 1.29/0.53  % (32349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (32349)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (32349)Memory used [KB]: 1663
% 1.29/0.53  % (32349)Time elapsed: 0.092 s
% 1.29/0.53  % (32349)------------------------------
% 1.29/0.53  % (32349)------------------------------
% 1.29/0.53  % (32362)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.29/0.53  % (32335)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.29/0.53  % (32335)Refutation not found, incomplete strategy% (32335)------------------------------
% 1.29/0.53  % (32335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (32335)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (32335)Memory used [KB]: 1663
% 1.29/0.53  % (32335)Time elapsed: 0.125 s
% 1.29/0.53  % (32335)------------------------------
% 1.29/0.53  % (32335)------------------------------
% 1.29/0.54  % (32342)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.29/0.54  % (32361)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.29/0.54  % (32365)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.29/0.54  % (32346)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.29/0.54  % (32338)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.29/0.54  % (32362)Refutation found. Thanks to Tanya!
% 1.29/0.54  % SZS status Theorem for theBenchmark
% 1.29/0.55  % (32363)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.29/0.55  % (32357)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.29/0.55  % SZS output start Proof for theBenchmark
% 1.29/0.55  fof(f154,plain,(
% 1.29/0.55    $false),
% 1.29/0.55    inference(avatar_sat_refutation,[],[f57,f65,f69,f84,f113,f127,f132,f137,f152])).
% 1.29/0.55  fof(f152,plain,(
% 1.29/0.55    spl3_3 | ~spl3_9 | ~spl3_10),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f151])).
% 1.29/0.55  fof(f151,plain,(
% 1.29/0.55    $false | (spl3_3 | ~spl3_9 | ~spl3_10)),
% 1.29/0.55    inference(subsumption_resolution,[],[f150,f68])).
% 1.29/0.55  fof(f68,plain,(
% 1.29/0.55    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) | spl3_3),
% 1.29/0.55    inference(avatar_component_clause,[],[f67])).
% 1.29/0.55  fof(f67,plain,(
% 1.29/0.55    spl3_3 <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.29/0.55  fof(f150,plain,(
% 1.29/0.55    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | (~spl3_9 | ~spl3_10)),
% 1.29/0.55    inference(forward_demodulation,[],[f147,f135])).
% 1.29/0.55  fof(f135,plain,(
% 1.29/0.55    sK1 = k2_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))) | ~spl3_10),
% 1.29/0.55    inference(avatar_component_clause,[],[f134])).
% 1.29/0.55  fof(f134,plain,(
% 1.29/0.55    spl3_10 <=> sK1 = k2_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.29/0.55  fof(f147,plain,(
% 1.29/0.55    k2_xboole_0(k1_tarski(sK0),sK1) = k2_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))) | ~spl3_9),
% 1.29/0.55    inference(superposition,[],[f30,f131])).
% 1.29/0.55  fof(f131,plain,(
% 1.29/0.55    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) | ~spl3_9),
% 1.29/0.55    inference(avatar_component_clause,[],[f130])).
% 1.29/0.55  fof(f130,plain,(
% 1.29/0.55    spl3_9 <=> k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.29/0.55  fof(f30,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f8])).
% 1.29/0.55  fof(f8,axiom,(
% 1.29/0.55    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.29/0.55  fof(f137,plain,(
% 1.29/0.55    spl3_10 | ~spl3_7 | ~spl3_8),
% 1.29/0.55    inference(avatar_split_clause,[],[f128,f125,f111,f134])).
% 1.29/0.55  fof(f111,plain,(
% 1.29/0.55    spl3_7 <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.29/0.55  fof(f125,plain,(
% 1.29/0.55    spl3_8 <=> sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.29/0.55  fof(f128,plain,(
% 1.29/0.55    sK1 = k2_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))) | (~spl3_7 | ~spl3_8)),
% 1.29/0.55    inference(forward_demodulation,[],[f126,f119])).
% 1.29/0.55  fof(f119,plain,(
% 1.29/0.55    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) | ~spl3_7),
% 1.29/0.55    inference(superposition,[],[f43,f112])).
% 1.29/0.55  fof(f112,plain,(
% 1.29/0.55    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl3_7),
% 1.29/0.55    inference(avatar_component_clause,[],[f111])).
% 1.29/0.55  fof(f43,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f5])).
% 1.29/0.55  fof(f5,axiom,(
% 1.29/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.29/0.55  fof(f126,plain,(
% 1.29/0.55    sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | ~spl3_8),
% 1.29/0.55    inference(avatar_component_clause,[],[f125])).
% 1.29/0.55  fof(f132,plain,(
% 1.29/0.55    spl3_9 | ~spl3_7),
% 1.29/0.55    inference(avatar_split_clause,[],[f119,f111,f130])).
% 1.29/0.55  fof(f127,plain,(
% 1.29/0.55    spl3_8 | ~spl3_7),
% 1.29/0.55    inference(avatar_split_clause,[],[f118,f111,f125])).
% 1.29/0.55  fof(f118,plain,(
% 1.29/0.55    sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | ~spl3_7),
% 1.29/0.55    inference(superposition,[],[f29,f112])).
% 1.29/0.55  fof(f29,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.29/0.55    inference(cnf_transformation,[],[f9])).
% 1.29/0.55  fof(f9,axiom,(
% 1.29/0.55    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.29/0.55  fof(f113,plain,(
% 1.29/0.55    spl3_7 | ~spl3_4),
% 1.29/0.55    inference(avatar_split_clause,[],[f94,f82,f111])).
% 1.29/0.55  fof(f82,plain,(
% 1.29/0.55    spl3_4 <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.29/0.55  fof(f94,plain,(
% 1.29/0.55    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl3_4),
% 1.29/0.55    inference(superposition,[],[f83,f45])).
% 1.29/0.55  fof(f45,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f1])).
% 1.29/0.55  fof(f1,axiom,(
% 1.29/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.29/0.55  fof(f83,plain,(
% 1.29/0.55    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~spl3_4),
% 1.29/0.55    inference(avatar_component_clause,[],[f82])).
% 1.29/0.55  fof(f84,plain,(
% 1.29/0.55    spl3_4 | ~spl3_2),
% 1.29/0.55    inference(avatar_split_clause,[],[f72,f63,f82])).
% 1.29/0.55  fof(f63,plain,(
% 1.29/0.55    spl3_2 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.29/0.55  fof(f72,plain,(
% 1.29/0.55    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~spl3_2),
% 1.29/0.55    inference(resolution,[],[f64,f44])).
% 1.29/0.55  fof(f44,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.29/0.55    inference(cnf_transformation,[],[f26])).
% 1.29/0.55  fof(f26,plain,(
% 1.29/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f7])).
% 1.29/0.55  fof(f7,axiom,(
% 1.29/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.29/0.55  fof(f64,plain,(
% 1.29/0.55    r1_tarski(k1_tarski(sK0),sK1) | ~spl3_2),
% 1.29/0.55    inference(avatar_component_clause,[],[f63])).
% 1.29/0.55  fof(f69,plain,(
% 1.29/0.55    ~spl3_3),
% 1.29/0.55    inference(avatar_split_clause,[],[f28,f67])).
% 1.29/0.55  fof(f28,plain,(
% 1.29/0.55    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.29/0.55    inference(cnf_transformation,[],[f22])).
% 1.29/0.55  fof(f22,plain,(
% 1.29/0.55    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f20])).
% 1.29/0.55  fof(f20,negated_conjecture,(
% 1.29/0.55    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.29/0.55    inference(negated_conjecture,[],[f19])).
% 1.29/0.55  fof(f19,conjecture,(
% 1.29/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.29/0.55  fof(f65,plain,(
% 1.29/0.55    spl3_2 | ~spl3_1),
% 1.29/0.55    inference(avatar_split_clause,[],[f61,f55,f63])).
% 1.29/0.55  fof(f55,plain,(
% 1.29/0.55    spl3_1 <=> r2_hidden(sK0,sK1)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.29/0.55  fof(f61,plain,(
% 1.29/0.55    r1_tarski(k1_tarski(sK0),sK1) | ~spl3_1),
% 1.29/0.55    inference(resolution,[],[f56,f32])).
% 1.29/0.55  fof(f32,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f17])).
% 1.29/0.55  fof(f17,axiom,(
% 1.29/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.29/0.55  fof(f56,plain,(
% 1.29/0.55    r2_hidden(sK0,sK1) | ~spl3_1),
% 1.29/0.55    inference(avatar_component_clause,[],[f55])).
% 1.29/0.55  fof(f57,plain,(
% 1.29/0.55    spl3_1),
% 1.29/0.55    inference(avatar_split_clause,[],[f27,f55])).
% 1.29/0.55  fof(f27,plain,(
% 1.29/0.55    r2_hidden(sK0,sK1)),
% 1.29/0.55    inference(cnf_transformation,[],[f22])).
% 1.29/0.55  % SZS output end Proof for theBenchmark
% 1.29/0.55  % (32362)------------------------------
% 1.29/0.55  % (32362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (32362)Termination reason: Refutation
% 1.29/0.55  
% 1.29/0.55  % (32362)Memory used [KB]: 6268
% 1.29/0.55  % (32362)Time elapsed: 0.098 s
% 1.29/0.55  % (32362)------------------------------
% 1.29/0.55  % (32362)------------------------------
% 1.29/0.55  % (32351)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.47/0.55  % (32333)Success in time 0.186 s
%------------------------------------------------------------------------------
