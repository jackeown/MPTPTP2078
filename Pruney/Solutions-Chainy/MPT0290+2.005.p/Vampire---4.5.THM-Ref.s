%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  95 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 193 expanded)
%              Number of equality atoms :   26 (  61 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f364,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f117,f202,f349])).

fof(f349,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f347,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f37,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f347,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl2_3 ),
    inference(forward_demodulation,[],[f346,f50])).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f34,f44])).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

% (12354)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (12356)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (12376)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f346,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))
    | spl2_3 ),
    inference(forward_demodulation,[],[f337,f44])).

fof(f337,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)))
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f201,f96])).

fof(f96,plain,(
    ! [X6,X8,X7] :
      ( k1_xboole_0 != k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8)))
      | r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X7)),X8) ) ),
    inference(superposition,[],[f29,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f31,f24,f24])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f201,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl2_3
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f202,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f118,f114,f199])).

fof(f114,plain,
    ( spl2_2
  <=> r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f118,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f116,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f116,plain,
    ( ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f79,f60,f114])).

fof(f60,plain,
    ( spl2_1
  <=> r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f79,plain,
    ( ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1))
    | spl2_1 ),
    inference(subsumption_resolution,[],[f71,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_tarski(k4_xboole_0(X0,X1)),k3_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f23,f25])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f71,plain,
    ( ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1))
    | ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0))
    | spl2_1 ),
    inference(resolution,[],[f36,f62])).

fof(f62,plain,
    ( ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f24])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

% (12374)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f63,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))) ),
    inference(definition_unfolding,[],[f21,f24,f24])).

fof(f21,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).

% (12356)Refutation not found, incomplete strategy% (12356)------------------------------
% (12356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12356)Termination reason: Refutation not found, incomplete strategy

% (12356)Memory used [KB]: 6140
% (12356)Time elapsed: 0.139 s
% (12356)------------------------------
% (12356)------------------------------
fof(f16,plain,
    ( ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))
   => ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (12347)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (12377)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (12367)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (12368)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (12344)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (12349)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (12348)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (12377)Refutation not found, incomplete strategy% (12377)------------------------------
% 0.20/0.54  % (12377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12377)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12377)Memory used [KB]: 1663
% 0.20/0.54  % (12377)Time elapsed: 0.120 s
% 0.20/0.54  % (12377)------------------------------
% 0.20/0.54  % (12377)------------------------------
% 0.20/0.54  % (12369)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (12346)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (12345)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (12345)Refutation not found, incomplete strategy% (12345)------------------------------
% 0.20/0.54  % (12345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12345)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12345)Memory used [KB]: 1663
% 0.20/0.54  % (12345)Time elapsed: 0.119 s
% 0.20/0.54  % (12345)------------------------------
% 0.20/0.54  % (12345)------------------------------
% 0.20/0.54  % (12360)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (12352)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (12351)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (12375)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (12365)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (12367)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f364,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f63,f117,f202,f349])).
% 0.20/0.55  fof(f349,plain,(
% 0.20/0.55    spl2_3),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f348])).
% 0.20/0.55  fof(f348,plain,(
% 0.20/0.55    $false | spl2_3),
% 0.20/0.55    inference(subsumption_resolution,[],[f347,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f37,f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.55    inference(nnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(flattening,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.55  fof(f347,plain,(
% 0.20/0.55    k1_xboole_0 != k4_xboole_0(sK0,sK0) | spl2_3),
% 0.20/0.55    inference(forward_demodulation,[],[f346,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.55    inference(backward_demodulation,[],[f34,f44])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.20/0.55    inference(definition_unfolding,[],[f22,f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,plain,(
% 0.20/0.55    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.55    inference(rectify,[],[f1])).
% 0.20/0.55  % (12354)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (12356)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (12376)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.55  fof(f346,plain,(
% 0.20/0.55    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) | spl2_3),
% 0.20/0.55    inference(forward_demodulation,[],[f337,f44])).
% 0.20/0.55  fof(f337,plain,(
% 0.20/0.55    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))) | spl2_3),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f201,f96])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    ( ! [X6,X8,X7] : (k1_xboole_0 != k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X8))) | r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X7)),X8)) )),
% 0.20/0.55    inference(superposition,[],[f29,f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f31,f24,f24])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f201,plain,(
% 0.20/0.55    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) | spl2_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f199])).
% 0.20/0.55  fof(f199,plain,(
% 0.20/0.55    spl2_3 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    ~spl2_3 | spl2_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f118,f114,f199])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    spl2_2 <=> r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.55  fof(f118,plain,(
% 0.20/0.55    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) | spl2_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f116,f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.20/0.55  fof(f116,plain,(
% 0.20/0.55    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1)) | spl2_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f114])).
% 0.20/0.55  fof(f117,plain,(
% 0.20/0.55    ~spl2_2 | spl2_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f79,f60,f114])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    spl2_1 <=> r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1)) | spl2_1),
% 0.20/0.55    inference(subsumption_resolution,[],[f71,f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k3_tarski(k4_xboole_0(X0,X1)),k3_tarski(X0))) )),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f23,f25])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1)) | ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0)) | spl2_1),
% 0.20/0.55    inference(resolution,[],[f36,f62])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))) | spl2_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f60])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f32,f24])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.55    inference(flattening,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.55  % (12374)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ~spl2_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f33,f60])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))),
% 0.20/0.55    inference(definition_unfolding,[],[f21,f24,f24])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).
% 0.20/0.55  % (12356)Refutation not found, incomplete strategy% (12356)------------------------------
% 0.20/0.55  % (12356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12356)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (12356)Memory used [KB]: 6140
% 0.20/0.55  % (12356)Time elapsed: 0.139 s
% 0.20/0.55  % (12356)------------------------------
% 0.20/0.55  % (12356)------------------------------
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) => ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.20/0.55    inference(negated_conjecture,[],[f9])).
% 0.20/0.55  fof(f9,conjecture,(
% 0.20/0.55    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_zfmisc_1)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (12367)------------------------------
% 0.20/0.55  % (12367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12367)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (12367)Memory used [KB]: 10874
% 0.20/0.55  % (12367)Time elapsed: 0.117 s
% 0.20/0.55  % (12367)------------------------------
% 0.20/0.55  % (12367)------------------------------
% 0.20/0.55  % (12374)Refutation not found, incomplete strategy% (12374)------------------------------
% 0.20/0.55  % (12374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12363)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (12371)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (12376)Refutation not found, incomplete strategy% (12376)------------------------------
% 0.20/0.55  % (12376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12365)Refutation not found, incomplete strategy% (12365)------------------------------
% 0.20/0.55  % (12365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12365)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (12365)Memory used [KB]: 1663
% 0.20/0.55  % (12365)Time elapsed: 0.140 s
% 0.20/0.55  % (12365)------------------------------
% 0.20/0.55  % (12365)------------------------------
% 0.20/0.55  % (12339)Success in time 0.187 s
%------------------------------------------------------------------------------
