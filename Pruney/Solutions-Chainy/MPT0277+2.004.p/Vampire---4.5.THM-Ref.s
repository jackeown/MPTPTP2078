%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 140 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :   20
%              Number of atoms          :  148 ( 334 expanded)
%              Number of equality atoms :  110 ( 288 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f135,f153])).

fof(f153,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f151,f119])).

fof(f119,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f151,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f142,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f142,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl5_2 ),
    inference(superposition,[],[f96,f122])).

fof(f122,plain,
    ( sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_2
  <=> sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f96,plain,(
    ! [X2,X1] : r1_tarski(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) != X0
      | r1_tarski(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ) ),
    inference(definition_unfolding,[],[f48,f53,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(f135,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f133,f114])).

fof(f114,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f113,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f113,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(inner_rewriting,[],[f76])).

fof(f76,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f35,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f133,plain,
    ( k1_xboole_0 = sK0
    | spl5_2 ),
    inference(subsumption_resolution,[],[f132,f123])).

fof(f123,plain,
    ( sK0 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f132,plain,
    ( sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | k1_xboole_0 = sK0
    | spl5_2 ),
    inference(subsumption_resolution,[],[f131,f108])).

fof(f108,plain,(
    sK0 != k1_tarski(sK2) ),
    inference(subsumption_resolution,[],[f107,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f107,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,k1_tarski(sK1)))
    | sK0 != k1_tarski(sK2) ),
    inference(forward_demodulation,[],[f106,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f106,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),sK0)) ),
    inference(inner_rewriting,[],[f74])).

fof(f74,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f37,f53])).

fof(f37,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f131,plain,
    ( sK0 = k1_tarski(sK2)
    | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | k1_xboole_0 = sK0
    | spl5_2 ),
    inference(subsumption_resolution,[],[f128,f111])).

fof(f111,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f110,f54])).

fof(f110,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,k1_tarski(sK2))) ),
    inference(inner_rewriting,[],[f75])).

fof(f75,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f36,f53])).

fof(f36,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f128,plain,
    ( sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | k1_xboole_0 = sK0
    | spl5_2 ),
    inference(resolution,[],[f127,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f44,f53,f53])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f127,plain,
    ( r1_tarski(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | spl5_2 ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | spl5_2 ),
    inference(superposition,[],[f68,f125])).

fof(f125,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f115,f123])).

fof(f115,plain,
    ( sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(subsumption_resolution,[],[f112,f114])).

fof(f112,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(subsumption_resolution,[],[f109,f111])).

fof(f109,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(subsumption_resolution,[],[f72,f108])).

fof(f72,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f39,f53,f53])).

fof(f39,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f124,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f105,f121,f117])).

fof(f105,plain,
    ( sK0 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | k1_xboole_0 != k4_xboole_0(sK0,sK0) ),
    inference(inner_rewriting,[],[f73])).

fof(f73,plain,
    ( sK0 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f38,f53,f53])).

fof(f38,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:50:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (23978)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (24001)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.51  % (23993)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (23992)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (23995)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (23982)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (23983)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (23973)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (23973)Refutation not found, incomplete strategy% (23973)------------------------------
% 0.22/0.52  % (23973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23973)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (23973)Memory used [KB]: 1663
% 0.22/0.52  % (23973)Time elapsed: 0.105 s
% 0.22/0.52  % (23973)------------------------------
% 0.22/0.52  % (23973)------------------------------
% 0.22/0.52  % (23981)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (23984)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (23977)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (23972)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (23976)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (23975)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (24000)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (24002)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (24002)Refutation not found, incomplete strategy% (24002)------------------------------
% 0.22/0.54  % (24002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24002)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (24002)Memory used [KB]: 1663
% 0.22/0.54  % (24002)Time elapsed: 0.129 s
% 0.22/0.54  % (24002)------------------------------
% 0.22/0.54  % (24002)------------------------------
% 0.22/0.54  % (24000)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (23974)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (23994)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (23986)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (23985)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (23996)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (23998)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (23987)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (23988)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (23999)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f124,f135,f153])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    spl5_1 | ~spl5_2),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f152])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    $false | (spl5_1 | ~spl5_2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f151,f119])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    k1_xboole_0 != k4_xboole_0(sK0,sK0) | spl5_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f117])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    spl5_1 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl5_2),
% 0.22/0.55    inference(resolution,[],[f142,f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    r1_tarski(sK0,sK0) | ~spl5_2),
% 0.22/0.55    inference(superposition,[],[f96,f122])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | ~spl5_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f121])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    spl5_2 <=> sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ( ! [X2,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) )),
% 0.22/0.55    inference(equality_resolution,[],[f81])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) != X0 | r1_tarski(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f48,f53,f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,axiom,(
% 0.22/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    spl5_2),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f134])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    $false | spl5_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f133,f114])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    k1_xboole_0 != sK0),
% 0.22/0.55    inference(subsumption_resolution,[],[f113,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.55  fof(f113,plain,(
% 0.22/0.55    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.55    inference(inner_rewriting,[],[f76])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.55    inference(definition_unfolding,[],[f35,f53])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.22/0.55    inference(negated_conjecture,[],[f28])).
% 0.22/0.55  fof(f28,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | spl5_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f132,f123])).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    sK0 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | spl5_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f121])).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | k1_xboole_0 = sK0 | spl5_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f131,f108])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    sK0 != k1_tarski(sK2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f107,f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,k1_tarski(sK1))) | sK0 != k1_tarski(sK2)),
% 0.22/0.55    inference(forward_demodulation,[],[f106,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),sK0))),
% 0.22/0.55    inference(inner_rewriting,[],[f74])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.55    inference(definition_unfolding,[],[f37,f53])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    sK0 = k1_tarski(sK2) | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | k1_xboole_0 = sK0 | spl5_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f128,f111])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    sK0 != k1_tarski(sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f110,f54])).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,k1_tarski(sK2)))),
% 0.22/0.55    inference(inner_rewriting,[],[f75])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.55    inference(definition_unfolding,[],[f36,f53])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    sK0 = k1_tarski(sK1) | sK0 = k1_tarski(sK2) | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | k1_xboole_0 = sK0 | spl5_2),
% 0.22/0.55    inference(resolution,[],[f127,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(definition_unfolding,[],[f44,f53,f53])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    r1_tarski(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | spl5_2),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f126])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | spl5_2),
% 0.22/0.55    inference(superposition,[],[f68,f125])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | spl5_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f115,f123])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f112,f114])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f109,f111])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f72,f108])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | sK0 = k1_tarski(sK2) | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.55    inference(definition_unfolding,[],[f39,f53,f53])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | sK0 = k1_tarski(sK2) | sK0 = k2_tarski(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    ~spl5_1 | ~spl5_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f105,f121,f117])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    sK0 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | k1_xboole_0 != k4_xboole_0(sK0,sK0)),
% 0.22/0.55    inference(inner_rewriting,[],[f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    sK0 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.55    inference(definition_unfolding,[],[f38,f53,f53])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (24000)------------------------------
% 0.22/0.55  % (24000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24000)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (24000)Memory used [KB]: 6268
% 0.22/0.55  % (24000)Time elapsed: 0.131 s
% 0.22/0.55  % (24000)------------------------------
% 0.22/0.55  % (24000)------------------------------
% 0.22/0.55  % (23990)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (23968)Success in time 0.194 s
%------------------------------------------------------------------------------
