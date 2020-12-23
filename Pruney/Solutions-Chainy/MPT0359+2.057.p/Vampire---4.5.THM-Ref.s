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
% DateTime   : Thu Dec  3 12:44:46 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 161 expanded)
%              Number of leaves         :   15 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  159 ( 309 expanded)
%              Number of equality atoms :   39 ( 114 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f79,f131,f174,f180,f228])).

fof(f228,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f30,f207,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f207,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_zfmisc_1(sK0))
    | ~ spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f206,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f206,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f182,f193,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f193,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | ~ spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f184,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f184,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | ~ spl4_2
    | spl4_3 ),
    inference(backward_demodulation,[],[f77,f62])).

fof(f62,plain,
    ( sK0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f77,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_3
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f182,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f51,f62])).

fof(f51,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f20,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f180,plain,
    ( spl4_2
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl4_2
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f63,f141])).

fof(f141,plain,
    ( sK0 = sK1
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f133,f42])).

fof(f42,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f23,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f22,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f22,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f23,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f133,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f52,f130])).

fof(f130,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_6
  <=> k1_xboole_0 = k3_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f52,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f63,plain,
    ( sK0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f174,plain,
    ( spl4_1
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl4_1
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f30,f161])).

fof(f161,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl4_1
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f59,f154])).

fof(f154,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK0)
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f130,f141])).

fof(f59,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_1
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f131,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f73,f76,f128])).

fof(f73,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k1_xboole_0 = k3_subset_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f69,f52])).

fof(f69,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK1)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f51,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f79,plain,
    ( spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f50,f61,f76])).

fof(f50,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f41,f42])).

fof(f41,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f18,f39])).

fof(f18,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f49,f61,f57])).

fof(f49,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    inference(inner_rewriting,[],[f48])).

fof(f48,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f40,f42])).

fof(f40,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f19,f39])).

fof(f19,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:56:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (4343)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.18/0.51  % (4342)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.18/0.52  % (4336)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.18/0.52  % (4334)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.18/0.52  % (4342)Refutation not found, incomplete strategy% (4342)------------------------------
% 1.18/0.52  % (4342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (4342)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.52  
% 1.18/0.52  % (4342)Memory used [KB]: 10618
% 1.18/0.52  % (4342)Time elapsed: 0.111 s
% 1.18/0.52  % (4342)------------------------------
% 1.18/0.52  % (4342)------------------------------
% 1.18/0.52  % (4338)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.18/0.52  % (4334)Refutation not found, incomplete strategy% (4334)------------------------------
% 1.18/0.52  % (4334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (4334)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.52  
% 1.18/0.52  % (4334)Memory used [KB]: 10618
% 1.18/0.52  % (4334)Time elapsed: 0.113 s
% 1.18/0.52  % (4334)------------------------------
% 1.18/0.52  % (4334)------------------------------
% 1.18/0.53  % (4333)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.18/0.53  % (4355)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.18/0.53  % (4335)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.18/0.53  % (4337)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.53  % (4350)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.54  % (4344)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.54  % (4352)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.54  % (4347)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.54  % (4336)Refutation found. Thanks to Tanya!
% 1.32/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % SZS output start Proof for theBenchmark
% 1.32/0.54  fof(f229,plain,(
% 1.32/0.54    $false),
% 1.32/0.54    inference(avatar_sat_refutation,[],[f64,f79,f131,f174,f180,f228])).
% 1.32/0.54  fof(f228,plain,(
% 1.32/0.54    ~spl4_2 | spl4_3),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f224])).
% 1.32/0.54  fof(f224,plain,(
% 1.32/0.54    $false | (~spl4_2 | spl4_3)),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f30,f207,f46])).
% 1.32/0.54  fof(f46,plain,(
% 1.32/0.54    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(equality_resolution,[],[f24])).
% 1.32/0.54  fof(f24,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.32/0.54    inference(cnf_transformation,[],[f3])).
% 1.32/0.54  fof(f3,axiom,(
% 1.32/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.32/0.54  fof(f207,plain,(
% 1.32/0.54    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK0))) ) | (~spl4_2 | spl4_3)),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f206,f38])).
% 1.32/0.54  fof(f38,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f1])).
% 1.32/0.54  fof(f1,axiom,(
% 1.32/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.32/0.54  fof(f206,plain,(
% 1.32/0.54    v1_xboole_0(k1_zfmisc_1(sK0)) | (~spl4_2 | spl4_3)),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f182,f193,f36])).
% 1.32/0.54  fof(f36,plain,(
% 1.32/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f17])).
% 1.32/0.54  fof(f17,plain,(
% 1.32/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f4])).
% 1.32/0.54  fof(f4,axiom,(
% 1.32/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.32/0.54  fof(f193,plain,(
% 1.32/0.54    ~r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | (~spl4_2 | spl4_3)),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f184,f45])).
% 1.32/0.54  fof(f45,plain,(
% 1.32/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.32/0.54    inference(equality_resolution,[],[f25])).
% 1.32/0.54  fof(f25,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.32/0.54    inference(cnf_transformation,[],[f3])).
% 1.32/0.54  fof(f184,plain,(
% 1.32/0.54    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (~spl4_2 | spl4_3)),
% 1.32/0.54    inference(backward_demodulation,[],[f77,f62])).
% 1.32/0.54  fof(f62,plain,(
% 1.32/0.54    sK0 = sK1 | ~spl4_2),
% 1.32/0.54    inference(avatar_component_clause,[],[f61])).
% 1.32/0.54  fof(f61,plain,(
% 1.32/0.54    spl4_2 <=> sK0 = sK1),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.32/0.54  fof(f77,plain,(
% 1.32/0.54    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl4_3),
% 1.32/0.54    inference(avatar_component_clause,[],[f76])).
% 1.32/0.54  fof(f76,plain,(
% 1.32/0.54    spl4_3 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.32/0.54  fof(f182,plain,(
% 1.32/0.54    m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | ~spl4_2),
% 1.32/0.54    inference(backward_demodulation,[],[f51,f62])).
% 1.32/0.54  fof(f51,plain,(
% 1.32/0.54    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f20,f31])).
% 1.32/0.54  fof(f31,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f16])).
% 1.32/0.54  fof(f16,plain,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f7])).
% 1.32/0.54  fof(f7,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.32/0.54  fof(f20,plain,(
% 1.32/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.32/0.54    inference(cnf_transformation,[],[f13])).
% 1.32/0.54  fof(f13,plain,(
% 1.32/0.54    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f12])).
% 1.32/0.54  fof(f12,negated_conjecture,(
% 1.32/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.32/0.54    inference(negated_conjecture,[],[f11])).
% 1.32/0.54  fof(f11,conjecture,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 1.32/0.54  fof(f30,plain,(
% 1.32/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f2])).
% 1.32/0.54  fof(f2,axiom,(
% 1.32/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.32/0.54  fof(f180,plain,(
% 1.32/0.54    spl4_2 | ~spl4_6),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f176])).
% 1.32/0.54  fof(f176,plain,(
% 1.32/0.54    $false | (spl4_2 | ~spl4_6)),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f63,f141])).
% 1.32/0.54  fof(f141,plain,(
% 1.32/0.54    sK0 = sK1 | ~spl4_6),
% 1.32/0.54    inference(forward_demodulation,[],[f133,f42])).
% 1.32/0.54  fof(f42,plain,(
% 1.32/0.54    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.32/0.54    inference(definition_unfolding,[],[f23,f39])).
% 1.32/0.54  fof(f39,plain,(
% 1.32/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f22,f32])).
% 1.32/0.54  fof(f32,plain,(
% 1.32/0.54    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f5])).
% 1.32/0.54  fof(f5,axiom,(
% 1.32/0.54    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.32/0.54  fof(f22,plain,(
% 1.32/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f9])).
% 1.32/0.54  fof(f9,axiom,(
% 1.32/0.54    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 1.32/0.54  fof(f23,plain,(
% 1.32/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f6])).
% 1.32/0.54  fof(f6,axiom,(
% 1.32/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.32/0.54  fof(f133,plain,(
% 1.32/0.54    sK1 = k3_subset_1(sK0,k1_xboole_0) | ~spl4_6),
% 1.32/0.54    inference(backward_demodulation,[],[f52,f130])).
% 1.32/0.54  fof(f130,plain,(
% 1.32/0.54    k1_xboole_0 = k3_subset_1(sK0,sK1) | ~spl4_6),
% 1.32/0.54    inference(avatar_component_clause,[],[f128])).
% 1.32/0.54  fof(f128,plain,(
% 1.32/0.54    spl4_6 <=> k1_xboole_0 = k3_subset_1(sK0,sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.32/0.54  fof(f52,plain,(
% 1.32/0.54    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f20,f21])).
% 1.32/0.54  fof(f21,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.32/0.54    inference(cnf_transformation,[],[f14])).
% 1.32/0.54  fof(f14,plain,(
% 1.32/0.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f8])).
% 1.32/0.54  fof(f8,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.32/0.54  fof(f63,plain,(
% 1.32/0.54    sK0 != sK1 | spl4_2),
% 1.32/0.54    inference(avatar_component_clause,[],[f61])).
% 1.32/0.54  fof(f174,plain,(
% 1.32/0.54    spl4_1 | ~spl4_6),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f170])).
% 1.32/0.54  fof(f170,plain,(
% 1.32/0.54    $false | (spl4_1 | ~spl4_6)),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f30,f161])).
% 1.32/0.54  fof(f161,plain,(
% 1.32/0.54    ~r1_tarski(k1_xboole_0,sK0) | (spl4_1 | ~spl4_6)),
% 1.32/0.54    inference(backward_demodulation,[],[f59,f154])).
% 1.32/0.54  fof(f154,plain,(
% 1.32/0.54    k1_xboole_0 = k3_subset_1(sK0,sK0) | ~spl4_6),
% 1.32/0.54    inference(backward_demodulation,[],[f130,f141])).
% 1.32/0.54  fof(f59,plain,(
% 1.32/0.54    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl4_1),
% 1.32/0.54    inference(avatar_component_clause,[],[f57])).
% 1.32/0.54  fof(f57,plain,(
% 1.32/0.54    spl4_1 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.32/0.54  fof(f131,plain,(
% 1.32/0.54    spl4_6 | ~spl4_3),
% 1.32/0.54    inference(avatar_split_clause,[],[f73,f76,f128])).
% 1.32/0.54  fof(f73,plain,(
% 1.32/0.54    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | k1_xboole_0 = k3_subset_1(sK0,sK1)),
% 1.32/0.54    inference(forward_demodulation,[],[f69,f52])).
% 1.32/0.54  fof(f69,plain,(
% 1.32/0.54    k1_xboole_0 = k3_subset_1(sK0,sK1) | ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,sK1)))),
% 1.32/0.54    inference(resolution,[],[f51,f43])).
% 1.32/0.54  fof(f43,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 1.32/0.54    inference(definition_unfolding,[],[f29,f32])).
% 1.32/0.54  fof(f29,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f15])).
% 1.32/0.54  fof(f15,plain,(
% 1.32/0.54    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f10])).
% 1.32/0.54  fof(f10,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 1.32/0.54  fof(f79,plain,(
% 1.32/0.54    spl4_3 | spl4_2),
% 1.32/0.54    inference(avatar_split_clause,[],[f50,f61,f76])).
% 1.32/0.54  fof(f50,plain,(
% 1.32/0.54    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.32/0.54    inference(forward_demodulation,[],[f41,f42])).
% 1.32/0.54  fof(f41,plain,(
% 1.32/0.54    sK1 = k3_subset_1(sK0,k1_xboole_0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.32/0.54    inference(definition_unfolding,[],[f18,f39])).
% 1.32/0.54  fof(f18,plain,(
% 1.32/0.54    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.32/0.54    inference(cnf_transformation,[],[f13])).
% 1.32/0.54  fof(f64,plain,(
% 1.32/0.54    ~spl4_1 | ~spl4_2),
% 1.32/0.54    inference(avatar_split_clause,[],[f49,f61,f57])).
% 1.32/0.54  fof(f49,plain,(
% 1.32/0.54    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 1.32/0.54    inference(inner_rewriting,[],[f48])).
% 1.32/0.54  fof(f48,plain,(
% 1.32/0.54    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.32/0.54    inference(forward_demodulation,[],[f40,f42])).
% 1.32/0.54  fof(f40,plain,(
% 1.32/0.54    sK1 != k3_subset_1(sK0,k1_xboole_0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.32/0.54    inference(definition_unfolding,[],[f19,f39])).
% 1.32/0.54  fof(f19,plain,(
% 1.32/0.54    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.32/0.54    inference(cnf_transformation,[],[f13])).
% 1.32/0.54  % SZS output end Proof for theBenchmark
% 1.32/0.54  % (4336)------------------------------
% 1.32/0.54  % (4336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (4336)Termination reason: Refutation
% 1.32/0.54  
% 1.32/0.54  % (4336)Memory used [KB]: 6268
% 1.32/0.54  % (4336)Time elapsed: 0.120 s
% 1.32/0.54  % (4336)------------------------------
% 1.32/0.54  % (4336)------------------------------
% 1.32/0.54  % (4358)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.54  % (4360)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.54  % (4331)Success in time 0.174 s
%------------------------------------------------------------------------------
