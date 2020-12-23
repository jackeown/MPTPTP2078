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
% DateTime   : Thu Dec  3 12:48:58 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   60 (  87 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 196 expanded)
%              Number of equality atoms :   27 (  50 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f146,f151,f156])).

fof(f156,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f45,f145,f123])).

fof(f123,plain,
    ( ! [X2] :
        ( r1_tarski(k2_relat_1(k8_relat_1(sK0,X2)),sK1)
        | ~ v1_relat_1(X2) )
    | ~ spl3_2 ),
    inference(superposition,[],[f81,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f81,plain,
    ( ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(X0,sK0)),sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f78,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f78,plain,
    ( ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(sK0,X0)),sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f73,f39])).

fof(f73,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f69,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f69,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f50])).

fof(f50,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f145,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_7
  <=> r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f45,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f151,plain,
    ( ~ spl3_1
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl3_1
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f45,f141,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f141,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_6
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f146,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | spl3_3 ),
    inference(avatar_split_clause,[],[f91,f53,f143,f139])).

fof(f53,plain,
    ( spl3_3
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f91,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl3_3 ),
    inference(trivial_inequality_removal,[],[f88])).

fof(f88,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2)
    | ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl3_3 ),
    inference(superposition,[],[f55,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f55,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f56,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f51,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (19756)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (19780)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (19757)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (19757)Refutation not found, incomplete strategy% (19757)------------------------------
% 0.21/0.52  % (19757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19757)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19757)Memory used [KB]: 1663
% 0.21/0.52  % (19757)Time elapsed: 0.102 s
% 0.21/0.52  % (19757)------------------------------
% 0.21/0.52  % (19757)------------------------------
% 1.25/0.53  % (19760)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.25/0.53  % (19761)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.25/0.53  % (19779)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.25/0.53  % (19768)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.25/0.53  % (19778)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.25/0.54  % (19779)Refutation found. Thanks to Tanya!
% 1.25/0.54  % SZS status Theorem for theBenchmark
% 1.25/0.54  % (19776)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.25/0.54  % SZS output start Proof for theBenchmark
% 1.25/0.54  fof(f157,plain,(
% 1.25/0.54    $false),
% 1.25/0.54    inference(avatar_sat_refutation,[],[f46,f51,f56,f146,f151,f156])).
% 1.25/0.54  fof(f156,plain,(
% 1.25/0.54    ~spl3_1 | ~spl3_2 | spl3_7),
% 1.25/0.54    inference(avatar_contradiction_clause,[],[f153])).
% 1.25/0.54  fof(f153,plain,(
% 1.25/0.54    $false | (~spl3_1 | ~spl3_2 | spl3_7)),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f45,f145,f123])).
% 1.25/0.54  fof(f123,plain,(
% 1.25/0.54    ( ! [X2] : (r1_tarski(k2_relat_1(k8_relat_1(sK0,X2)),sK1) | ~v1_relat_1(X2)) ) | ~spl3_2),
% 1.25/0.54    inference(superposition,[],[f81,f109])).
% 1.25/0.54  fof(f109,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.25/0.54    inference(forward_demodulation,[],[f38,f39])).
% 1.25/0.54  fof(f39,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.25/0.54    inference(definition_unfolding,[],[f36,f35])).
% 1.25/0.54  fof(f35,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f4])).
% 1.25/0.54  fof(f4,axiom,(
% 1.25/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.25/0.54  fof(f36,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.25/0.54    inference(cnf_transformation,[],[f6])).
% 1.25/0.54  fof(f6,axiom,(
% 1.25/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.25/0.54  fof(f38,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.25/0.54    inference(definition_unfolding,[],[f31,f35])).
% 1.25/0.54  fof(f31,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f16])).
% 1.25/0.54  fof(f16,plain,(
% 1.25/0.54    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.25/0.54    inference(ennf_transformation,[],[f8])).
% 1.25/0.54  fof(f8,axiom,(
% 1.25/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 1.25/0.54  fof(f81,plain,(
% 1.25/0.54    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(X0,sK0)),sK1)) ) | ~spl3_2),
% 1.25/0.54    inference(superposition,[],[f78,f37])).
% 1.25/0.54  fof(f37,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f5])).
% 1.25/0.54  fof(f5,axiom,(
% 1.25/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.25/0.54  fof(f78,plain,(
% 1.25/0.54    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(sK0,X0)),sK1)) ) | ~spl3_2),
% 1.25/0.54    inference(superposition,[],[f73,f39])).
% 1.25/0.54  fof(f73,plain,(
% 1.25/0.54    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),sK1)) ) | ~spl3_2),
% 1.25/0.54    inference(resolution,[],[f69,f34])).
% 1.25/0.54  fof(f34,plain,(
% 1.25/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f3])).
% 1.25/0.54  fof(f3,axiom,(
% 1.25/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.25/0.54  fof(f69,plain,(
% 1.25/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,sK1)) ) | ~spl3_2),
% 1.25/0.54    inference(resolution,[],[f33,f50])).
% 1.25/0.54  fof(f50,plain,(
% 1.25/0.54    r1_tarski(sK0,sK1) | ~spl3_2),
% 1.25/0.54    inference(avatar_component_clause,[],[f48])).
% 1.25/0.54  fof(f48,plain,(
% 1.25/0.54    spl3_2 <=> r1_tarski(sK0,sK1)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.25/0.54  fof(f33,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f19])).
% 1.25/0.54  fof(f19,plain,(
% 1.25/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.25/0.54    inference(flattening,[],[f18])).
% 1.25/0.54  fof(f18,plain,(
% 1.25/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.25/0.54    inference(ennf_transformation,[],[f2])).
% 1.25/0.54  fof(f2,axiom,(
% 1.25/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.25/0.54  fof(f145,plain,(
% 1.25/0.54    ~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) | spl3_7),
% 1.25/0.54    inference(avatar_component_clause,[],[f143])).
% 1.25/0.54  fof(f143,plain,(
% 1.25/0.54    spl3_7 <=> r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.25/0.54  fof(f45,plain,(
% 1.25/0.54    v1_relat_1(sK2) | ~spl3_1),
% 1.25/0.54    inference(avatar_component_clause,[],[f43])).
% 1.25/0.54  fof(f43,plain,(
% 1.25/0.54    spl3_1 <=> v1_relat_1(sK2)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.25/0.54  fof(f151,plain,(
% 1.25/0.54    ~spl3_1 | spl3_6),
% 1.25/0.54    inference(avatar_contradiction_clause,[],[f147])).
% 1.25/0.54  fof(f147,plain,(
% 1.25/0.54    $false | (~spl3_1 | spl3_6)),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f45,f141,f32])).
% 1.25/0.54  fof(f32,plain,(
% 1.25/0.54    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f17])).
% 1.25/0.54  fof(f17,plain,(
% 1.25/0.54    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 1.25/0.54    inference(ennf_transformation,[],[f7])).
% 1.25/0.54  fof(f7,axiom,(
% 1.25/0.54    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 1.25/0.54  fof(f141,plain,(
% 1.25/0.54    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl3_6),
% 1.25/0.54    inference(avatar_component_clause,[],[f139])).
% 1.25/0.54  fof(f139,plain,(
% 1.25/0.54    spl3_6 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.25/0.54  fof(f146,plain,(
% 1.25/0.54    ~spl3_6 | ~spl3_7 | spl3_3),
% 1.25/0.54    inference(avatar_split_clause,[],[f91,f53,f143,f139])).
% 1.25/0.54  fof(f53,plain,(
% 1.25/0.54    spl3_3 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.25/0.54  fof(f91,plain,(
% 1.25/0.54    ~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl3_3),
% 1.25/0.54    inference(trivial_inequality_removal,[],[f88])).
% 1.25/0.54  fof(f88,plain,(
% 1.25/0.54    k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2) | ~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl3_3),
% 1.25/0.54    inference(superposition,[],[f55,f30])).
% 1.25/0.54  fof(f30,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f15])).
% 1.25/0.54  fof(f15,plain,(
% 1.25/0.54    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.25/0.54    inference(flattening,[],[f14])).
% 1.25/0.54  fof(f14,plain,(
% 1.25/0.54    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.25/0.54    inference(ennf_transformation,[],[f9])).
% 1.25/0.54  fof(f9,axiom,(
% 1.25/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 1.25/0.54  fof(f55,plain,(
% 1.25/0.54    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | spl3_3),
% 1.25/0.54    inference(avatar_component_clause,[],[f53])).
% 1.25/0.54  fof(f56,plain,(
% 1.25/0.54    ~spl3_3),
% 1.25/0.54    inference(avatar_split_clause,[],[f26,f53])).
% 1.25/0.54  fof(f26,plain,(
% 1.25/0.54    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 1.25/0.54    inference(cnf_transformation,[],[f21])).
% 1.25/0.54  fof(f21,plain,(
% 1.25/0.54    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f20])).
% 1.25/0.54  fof(f20,plain,(
% 1.25/0.54    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f13,plain,(
% 1.25/0.54    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.25/0.54    inference(flattening,[],[f12])).
% 1.25/0.54  fof(f12,plain,(
% 1.25/0.54    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.25/0.54    inference(ennf_transformation,[],[f11])).
% 1.25/0.54  fof(f11,negated_conjecture,(
% 1.25/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 1.25/0.54    inference(negated_conjecture,[],[f10])).
% 1.25/0.54  fof(f10,conjecture,(
% 1.25/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 1.25/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 1.25/0.54  fof(f51,plain,(
% 1.25/0.54    spl3_2),
% 1.25/0.54    inference(avatar_split_clause,[],[f25,f48])).
% 1.25/0.54  fof(f25,plain,(
% 1.25/0.54    r1_tarski(sK0,sK1)),
% 1.25/0.54    inference(cnf_transformation,[],[f21])).
% 1.25/0.54  fof(f46,plain,(
% 1.25/0.54    spl3_1),
% 1.25/0.54    inference(avatar_split_clause,[],[f24,f43])).
% 1.25/0.54  fof(f24,plain,(
% 1.25/0.54    v1_relat_1(sK2)),
% 1.25/0.54    inference(cnf_transformation,[],[f21])).
% 1.25/0.54  % SZS output end Proof for theBenchmark
% 1.25/0.54  % (19779)------------------------------
% 1.25/0.54  % (19779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (19779)Termination reason: Refutation
% 1.25/0.54  
% 1.25/0.54  % (19779)Memory used [KB]: 10746
% 1.25/0.54  % (19779)Time elapsed: 0.112 s
% 1.25/0.54  % (19779)------------------------------
% 1.25/0.54  % (19779)------------------------------
% 1.25/0.54  % (19755)Success in time 0.179 s
%------------------------------------------------------------------------------
