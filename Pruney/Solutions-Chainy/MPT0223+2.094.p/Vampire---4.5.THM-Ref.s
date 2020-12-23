%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  46 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 (  81 expanded)
%              Number of equality atoms :   37 (  49 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f34,f40,f46,f50])).

fof(f50,plain,
    ( spl2_1
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f48,f29])).

fof(f29,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f48,plain,
    ( sK0 = sK1
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f47])).

fof(f47,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | sK0 = sK1
    | ~ spl2_4 ),
    inference(superposition,[],[f20,f45])).

fof(f45,plain,
    ( k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_4
  <=> k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f46,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f42,f38,f44])).

fof(f38,plain,
    ( spl2_3
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f42,plain,
    ( k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f41,f23])).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f41,plain,
    ( k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK1),k1_xboole_0)
    | ~ spl2_3 ),
    inference(superposition,[],[f22,f39])).

fof(f39,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f40,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f36,f32,f38])).

fof(f32,plain,
    ( spl2_2
  <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f36,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f35,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f35,plain,
    ( k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl2_2 ),
    inference(superposition,[],[f19,f33])).

fof(f33,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f32])).

fof(f17,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f30,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f18,f28])).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (12196)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (12173)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (12170)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (12182)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (12182)Refutation not found, incomplete strategy% (12182)------------------------------
% 0.21/0.53  % (12182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12182)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12182)Memory used [KB]: 10618
% 0.21/0.53  % (12182)Time elapsed: 0.117 s
% 0.21/0.53  % (12182)------------------------------
% 0.21/0.53  % (12182)------------------------------
% 0.21/0.53  % (12175)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (12197)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (12196)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f30,f34,f40,f46,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    spl2_1 | ~spl2_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    $false | (spl2_1 | ~spl2_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f48,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    sK0 != sK1 | spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    spl2_1 <=> sK0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    sK0 = sK1 | ~spl2_4),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    k1_tarski(sK1) != k1_tarski(sK1) | sK0 = sK1 | ~spl2_4),
% 0.21/0.53    inference(superposition,[],[f20,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | ~spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    spl2_4 <=> k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 | k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    spl2_4 | ~spl2_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f42,f38,f44])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    spl2_3 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | ~spl2_3),
% 0.21/0.53    inference(forward_demodulation,[],[f41,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK1),k1_xboole_0) | ~spl2_3),
% 0.21/0.53    inference(superposition,[],[f22,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f38])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    spl2_3 | ~spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f32,f38])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    spl2_2 <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl2_2),
% 0.21/0.53    inference(forward_demodulation,[],[f35,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | ~spl2_2),
% 0.21/0.53    inference(superposition,[],[f19,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f32])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f17,f32])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.53    inference(negated_conjecture,[],[f13])).
% 0.21/0.53  fof(f13,conjecture,(
% 0.21/0.53    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ~spl2_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f18,f28])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    sK0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (12196)------------------------------
% 0.21/0.53  % (12196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12196)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (12196)Memory used [KB]: 6268
% 0.21/0.53  % (12196)Time elapsed: 0.114 s
% 0.21/0.53  % (12196)------------------------------
% 0.21/0.53  % (12196)------------------------------
% 0.21/0.53  % (12174)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (12169)Success in time 0.169 s
%------------------------------------------------------------------------------
