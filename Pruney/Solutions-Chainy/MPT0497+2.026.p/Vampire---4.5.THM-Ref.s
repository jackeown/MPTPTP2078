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
% DateTime   : Thu Dec  3 12:48:27 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 106 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 213 expanded)
%              Number of equality atoms :   50 (  81 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f50,f51,f61,f70,f120,f136,f144,f146])).

fof(f146,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f144,plain,
    ( spl2_3
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f125,f111,f38,f47])).

fof(f47,plain,
    ( spl2_3
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f38,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f111,plain,
    ( spl2_10
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f125,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(superposition,[],[f109,f113])).

fof(f113,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f109,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,X0))
        | r1_xboole_0(k1_relat_1(sK1),X0) )
    | ~ spl2_1 ),
    inference(superposition,[],[f34,f100])).

fof(f100,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))
    | ~ spl2_1 ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f136,plain,
    ( spl2_2
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f135,f111,f38,f43])).

fof(f43,plain,
    ( spl2_2
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f135,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f134,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f134,plain,
    ( k7_relat_1(sK1,sK0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,sK0),k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f131,f36])).

fof(f36,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f131,plain,
    ( k7_relat_1(sK1,sK0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,sK0)))))
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(superposition,[],[f81,f113])).

fof(f81,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(k7_relat_1(sK1,X0)))))
    | ~ spl2_1 ),
    inference(resolution,[],[f31,f62])).

fof(f62,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_1 ),
    inference(resolution,[],[f23,f40])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_setfam_1(k2_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f120,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f107,f67,f38,f111])).

fof(f67,plain,
    ( spl2_6
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f107,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(superposition,[],[f69,f100])).

fof(f69,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f70,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f65,f47,f67])).

fof(f65,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f33,f48])).

fof(f48,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f26,f22])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f61,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f18,f58])).

fof(f58,plain,
    ( spl2_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f18,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f51,plain,
    ( spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f15,f47,f43])).

fof(f15,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f50,plain,
    ( ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f16,f47,f43])).

fof(f16,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.27/0.54  % (3877)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.27/0.54  % (3869)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.54  % (3884)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.27/0.54  % (3877)Refutation not found, incomplete strategy% (3877)------------------------------
% 1.27/0.54  % (3877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (3877)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (3877)Memory used [KB]: 10618
% 1.27/0.54  % (3877)Time elapsed: 0.076 s
% 1.27/0.54  % (3877)------------------------------
% 1.27/0.54  % (3877)------------------------------
% 1.39/0.55  % (3876)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.55  % (3860)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.39/0.55  % (3876)Refutation found. Thanks to Tanya!
% 1.39/0.55  % SZS status Theorem for theBenchmark
% 1.39/0.55  % SZS output start Proof for theBenchmark
% 1.39/0.55  fof(f147,plain,(
% 1.39/0.55    $false),
% 1.39/0.55    inference(avatar_sat_refutation,[],[f41,f50,f51,f61,f70,f120,f136,f144,f146])).
% 1.39/0.55  fof(f146,plain,(
% 1.39/0.55    k1_xboole_0 != k7_relat_1(sK1,sK0) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.39/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.39/0.55  fof(f144,plain,(
% 1.39/0.55    spl2_3 | ~spl2_1 | ~spl2_10),
% 1.39/0.55    inference(avatar_split_clause,[],[f125,f111,f38,f47])).
% 1.39/0.55  fof(f47,plain,(
% 1.39/0.55    spl2_3 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.39/0.55  fof(f38,plain,(
% 1.39/0.55    spl2_1 <=> v1_relat_1(sK1)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.39/0.55  fof(f111,plain,(
% 1.39/0.55    spl2_10 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.39/0.55  fof(f125,plain,(
% 1.39/0.55    r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_1 | ~spl2_10)),
% 1.39/0.55    inference(trivial_inequality_removal,[],[f122])).
% 1.39/0.55  fof(f122,plain,(
% 1.39/0.55    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_1 | ~spl2_10)),
% 1.39/0.55    inference(superposition,[],[f109,f113])).
% 1.39/0.55  fof(f113,plain,(
% 1.39/0.55    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_10),
% 1.39/0.55    inference(avatar_component_clause,[],[f111])).
% 1.39/0.55  fof(f109,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,X0)) | r1_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl2_1),
% 1.39/0.55    inference(superposition,[],[f34,f100])).
% 1.39/0.55  fof(f100,plain,(
% 1.39/0.55    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) ) | ~spl2_1),
% 1.39/0.55    inference(resolution,[],[f32,f40])).
% 1.39/0.55  fof(f40,plain,(
% 1.39/0.55    v1_relat_1(sK1) | ~spl2_1),
% 1.39/0.55    inference(avatar_component_clause,[],[f38])).
% 1.39/0.55  fof(f32,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 1.39/0.55    inference(definition_unfolding,[],[f24,f22])).
% 1.39/0.55  fof(f22,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f4])).
% 1.39/0.55  fof(f4,axiom,(
% 1.39/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.39/0.55  fof(f24,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f14])).
% 1.39/0.55  fof(f14,plain,(
% 1.39/0.55    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.39/0.55    inference(ennf_transformation,[],[f8])).
% 1.39/0.55  fof(f8,axiom,(
% 1.39/0.55    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.39/0.55  fof(f34,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.39/0.55    inference(definition_unfolding,[],[f25,f22])).
% 1.39/0.55  fof(f25,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f1])).
% 1.39/0.55  fof(f1,axiom,(
% 1.39/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.39/0.55  fof(f136,plain,(
% 1.39/0.55    spl2_2 | ~spl2_1 | ~spl2_10),
% 1.39/0.55    inference(avatar_split_clause,[],[f135,f111,f38,f43])).
% 1.39/0.55  fof(f43,plain,(
% 1.39/0.55    spl2_2 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.39/0.55  fof(f135,plain,(
% 1.39/0.55    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl2_1 | ~spl2_10)),
% 1.39/0.55    inference(forward_demodulation,[],[f134,f30])).
% 1.39/0.55  fof(f30,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.39/0.55    inference(definition_unfolding,[],[f20,f22])).
% 1.39/0.55  fof(f20,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.39/0.55  fof(f134,plain,(
% 1.39/0.55    k7_relat_1(sK1,sK0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,sK0),k1_xboole_0)) | (~spl2_1 | ~spl2_10)),
% 1.39/0.55    inference(forward_demodulation,[],[f131,f36])).
% 1.39/0.55  fof(f36,plain,(
% 1.39/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f28])).
% 1.39/0.55  fof(f28,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f3])).
% 1.39/0.55  fof(f3,axiom,(
% 1.39/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.55  fof(f131,plain,(
% 1.39/0.55    k7_relat_1(sK1,sK0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,sK0))))) | (~spl2_1 | ~spl2_10)),
% 1.39/0.55    inference(superposition,[],[f81,f113])).
% 1.39/0.55  fof(f81,plain,(
% 1.39/0.55    ( ! [X0] : (k7_relat_1(sK1,X0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(k7_relat_1(sK1,X0)))))) ) | ~spl2_1),
% 1.39/0.55    inference(resolution,[],[f31,f62])).
% 1.39/0.55  fof(f62,plain,(
% 1.39/0.55    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_1),
% 1.39/0.55    inference(resolution,[],[f23,f40])).
% 1.39/0.55  fof(f23,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f13])).
% 1.39/0.55  fof(f13,plain,(
% 1.39/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f5])).
% 1.39/0.55  fof(f5,axiom,(
% 1.39/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.39/0.55  fof(f31,plain,(
% 1.39/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_setfam_1(k2_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) )),
% 1.39/0.55    inference(definition_unfolding,[],[f21,f22])).
% 1.39/0.55  fof(f21,plain,(
% 1.39/0.55    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 1.39/0.55    inference(cnf_transformation,[],[f12])).
% 1.39/0.55  fof(f12,plain,(
% 1.39/0.55    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f6])).
% 1.39/0.55  fof(f6,axiom,(
% 1.39/0.55    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.39/0.55  fof(f120,plain,(
% 1.39/0.55    spl2_10 | ~spl2_1 | ~spl2_6),
% 1.39/0.55    inference(avatar_split_clause,[],[f107,f67,f38,f111])).
% 1.39/0.55  fof(f67,plain,(
% 1.39/0.55    spl2_6 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.39/0.55  fof(f107,plain,(
% 1.39/0.55    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_6)),
% 1.39/0.55    inference(superposition,[],[f69,f100])).
% 1.39/0.55  fof(f69,plain,(
% 1.39/0.55    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) | ~spl2_6),
% 1.39/0.55    inference(avatar_component_clause,[],[f67])).
% 1.39/0.55  fof(f70,plain,(
% 1.39/0.55    spl2_6 | ~spl2_3),
% 1.39/0.55    inference(avatar_split_clause,[],[f65,f47,f67])).
% 1.39/0.55  fof(f65,plain,(
% 1.39/0.55    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) | ~spl2_3),
% 1.39/0.55    inference(resolution,[],[f33,f48])).
% 1.39/0.55  fof(f48,plain,(
% 1.39/0.55    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_3),
% 1.39/0.55    inference(avatar_component_clause,[],[f47])).
% 1.39/0.55  fof(f33,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.39/0.55    inference(definition_unfolding,[],[f26,f22])).
% 1.39/0.55  fof(f26,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f1])).
% 1.39/0.55  fof(f61,plain,(
% 1.39/0.55    spl2_5),
% 1.39/0.55    inference(avatar_split_clause,[],[f18,f58])).
% 1.39/0.55  fof(f58,plain,(
% 1.39/0.55    spl2_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.39/0.55  fof(f18,plain,(
% 1.39/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(cnf_transformation,[],[f7])).
% 1.39/0.55  fof(f7,axiom,(
% 1.39/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.39/0.55  fof(f51,plain,(
% 1.39/0.55    spl2_2 | spl2_3),
% 1.39/0.55    inference(avatar_split_clause,[],[f15,f47,f43])).
% 1.39/0.55  fof(f15,plain,(
% 1.39/0.55    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.39/0.55    inference(cnf_transformation,[],[f11])).
% 1.39/0.55  fof(f11,plain,(
% 1.39/0.55    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.39/0.55    inference(ennf_transformation,[],[f10])).
% 1.39/0.55  fof(f10,negated_conjecture,(
% 1.39/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.39/0.55    inference(negated_conjecture,[],[f9])).
% 1.39/0.55  fof(f9,conjecture,(
% 1.39/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 1.39/0.55  fof(f50,plain,(
% 1.39/0.55    ~spl2_2 | ~spl2_3),
% 1.39/0.55    inference(avatar_split_clause,[],[f16,f47,f43])).
% 1.39/0.55  fof(f16,plain,(
% 1.39/0.55    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 1.39/0.55    inference(cnf_transformation,[],[f11])).
% 1.39/0.55  fof(f41,plain,(
% 1.39/0.55    spl2_1),
% 1.39/0.55    inference(avatar_split_clause,[],[f17,f38])).
% 1.39/0.55  fof(f17,plain,(
% 1.39/0.55    v1_relat_1(sK1)),
% 1.39/0.55    inference(cnf_transformation,[],[f11])).
% 1.39/0.55  % SZS output end Proof for theBenchmark
% 1.39/0.55  % (3876)------------------------------
% 1.39/0.55  % (3876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (3876)Termination reason: Refutation
% 1.39/0.55  
% 1.39/0.55  % (3876)Memory used [KB]: 10746
% 1.39/0.55  % (3876)Time elapsed: 0.126 s
% 1.39/0.55  % (3876)------------------------------
% 1.39/0.55  % (3876)------------------------------
% 1.39/0.55  % (3859)Success in time 0.187 s
%------------------------------------------------------------------------------
