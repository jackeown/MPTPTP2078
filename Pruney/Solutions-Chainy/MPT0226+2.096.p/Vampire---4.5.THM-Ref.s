%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  29 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  49 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f31])).

fof(f31,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f29])).

fof(f29,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f9,f18])).

fof(f18,plain,
    ( sK0 = sK1
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f9,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f28,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f24])).

fof(f24,plain,
    ( $false
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f10,f22])).

fof(f22,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_xboole_0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl2_2
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f10,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f23,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f14,f20,f16])).

fof(f14,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_xboole_0)
    | sK0 = sK1 ),
    inference(superposition,[],[f13,f8])).

fof(f8,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f12,f11])).

fof(f11,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:21:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (29989)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.46  % (29989)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f23,f28,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ~spl2_1),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    $false | ~spl2_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f9,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    sK0 = sK1 | ~spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    spl2_1 <=> sK0 = sK1),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    sK0 != sK1),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.46    inference(negated_conjecture,[],[f4])).
% 0.21/0.46  fof(f4,conjecture,(
% 0.21/0.46    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    spl2_2),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    $false | spl2_2),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f10,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_xboole_0) | spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    spl2_2 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    spl2_1 | ~spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f14,f20,f16])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_xboole_0) | sK0 = sK1),
% 0.21/0.46    inference(superposition,[],[f13,f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) | X0 = X1) )),
% 0.21/0.46    inference(definition_unfolding,[],[f12,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ! [X0,X1] : (X0 = X1 | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (29989)------------------------------
% 0.21/0.46  % (29989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (29989)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (29989)Memory used [KB]: 6140
% 0.21/0.46  % (29989)Time elapsed: 0.054 s
% 0.21/0.46  % (29989)------------------------------
% 0.21/0.46  % (29989)------------------------------
% 0.21/0.46  % (29975)Success in time 0.109 s
%------------------------------------------------------------------------------
