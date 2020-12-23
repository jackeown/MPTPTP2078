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
% DateTime   : Thu Dec  3 12:36:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  69 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 120 expanded)
%              Number of equality atoms :   36 (  59 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f51,f54,f63,f67])).

fof(f67,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f28,f62])).

fof(f62,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_5
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f28,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f63,plain,
    ( ~ spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f56,f48,f60])).

fof(f48,plain,
    ( spl2_4
  <=> k1_xboole_0 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f56,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_4 ),
    inference(superposition,[],[f29,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f29,plain,(
    ! [X1] : ~ r1_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f22,f15,f15])).

fof(f15,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f54,plain,
    ( spl2_1
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl2_1
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f33,f46,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f19,f15,f15])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f46,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_3
  <=> r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f33,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f51,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f40,f36,f48,f44])).

fof(f36,plain,
    ( spl2_2
  <=> k1_xboole_0 = k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f40,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))
    | ~ spl2_2 ),
    inference(superposition,[],[f38,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f18])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f38,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f39,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f23,f36])).

fof(f23,plain,(
    k1_xboole_0 = k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) ),
    inference(definition_unfolding,[],[f13,f18,f15,f15])).

fof(f13,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f34,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:07:38 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (26452)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (26467)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (26463)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (26451)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (26467)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f34,f39,f51,f54,f63,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl2_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    $false | spl2_5),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f28,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl2_5 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(equality_resolution,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ~spl2_5 | ~spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f56,f48,f60])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    spl2_4 <=> k1_xboole_0 = k2_tarski(sK0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_4),
% 0.21/0.51    inference(superposition,[],[f29,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f48])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) | X0 != X1) )),
% 0.21/0.51    inference(definition_unfolding,[],[f22,f15,f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl2_1 | spl2_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    $false | (spl2_1 | spl2_3)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f33,f46,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) | X0 = X1) )),
% 0.21/0.51    inference(definition_unfolding,[],[f19,f15,f15])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X0,X1] : (X0 = X1 | r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ~r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) | spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    spl2_3 <=> r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    sK0 != sK1 | spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    spl2_1 <=> sK0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ~spl2_3 | spl2_4 | ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f36,f48,f44])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    spl2_2 <=> k1_xboole_0 = k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    k1_xboole_0 = k2_tarski(sK0,sK0) | ~r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) | ~spl2_2),
% 0.21/0.51    inference(superposition,[],[f38,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f21,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    k1_xboole_0 = k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f36])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f23,f36])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    k1_xboole_0 = k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)))),
% 0.21/0.51    inference(definition_unfolding,[],[f13,f18,f15,f15])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ~spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f14,f31])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    sK0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (26467)------------------------------
% 0.21/0.51  % (26467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26467)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (26467)Memory used [KB]: 10618
% 0.21/0.51  % (26467)Time elapsed: 0.060 s
% 0.21/0.51  % (26467)------------------------------
% 0.21/0.51  % (26467)------------------------------
% 1.19/0.52  % (26444)Success in time 0.151 s
%------------------------------------------------------------------------------
