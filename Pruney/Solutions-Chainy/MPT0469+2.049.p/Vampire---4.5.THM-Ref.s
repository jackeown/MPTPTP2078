%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  55 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 (  95 expanded)
%              Number of equality atoms :   24 (  40 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f50,f65])).

fof(f65,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f24,f53,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f53,plain,
    ( r2_hidden(k4_tarski(sK3(k1_relat_1(o_0_0_xboole_0)),sK5(o_0_0_xboole_0,sK3(k1_relat_1(o_0_0_xboole_0)))),o_0_0_xboole_0)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f29])).

fof(f29,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f52,plain,
    ( r2_hidden(sK3(k1_relat_1(o_0_0_xboole_0)),k1_relat_1(o_0_0_xboole_0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f38,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f16,f21])).

fof(f21,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f38,plain,
    ( o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl8_2
  <=> o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f24,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f50,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f24,f41,f23])).

fof(f41,plain,
    ( r2_hidden(k4_tarski(sK1(o_0_0_xboole_0,sK3(k2_relat_1(o_0_0_xboole_0))),sK3(k2_relat_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f40,f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK1(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f40,plain,
    ( r2_hidden(sK3(k2_relat_1(o_0_0_xboole_0)),k2_relat_1(o_0_0_xboole_0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f34,f26])).

fof(f34,plain,
    ( o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl8_1
  <=> o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f39,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f25,f36,f32])).

fof(f25,plain,
    ( o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f11,f21,f21,f21,f21])).

fof(f11,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:29:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (4299)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (4299)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (4296)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (4297)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (4308)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (4300)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (4324)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f39,f50,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl8_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    $false | spl8_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f24,f53,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK3(k1_relat_1(o_0_0_xboole_0)),sK5(o_0_0_xboole_0,sK3(k1_relat_1(o_0_0_xboole_0)))),o_0_0_xboole_0) | spl8_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f52,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    r2_hidden(sK3(k1_relat_1(o_0_0_xboole_0)),k1_relat_1(o_0_0_xboole_0)) | spl8_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f38,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | o_0_0_xboole_0 = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f16,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    k1_xboole_0 = o_0_0_xboole_0),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    k1_xboole_0 = o_0_0_xboole_0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0) | spl8_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    spl8_2 <=> o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    v1_xboole_0(o_0_0_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    v1_xboole_0(o_0_0_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    spl8_1),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    $false | spl8_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f24,f41,f23])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK1(o_0_0_xboole_0,sK3(k2_relat_1(o_0_0_xboole_0))),sK3(k2_relat_1(o_0_0_xboole_0))),o_0_0_xboole_0) | spl8_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f40,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK1(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    r2_hidden(sK3(k2_relat_1(o_0_0_xboole_0)),k2_relat_1(o_0_0_xboole_0)) | spl8_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f34,f26])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0) | spl8_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    spl8_1 <=> o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ~spl8_1 | ~spl8_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f25,f36,f32])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0) | o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0)),
% 0.22/0.53    inference(definition_unfolding,[],[f11,f21,f21,f21,f21])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,negated_conjecture,(
% 0.22/0.53    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.22/0.53    inference(negated_conjecture,[],[f7])).
% 0.22/0.53  fof(f7,conjecture,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (4299)------------------------------
% 0.22/0.53  % (4299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4299)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (4299)Memory used [KB]: 6268
% 0.22/0.53  % (4299)Time elapsed: 0.109 s
% 0.22/0.53  % (4299)------------------------------
% 0.22/0.53  % (4299)------------------------------
% 0.22/0.53  % (4298)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (4294)Success in time 0.167 s
%------------------------------------------------------------------------------
