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
% DateTime   : Thu Dec  3 12:29:49 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   44 (  67 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 152 expanded)
%              Number of equality atoms :   15 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f43,f85,f114])).

fof(f114,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f26,f106,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f106,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_xboole_0)
    | ~ spl6_1
    | spl6_2 ),
    inference(forward_demodulation,[],[f104,f35])).

fof(f35,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl6_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f104,plain,
    ( r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1))
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f86,f87,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f87,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK1)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f38,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f38,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl6_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f86,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f38,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f85,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f39,f45,f46,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK1)),sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f44,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f23])).

% (30102)Termination reason: Refutation not found, incomplete strategy
fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f34,f25])).

% (30102)Memory used [KB]: 10746
fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

% (30102)Time elapsed: 0.119 s
% (30102)------------------------------
% (30102)------------------------------
fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f34,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f45,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK1)),sK0)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f44,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f39,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f43,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f14,f37,f33])).

fof(f14,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <~> r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
      <=> r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f40,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f13,f37,f33])).

fof(f13,plain,
    ( r1_tarski(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.19/0.53  % (30088)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.53  % (30089)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.53  % (30094)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.53  % (30096)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.53  % (30097)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.53  % (30102)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.54  % (30086)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.54  % (30102)Refutation not found, incomplete strategy% (30102)------------------------------
% 1.29/0.54  % (30102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (30086)Refutation found. Thanks to Tanya!
% 1.29/0.54  % SZS status Theorem for theBenchmark
% 1.29/0.54  % (30105)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.54  % SZS output start Proof for theBenchmark
% 1.29/0.54  fof(f115,plain,(
% 1.29/0.54    $false),
% 1.29/0.54    inference(avatar_sat_refutation,[],[f40,f43,f85,f114])).
% 1.29/0.54  fof(f114,plain,(
% 1.29/0.54    ~spl6_1 | spl6_2),
% 1.29/0.54    inference(avatar_contradiction_clause,[],[f108])).
% 1.29/0.54  fof(f108,plain,(
% 1.29/0.54    $false | (~spl6_1 | spl6_2)),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f26,f106,f28])).
% 1.29/0.54  fof(f28,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f1])).
% 1.29/0.54  fof(f1,axiom,(
% 1.29/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.29/0.54  fof(f106,plain,(
% 1.29/0.54    r2_hidden(sK2(sK0,sK1),k1_xboole_0) | (~spl6_1 | spl6_2)),
% 1.29/0.54    inference(forward_demodulation,[],[f104,f35])).
% 1.29/0.54  fof(f35,plain,(
% 1.29/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl6_1),
% 1.29/0.54    inference(avatar_component_clause,[],[f33])).
% 1.29/0.54  fof(f33,plain,(
% 1.29/0.54    spl6_1 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.29/0.54  fof(f104,plain,(
% 1.29/0.54    r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1)) | spl6_2),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f86,f87,f29])).
% 1.29/0.54  fof(f29,plain,(
% 1.29/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 1.29/0.54    inference(equality_resolution,[],[f24])).
% 1.29/0.54  fof(f24,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.29/0.54    inference(cnf_transformation,[],[f3])).
% 1.29/0.54  fof(f3,axiom,(
% 1.29/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.29/0.54  fof(f87,plain,(
% 1.29/0.54    ~r2_hidden(sK2(sK0,sK1),sK1) | spl6_2),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f38,f18])).
% 1.29/0.54  fof(f18,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f11])).
% 1.29/0.54  fof(f11,plain,(
% 1.29/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.29/0.54    inference(ennf_transformation,[],[f2])).
% 1.29/0.54  fof(f2,axiom,(
% 1.29/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.29/0.54  fof(f38,plain,(
% 1.29/0.54    ~r1_tarski(sK0,sK1) | spl6_2),
% 1.29/0.54    inference(avatar_component_clause,[],[f37])).
% 1.29/0.54  fof(f37,plain,(
% 1.29/0.54    spl6_2 <=> r1_tarski(sK0,sK1)),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.29/0.54  fof(f86,plain,(
% 1.29/0.54    r2_hidden(sK2(sK0,sK1),sK0) | spl6_2),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f38,f17])).
% 1.29/0.54  fof(f17,plain,(
% 1.29/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f11])).
% 1.29/0.54  fof(f26,plain,(
% 1.29/0.54    v1_xboole_0(k1_xboole_0)),
% 1.29/0.54    inference(cnf_transformation,[],[f4])).
% 1.29/0.54  fof(f4,axiom,(
% 1.29/0.54    v1_xboole_0(k1_xboole_0)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.29/0.54  fof(f85,plain,(
% 1.29/0.54    spl6_1 | ~spl6_2),
% 1.29/0.54    inference(avatar_contradiction_clause,[],[f84])).
% 1.29/0.54  fof(f84,plain,(
% 1.29/0.54    $false | (spl6_1 | ~spl6_2)),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f39,f45,f46,f16])).
% 1.29/0.54  fof(f16,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f11])).
% 1.29/0.54  fof(f46,plain,(
% 1.29/0.54    ~r2_hidden(sK4(k4_xboole_0(sK0,sK1)),sK1) | spl6_1),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f44,f30])).
% 1.29/0.54  fof(f30,plain,(
% 1.29/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.29/0.54    inference(equality_resolution,[],[f23])).
% 1.29/0.54  % (30102)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  fof(f23,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.29/0.54    inference(cnf_transformation,[],[f3])).
% 1.29/0.54  
% 1.29/0.54  fof(f44,plain,(
% 1.29/0.54    r2_hidden(sK4(k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl6_1),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f34,f25])).
% 1.29/0.54  % (30102)Memory used [KB]: 10746
% 1.29/0.54  fof(f25,plain,(
% 1.29/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.29/0.54    inference(cnf_transformation,[],[f12])).
% 1.29/0.54  % (30102)Time elapsed: 0.119 s
% 1.29/0.54  % (30102)------------------------------
% 1.29/0.54  % (30102)------------------------------
% 1.29/0.54  fof(f12,plain,(
% 1.29/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.29/0.54    inference(ennf_transformation,[],[f5])).
% 1.29/0.54  fof(f5,axiom,(
% 1.29/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.29/0.54  fof(f34,plain,(
% 1.29/0.54    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl6_1),
% 1.29/0.54    inference(avatar_component_clause,[],[f33])).
% 1.29/0.54  fof(f45,plain,(
% 1.29/0.54    r2_hidden(sK4(k4_xboole_0(sK0,sK1)),sK0) | spl6_1),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f44,f31])).
% 1.29/0.54  fof(f31,plain,(
% 1.29/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 1.29/0.54    inference(equality_resolution,[],[f22])).
% 1.29/0.54  fof(f22,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.29/0.54    inference(cnf_transformation,[],[f3])).
% 1.29/0.54  fof(f39,plain,(
% 1.29/0.54    r1_tarski(sK0,sK1) | ~spl6_2),
% 1.29/0.54    inference(avatar_component_clause,[],[f37])).
% 1.29/0.54  fof(f43,plain,(
% 1.29/0.54    ~spl6_1 | ~spl6_2),
% 1.29/0.54    inference(avatar_split_clause,[],[f14,f37,f33])).
% 1.29/0.54  fof(f14,plain,(
% 1.29/0.54    ~r1_tarski(sK0,sK1) | k1_xboole_0 != k4_xboole_0(sK0,sK1)),
% 1.29/0.54    inference(cnf_transformation,[],[f9])).
% 1.29/0.54  fof(f9,plain,(
% 1.29/0.54    ? [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <~> r1_tarski(X0,X1))),
% 1.29/0.54    inference(ennf_transformation,[],[f8])).
% 1.29/0.54  fof(f8,negated_conjecture,(
% 1.29/0.54    ~! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.29/0.54    inference(negated_conjecture,[],[f7])).
% 1.29/0.54  fof(f7,conjecture,(
% 1.29/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 1.29/0.54  fof(f40,plain,(
% 1.29/0.54    spl6_1 | spl6_2),
% 1.29/0.54    inference(avatar_split_clause,[],[f13,f37,f33])).
% 1.29/0.54  fof(f13,plain,(
% 1.29/0.54    r1_tarski(sK0,sK1) | k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.29/0.54    inference(cnf_transformation,[],[f9])).
% 1.29/0.54  % SZS output end Proof for theBenchmark
% 1.29/0.54  % (30086)------------------------------
% 1.29/0.54  % (30086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (30086)Termination reason: Refutation
% 1.29/0.54  
% 1.29/0.54  % (30086)Memory used [KB]: 6268
% 1.29/0.54  % (30086)Time elapsed: 0.123 s
% 1.29/0.54  % (30086)------------------------------
% 1.29/0.54  % (30086)------------------------------
% 1.29/0.55  % (30081)Success in time 0.181 s
%------------------------------------------------------------------------------
