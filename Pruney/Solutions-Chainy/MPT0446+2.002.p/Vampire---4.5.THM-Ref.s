%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:06 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   48 (  98 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 198 expanded)
%              Number of equality atoms :   17 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f316,f337])).

fof(f337,plain,(
    spl10_2 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f66,f158,f88,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f88,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl10_2
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f158,plain,(
    r1_tarski(k1_relat_1(sK2),k3_relat_1(sK2)) ),
    inference(superposition,[],[f55,f61])).

fof(f61,plain,(
    k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f29,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f31,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
         => ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f66,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f30,f58])).

fof(f58,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

% (26241)Refutation not found, incomplete strategy% (26241)------------------------------
% (26241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26241)Termination reason: Refutation not found, incomplete strategy

% (26244)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (26241)Memory used [KB]: 10746
% (26241)Time elapsed: 0.126 s
% (26241)------------------------------
% (26241)------------------------------
fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f30,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f316,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f84,f307])).

fof(f307,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(superposition,[],[f250,f61])).

fof(f250,plain,(
    ! [X0] : r2_hidden(sK1,k3_tarski(k1_enumset1(X0,X0,k2_relat_1(sK2)))) ),
    inference(superposition,[],[f72,f56])).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f50,f49,f49])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f72,plain,(
    ! [X0] : r2_hidden(sK1,k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0))) ),
    inference(unit_resulting_resolution,[],[f55,f65,f32])).

fof(f65,plain,(
    r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f30,f60])).

fof(f60,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f84,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl10_1
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f89,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f28,f86,f82])).

fof(f28,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:55:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (26243)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (26266)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.52  % (26252)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (26245)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (26240)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.53  % (26243)Refutation found. Thanks to Tanya!
% 1.29/0.53  % SZS status Theorem for theBenchmark
% 1.29/0.53  % (26251)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.53  % (26239)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.54  % (26241)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.54  % (26265)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.54  % SZS output start Proof for theBenchmark
% 1.29/0.54  fof(f338,plain,(
% 1.29/0.54    $false),
% 1.29/0.54    inference(avatar_sat_refutation,[],[f89,f316,f337])).
% 1.29/0.54  fof(f337,plain,(
% 1.29/0.54    spl10_2),
% 1.29/0.54    inference(avatar_contradiction_clause,[],[f330])).
% 1.29/0.54  fof(f330,plain,(
% 1.29/0.54    $false | spl10_2),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f66,f158,f88,f32])).
% 1.29/0.54  fof(f32,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f24])).
% 1.29/0.54  fof(f24,plain,(
% 1.29/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.29/0.54    inference(ennf_transformation,[],[f1])).
% 1.29/0.54  fof(f1,axiom,(
% 1.29/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.29/0.54  fof(f88,plain,(
% 1.29/0.54    ~r2_hidden(sK0,k3_relat_1(sK2)) | spl10_2),
% 1.29/0.54    inference(avatar_component_clause,[],[f86])).
% 1.29/0.54  fof(f86,plain,(
% 1.29/0.54    spl10_2 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.29/0.54  fof(f158,plain,(
% 1.29/0.54    r1_tarski(k1_relat_1(sK2),k3_relat_1(sK2))),
% 1.29/0.54    inference(superposition,[],[f55,f61])).
% 1.29/0.54  fof(f61,plain,(
% 1.29/0.54    k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f29,f54])).
% 1.29/0.54  fof(f54,plain,(
% 1.29/0.54    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.29/0.54    inference(definition_unfolding,[],[f31,f53])).
% 1.29/0.54  fof(f53,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.29/0.54    inference(definition_unfolding,[],[f44,f49])).
% 1.29/0.54  fof(f49,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f4])).
% 1.29/0.54  fof(f4,axiom,(
% 1.29/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.29/0.54  fof(f44,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f11])).
% 1.29/0.54  fof(f11,axiom,(
% 1.29/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.29/0.54  fof(f31,plain,(
% 1.29/0.54    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f23])).
% 1.29/0.54  fof(f23,plain,(
% 1.29/0.54    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.29/0.54    inference(ennf_transformation,[],[f18])).
% 1.29/0.54  fof(f18,axiom,(
% 1.29/0.54    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.29/0.54  fof(f29,plain,(
% 1.29/0.54    v1_relat_1(sK2)),
% 1.29/0.54    inference(cnf_transformation,[],[f22])).
% 1.29/0.54  fof(f22,plain,(
% 1.29/0.54    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2))),
% 1.29/0.54    inference(flattening,[],[f21])).
% 1.29/0.54  fof(f21,plain,(
% 1.29/0.54    ? [X0,X1,X2] : (((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 1.29/0.54    inference(ennf_transformation,[],[f20])).
% 1.29/0.54  fof(f20,negated_conjecture,(
% 1.29/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.29/0.54    inference(negated_conjecture,[],[f19])).
% 1.29/0.54  fof(f19,conjecture,(
% 1.29/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 1.29/0.54  fof(f55,plain,(
% 1.29/0.54    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 1.29/0.54    inference(definition_unfolding,[],[f45,f53])).
% 1.29/0.54  fof(f45,plain,(
% 1.29/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f2])).
% 1.29/0.54  fof(f2,axiom,(
% 1.29/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.29/0.54  fof(f66,plain,(
% 1.29/0.54    r2_hidden(sK0,k1_relat_1(sK2))),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f30,f58])).
% 1.29/0.54  fof(f58,plain,(
% 1.29/0.54    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 1.29/0.54    inference(equality_resolution,[],[f36])).
% 1.29/0.54  fof(f36,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.29/0.54    inference(cnf_transformation,[],[f16])).
% 1.29/0.54  % (26241)Refutation not found, incomplete strategy% (26241)------------------------------
% 1.29/0.54  % (26241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (26241)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (26244)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.54  % (26241)Memory used [KB]: 10746
% 1.29/0.54  % (26241)Time elapsed: 0.126 s
% 1.29/0.54  % (26241)------------------------------
% 1.29/0.54  % (26241)------------------------------
% 1.29/0.54  fof(f16,axiom,(
% 1.29/0.54    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.29/0.54  fof(f30,plain,(
% 1.29/0.54    r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.29/0.54    inference(cnf_transformation,[],[f22])).
% 1.29/0.54  fof(f316,plain,(
% 1.29/0.54    spl10_1),
% 1.29/0.54    inference(avatar_contradiction_clause,[],[f308])).
% 1.29/0.54  fof(f308,plain,(
% 1.29/0.54    $false | spl10_1),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f84,f307])).
% 1.29/0.54  fof(f307,plain,(
% 1.29/0.54    r2_hidden(sK1,k3_relat_1(sK2))),
% 1.29/0.54    inference(superposition,[],[f250,f61])).
% 1.29/0.54  fof(f250,plain,(
% 1.29/0.54    ( ! [X0] : (r2_hidden(sK1,k3_tarski(k1_enumset1(X0,X0,k2_relat_1(sK2))))) )),
% 1.29/0.54    inference(superposition,[],[f72,f56])).
% 1.29/0.54  fof(f56,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f50,f49,f49])).
% 1.29/0.54  fof(f50,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f3])).
% 1.29/0.54  fof(f3,axiom,(
% 1.29/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.29/0.54  fof(f72,plain,(
% 1.29/0.54    ( ! [X0] : (r2_hidden(sK1,k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))) )),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f55,f65,f32])).
% 1.29/0.54  fof(f65,plain,(
% 1.29/0.54    r2_hidden(sK1,k2_relat_1(sK2))),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f30,f60])).
% 1.29/0.54  fof(f60,plain,(
% 1.29/0.54    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 1.29/0.54    inference(equality_resolution,[],[f40])).
% 1.29/0.54  fof(f40,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.29/0.54    inference(cnf_transformation,[],[f17])).
% 1.29/0.54  fof(f17,axiom,(
% 1.29/0.54    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.29/0.54  fof(f84,plain,(
% 1.29/0.54    ~r2_hidden(sK1,k3_relat_1(sK2)) | spl10_1),
% 1.29/0.54    inference(avatar_component_clause,[],[f82])).
% 1.29/0.54  fof(f82,plain,(
% 1.29/0.54    spl10_1 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.29/0.54  fof(f89,plain,(
% 1.29/0.54    ~spl10_1 | ~spl10_2),
% 1.29/0.54    inference(avatar_split_clause,[],[f28,f86,f82])).
% 1.29/0.54  fof(f28,plain,(
% 1.29/0.54    ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK1,k3_relat_1(sK2))),
% 1.29/0.54    inference(cnf_transformation,[],[f22])).
% 1.29/0.54  % SZS output end Proof for theBenchmark
% 1.29/0.54  % (26243)------------------------------
% 1.29/0.54  % (26243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (26243)Termination reason: Refutation
% 1.29/0.54  
% 1.29/0.54  % (26243)Memory used [KB]: 6396
% 1.29/0.54  % (26243)Time elapsed: 0.112 s
% 1.29/0.54  % (26243)------------------------------
% 1.29/0.54  % (26243)------------------------------
% 1.29/0.54  % (26238)Success in time 0.171 s
%------------------------------------------------------------------------------
