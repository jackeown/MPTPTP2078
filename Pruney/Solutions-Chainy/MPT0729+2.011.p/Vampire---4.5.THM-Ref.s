%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 195 expanded)
%              Number of leaves         :   15 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 271 expanded)
%              Number of equality atoms :   38 ( 172 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f106,f123,f143,f148])).

fof(f148,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f18,f101])).

fof(f101,plain,
    ( sK0 = sK1
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

fof(f143,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f66,f66,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f66,plain,
    ( r2_hidden(sK1,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl2_1
  <=> r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f123,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f45,f105,f18,f49,f60])).

fof(f60,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k2_xboole_0(X3,k2_enumset1(X4,X4,X4,X4)))
      | X4 = X5
      | r2_hidden(X5,X3)
      | r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)),k2_enumset1(X0,X0,X0,X0)) = X1
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f34,f34])).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f49,plain,(
    r2_hidden(sK1,k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f37,f36])).

fof(f36,plain,(
    k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f17,f35,f35])).

fof(f35,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f21,f34])).

fof(f21,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f17,plain,(
    k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f19,f35])).

% (8463)Refutation not found, incomplete strategy% (8463)------------------------------
% (8463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8463)Termination reason: Refutation not found, incomplete strategy

% (8463)Memory used [KB]: 10618
% (8463)Time elapsed: 0.107 s
% (8463)------------------------------
% (8463)------------------------------
fof(f19,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

% (8472)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f105,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_4
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f45,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(resolution,[],[f28,f42])).

fof(f42,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f106,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f95,f68,f103,f99])).

fof(f68,plain,
    ( spl2_2
  <=> sK1 = k4_xboole_0(k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f95,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = sK1
    | ~ spl2_2 ),
    inference(resolution,[],[f72,f37])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)))
        | ~ r2_hidden(sK1,X0)
        | sK1 = X0 )
    | ~ spl2_2 ),
    inference(superposition,[],[f53,f70])).

fof(f70,plain,
    ( sK1 = k4_xboole_0(k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f53,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(k4_xboole_0(X7,k2_enumset1(X6,X6,X6,X6)),X5)
      | ~ r2_hidden(X5,X7)
      | X5 = X6 ) ),
    inference(resolution,[],[f39,f24])).

fof(f71,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f58,f68,f64])).

fof(f58,plain,
    ( sK1 = k4_xboole_0(k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,sK1) ),
    inference(superposition,[],[f38,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (8452)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (8464)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (8452)Refutation not found, incomplete strategy% (8452)------------------------------
% 0.20/0.50  % (8452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8452)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (8452)Memory used [KB]: 1663
% 0.20/0.50  % (8452)Time elapsed: 0.096 s
% 0.20/0.50  % (8452)------------------------------
% 0.20/0.50  % (8452)------------------------------
% 0.20/0.50  % (8459)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (8475)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.51  % (8480)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (8453)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (8455)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (8464)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (8463)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f71,f106,f123,f143,f148])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    ~spl2_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f144])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    $false | ~spl2_3),
% 0.20/0.52    inference(subsumption_resolution,[],[f18,f101])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    sK0 = sK1 | ~spl2_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f99])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    spl2_3 <=> sK0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    sK0 != sK1),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 0.20/0.52    inference(negated_conjecture,[],[f11])).
% 0.20/0.52  fof(f11,conjecture,(
% 0.20/0.52    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    ~spl2_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f136])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    $false | ~spl2_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f66,f66,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    r2_hidden(sK1,sK1) | ~spl2_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    spl2_1 <=> r2_hidden(sK1,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    spl2_4),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f115])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    $false | spl2_4),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f45,f105,f18,f49,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X4,X5,X3] : (~r2_hidden(X5,k2_xboole_0(X3,k2_enumset1(X4,X4,X4,X4))) | X4 = X5 | r2_hidden(X5,X3) | r2_hidden(X4,X3)) )),
% 0.20/0.52    inference(superposition,[],[f39,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)),k2_enumset1(X0,X0,X0,X0)) = X1 | r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f23,f34,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f20,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f22,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 | r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f34])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    r2_hidden(sK1,k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.52    inference(superposition,[],[f37,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.52    inference(definition_unfolding,[],[f17,f35,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f21,f34])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f19,f35])).
% 0.20/0.52  % (8463)Refutation not found, incomplete strategy% (8463)------------------------------
% 0.20/0.52  % (8463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8463)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8463)Memory used [KB]: 10618
% 0.20/0.52  % (8463)Time elapsed: 0.107 s
% 0.20/0.52  % (8463)------------------------------
% 0.20/0.52  % (8463)------------------------------
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.20/0.52  % (8472)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    ~r2_hidden(sK1,sK0) | spl2_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f103])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    spl2_4 <=> r2_hidden(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 0.20/0.52    inference(resolution,[],[f28,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    spl2_3 | ~spl2_4 | ~spl2_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f95,f68,f103,f99])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    spl2_2 <=> sK1 = k4_xboole_0(k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ~r2_hidden(sK1,sK0) | sK0 = sK1 | ~spl2_2),
% 0.20/0.52    inference(resolution,[],[f72,f37])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0))) | ~r2_hidden(sK1,X0) | sK1 = X0) ) | ~spl2_2),
% 0.20/0.52    inference(superposition,[],[f53,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    sK1 = k4_xboole_0(k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl2_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f68])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X6,X7,X5] : (~r2_hidden(k4_xboole_0(X7,k2_enumset1(X6,X6,X6,X6)),X5) | ~r2_hidden(X5,X7) | X5 = X6) )),
% 0.20/0.52    inference(resolution,[],[f39,f24])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    spl2_1 | spl2_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f58,f68,f64])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    sK1 = k4_xboole_0(k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(sK1,sK1)),
% 0.20/0.52    inference(superposition,[],[f38,f36])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (8464)------------------------------
% 0.20/0.52  % (8464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8464)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (8464)Memory used [KB]: 6268
% 0.20/0.52  % (8464)Time elapsed: 0.109 s
% 0.20/0.52  % (8464)------------------------------
% 0.20/0.52  % (8464)------------------------------
% 0.20/0.52  % (8450)Success in time 0.163 s
%------------------------------------------------------------------------------
