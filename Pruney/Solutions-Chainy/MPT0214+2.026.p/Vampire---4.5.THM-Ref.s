%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 114 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 185 expanded)
%              Number of equality atoms :   59 ( 121 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f156,f174,f196])).

fof(f196,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f190])).

% (14053)Refutation not found, incomplete strategy% (14053)------------------------------
% (14053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14053)Termination reason: Refutation not found, incomplete strategy

fof(f190,plain,
    ( $false
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f18,f18,f18,f183,f74])).

% (14053)Memory used [KB]: 1663
% (14053)Time elapsed: 0.112 s
% (14053)------------------------------
% (14053)------------------------------
fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f40,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f183,plain,
    ( r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f65,f155])).

fof(f155,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl4_4
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f65,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_enumset1(X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f24,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f31])).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f174,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f85,f164])).

fof(f164,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl4_3 ),
    inference(superposition,[],[f65,f151])).

fof(f151,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl4_3
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f85,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r2_hidden(X2,k1_xboole_0)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f33,f75])).

fof(f75,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f47,f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f156,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f145,f153,f149])).

fof(f145,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f54,f46])).

fof(f46,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f17,f45,f45])).

fof(f17,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f45,f45])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (14052)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (14067)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (14064)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (14058)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (14059)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (14057)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (14065)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (14053)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (14065)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f156,f174,f196])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    ~spl4_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.52  % (14053)Refutation not found, incomplete strategy% (14053)------------------------------
% 0.21/0.52  % (14053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14053)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    $false | ~spl4_4),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f18,f18,f18,f183,f74])).
% 0.21/0.52  % (14053)Memory used [KB]: 1663
% 0.21/0.52  % (14053)Time elapsed: 0.112 s
% 0.21/0.52  % (14053)------------------------------
% 0.21/0.52  % (14053)------------------------------
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.21/0.52    inference(equality_resolution,[],[f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.21/0.52    inference(definition_unfolding,[],[f40,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_4),
% 0.21/0.52    inference(superposition,[],[f65,f155])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f153])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl4_4 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 0.21/0.52    inference(equality_resolution,[],[f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X2) != X1) )),
% 0.21/0.52    inference(equality_resolution,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.52    inference(definition_unfolding,[],[f24,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f22,f31])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    sK0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    ~spl4_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    $false | ~spl4_3),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f164])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    r2_hidden(sK0,k1_xboole_0) | ~spl4_3),
% 0.21/0.52    inference(superposition,[],[f65,f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    spl4_3 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f33,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f47,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.52    inference(rectify,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f19,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    spl4_3 | spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f145,f153,f149])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.52    inference(resolution,[],[f54,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(definition_unfolding,[],[f17,f45,f45])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f28,f45,f45])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (14065)------------------------------
% 0.21/0.52  % (14065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14065)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (14065)Memory used [KB]: 6268
% 0.21/0.52  % (14065)Time elapsed: 0.118 s
% 0.21/0.52  % (14065)------------------------------
% 0.21/0.52  % (14065)------------------------------
% 0.21/0.52  % (14051)Success in time 0.167 s
%------------------------------------------------------------------------------
