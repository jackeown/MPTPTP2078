%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 109 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  106 ( 157 expanded)
%              Number of equality atoms :   33 (  76 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f121,f154,f161,f167])).

fof(f167,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f22,f64])).

fof(f64,plain,
    ( ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_1
  <=> ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f22,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f161,plain,
    ( ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f52,f153,f69])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_2 ),
    inference(superposition,[],[f67,f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f67,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_2
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f153,plain,
    ( v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl5_6
  <=> v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f52,plain,(
    ! [X0,X3] : r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X3)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k3_enumset1(X0,X0,X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f154,plain,
    ( spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f144,f110,f151])).

% (22647)Termination reason: Refutation not found, incomplete strategy
fof(f110,plain,
    ( spl5_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f144,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f44,f117])).

% (22647)Memory used [KB]: 1663
fof(f117,plain,(
    k1_xboole_0 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    inference(forward_demodulation,[],[f42,f43])).

% (22647)Time elapsed: 0.003 s
% (22647)------------------------------
% (22647)------------------------------
% (22635)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (22619)Termination reason: Refutation not found, incomplete strategy

% (22619)Memory used [KB]: 1663
% (22619)Time elapsed: 0.106 s
% (22619)------------------------------
% (22619)------------------------------
fof(f43,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f25,f40,f40])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f42,plain,(
    k1_xboole_0 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f20,f41,f40])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f40])).

fof(f27,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f20,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f30,f41])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

fof(f121,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f21,f112])).

fof(f112,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f21,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f68,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f60,f66,f63])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f28,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:55:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (22631)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (22639)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (22621)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (22647)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (22619)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (22642)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (22622)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (22631)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (22619)Refutation not found, incomplete strategy% (22619)------------------------------
% 0.21/0.52  % (22619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22647)Refutation not found, incomplete strategy% (22647)------------------------------
% 0.21/0.52  % (22647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f68,f121,f154,f161,f167])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ~spl5_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f162])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    $false | ~spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f22,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl5_1 <=> ! [X0] : ~r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ~spl5_2 | ~spl5_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    $false | (~spl5_2 | ~spl5_6)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f52,f153,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) ) | ~spl5_2),
% 0.21/0.52    inference(superposition,[],[f67,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl5_2 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    spl5_6 <=> v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X3] : (r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X3))) )),
% 0.21/0.52    inference(equality_resolution,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k3_enumset1(X0,X0,X0,X0,X3) != X2) )),
% 0.21/0.52    inference(equality_resolution,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 0.21/0.52    inference(definition_unfolding,[],[f37,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f31,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    spl5_6 | ~spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f144,f110,f151])).
% 0.21/0.52  % (22647)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl5_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.21/0.52    inference(superposition,[],[f44,f117])).
% 0.21/0.52  % (22647)Memory used [KB]: 1663
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    k1_xboole_0 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 0.21/0.52    inference(forward_demodulation,[],[f42,f43])).
% 0.21/0.52  % (22647)Time elapsed: 0.003 s
% 0.21/0.52  % (22647)------------------------------
% 0.21/0.52  % (22647)------------------------------
% 0.21/0.52  % (22635)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (22619)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22619)Memory used [KB]: 1663
% 0.21/0.52  % (22619)Time elapsed: 0.106 s
% 0.21/0.52  % (22619)------------------------------
% 0.21/0.52  % (22619)------------------------------
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f25,f40,f40])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    k1_xboole_0 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f41,f40])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f27,f40])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.52    inference(negated_conjecture,[],[f13])).
% 0.21/0.52  fof(f13,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f30,f41])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_xboole_0(k2_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (~v1_xboole_0(X0) => ~v1_xboole_0(k2_xboole_0(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl5_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    $false | spl5_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f21,f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_xboole_0) | spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f110])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl5_1 | spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f60,f66,f63])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f28,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (22631)------------------------------
% 0.21/0.52  % (22631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22631)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (22631)Memory used [KB]: 6268
% 0.21/0.52  % (22631)Time elapsed: 0.098 s
% 0.21/0.52  % (22631)------------------------------
% 0.21/0.52  % (22631)------------------------------
% 0.21/0.53  % (22617)Success in time 0.161 s
%------------------------------------------------------------------------------
