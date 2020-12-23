%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 169 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  141 ( 260 expanded)
%              Number of equality atoms :   65 ( 172 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f435,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f389,f396,f402,f409,f411,f432])).

fof(f432,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f58,f99])).

fof(f99,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_1
  <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f58,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f23,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f55])).

% (30634)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f411,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f410,f97,f101])).

fof(f101,plain,
    ( spl5_2
  <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f410,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(forward_demodulation,[],[f341,f151])).

fof(f151,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f145,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f145,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f57,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f341,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(superposition,[],[f206,f59])).

fof(f59,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f21,f56])).

fof(f21,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f206,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X1
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f184,f151])).

fof(f184,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X2,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f61,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f30,f30])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f409,plain,
    ( spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f292,f401])).

fof(f401,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl5_5
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f292,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl5_2 ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK1,sK0)
    | spl5_2 ),
    inference(resolution,[],[f66,f103])).

fof(f103,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f402,plain,
    ( spl5_3
    | spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f397,f386,f399,f382])).

fof(f382,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f386,plain,
    ( spl5_4
  <=> sK1 = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f397,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ spl5_4 ),
    inference(superposition,[],[f27,f388])).

fof(f388,plain,
    ( sK1 = sK2(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f386])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f396,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f22,f384])).

fof(f384,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f382])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f389,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f379,f386,f382])).

fof(f379,plain,
    ( sK1 = sK2(sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f378,f27])).

fof(f378,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f326,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f36,f56])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f326,plain,(
    ! [X15] :
      ( r2_hidden(X15,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X15,sK0) ) ),
    inference(forward_demodulation,[],[f315,f151])).

fof(f315,plain,(
    ! [X15] :
      ( ~ r2_hidden(X15,k4_xboole_0(sK0,k1_xboole_0))
      | r2_hidden(X15,k2_enumset1(sK1,sK1,sK1,sK1)) ) ),
    inference(superposition,[],[f198,f59])).

fof(f198,plain,(
    ! [X14,X12,X13] :
      ( ~ r2_hidden(X14,k4_xboole_0(X13,k4_xboole_0(X13,X12)))
      | r2_hidden(X14,X12) ) ),
    inference(superposition,[],[f76,f61])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n024.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 14:40:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.52  % (30635)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (30643)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (30643)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (30660)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (30660)Refutation not found, incomplete strategy% (30660)------------------------------
% 0.22/0.54  % (30660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f435,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f389,f396,f402,f409,f411,f432])).
% 0.22/0.54  fof(f432,plain,(
% 0.22/0.54    ~spl5_1),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f418])).
% 0.22/0.54  fof(f418,plain,(
% 0.22/0.54    $false | ~spl5_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f58,f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f97])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    spl5_1 <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.22/0.54    inference(definition_unfolding,[],[f23,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f26,f55])).
% 0.22/0.54  % (30634)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f29,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    sK0 != k1_tarski(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f16])).
% 0.22/0.54  fof(f16,conjecture,(
% 0.22/0.54    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.22/0.54  fof(f411,plain,(
% 0.22/0.54    ~spl5_2 | spl5_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f410,f97,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    spl5_2 <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.54  fof(f410,plain,(
% 0.22/0.54    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f341,f151])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(forward_demodulation,[],[f145,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(superposition,[],[f57,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f24,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f31,f30])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  fof(f341,plain,(
% 0.22/0.54    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.22/0.54    inference(superposition,[],[f206,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.54    inference(definition_unfolding,[],[f21,f56])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    ( ! [X2,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X1 | ~r1_tarski(X1,X2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f184,f151])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    ( ! [X2,X1] : (k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) | ~r1_tarski(X1,X2)) )),
% 0.22/0.54    inference(superposition,[],[f61,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f30,f30])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.54  fof(f409,plain,(
% 0.22/0.54    spl5_2 | ~spl5_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f403])).
% 0.22/0.54  fof(f403,plain,(
% 0.22/0.54    $false | (spl5_2 | ~spl5_5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f292,f401])).
% 0.22/0.54  fof(f401,plain,(
% 0.22/0.54    r2_hidden(sK1,sK0) | ~spl5_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f399])).
% 0.22/0.54  fof(f399,plain,(
% 0.22/0.54    spl5_5 <=> r2_hidden(sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.54  fof(f292,plain,(
% 0.22/0.54    ~r2_hidden(sK1,sK0) | spl5_2),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f285])).
% 0.22/0.54  fof(f285,plain,(
% 0.22/0.54    ~r2_hidden(sK1,sK0) | ~r2_hidden(sK1,sK0) | spl5_2),
% 0.22/0.54    inference(resolution,[],[f66,f103])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | spl5_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f101])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f50,f55])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.54  fof(f402,plain,(
% 0.22/0.54    spl5_3 | spl5_5 | ~spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f397,f386,f399,f382])).
% 0.22/0.54  fof(f382,plain,(
% 0.22/0.54    spl5_3 <=> k1_xboole_0 = sK0),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.54  fof(f386,plain,(
% 0.22/0.54    spl5_4 <=> sK1 = sK2(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.54  fof(f397,plain,(
% 0.22/0.54    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0 | ~spl5_4),
% 0.22/0.54    inference(superposition,[],[f27,f388])).
% 0.22/0.54  fof(f388,plain,(
% 0.22/0.54    sK1 = sK2(sK0) | ~spl5_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f386])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.54  fof(f396,plain,(
% 0.22/0.54    ~spl5_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f390])).
% 0.22/0.54  fof(f390,plain,(
% 0.22/0.54    $false | ~spl5_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f22,f384])).
% 0.22/0.54  fof(f384,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | ~spl5_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f382])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    k1_xboole_0 != sK0),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f389,plain,(
% 0.22/0.54    spl5_3 | spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f379,f386,f382])).
% 0.22/0.54  fof(f379,plain,(
% 0.22/0.54    sK1 = sK2(sK0) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(resolution,[],[f378,f27])).
% 0.22/0.54  fof(f378,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 = X0) )),
% 0.22/0.54    inference(resolution,[],[f326,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 0.22/0.54    inference(equality_resolution,[],[f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f36,f56])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.54  fof(f326,plain,(
% 0.22/0.54    ( ! [X15] : (r2_hidden(X15,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X15,sK0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f315,f151])).
% 0.22/0.54  fof(f315,plain,(
% 0.22/0.54    ( ! [X15] : (~r2_hidden(X15,k4_xboole_0(sK0,k1_xboole_0)) | r2_hidden(X15,k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 0.22/0.54    inference(superposition,[],[f198,f59])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    ( ! [X14,X12,X13] : (~r2_hidden(X14,k4_xboole_0(X13,k4_xboole_0(X13,X12))) | r2_hidden(X14,X12)) )),
% 0.22/0.54    inference(superposition,[],[f76,f61])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (30643)------------------------------
% 0.22/0.54  % (30643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30643)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (30643)Memory used [KB]: 6396
% 0.22/0.54  % (30643)Time elapsed: 0.109 s
% 0.22/0.54  % (30643)------------------------------
% 0.22/0.54  % (30643)------------------------------
% 0.22/0.54  % (30630)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (30660)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30660)Memory used [KB]: 1663
% 0.22/0.54  % (30660)Time elapsed: 0.125 s
% 0.22/0.54  % (30660)------------------------------
% 0.22/0.54  % (30660)------------------------------
% 0.22/0.54  % (30628)Success in time 0.172 s
%------------------------------------------------------------------------------
