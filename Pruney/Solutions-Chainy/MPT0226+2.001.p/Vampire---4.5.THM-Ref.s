%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 211 expanded)
%              Number of leaves         :   15 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 266 expanded)
%              Number of equality atoms :   58 ( 209 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f180,f230])).

fof(f230,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f223,f29])).

fof(f29,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f223,plain,
    ( sK0 = sK1
    | ~ spl4_2 ),
    inference(resolution,[],[f159,f116])).

fof(f116,plain,
    ( r2_hidden(sK0,k1_enumset1(sK0,sK0,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_2
  <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f159,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,k1_enumset1(sK0,sK0,sK1))
      | sK1 = X9 ) ),
    inference(superposition,[],[f73,f99])).

fof(f99,plain,(
    k1_enumset1(sK1,sK1,sK1) = k1_enumset1(sK0,sK0,sK1) ),
    inference(superposition,[],[f85,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f85,plain,(
    k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f76,f72])).

fof(f72,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f55,f54,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f76,plain,(
    k1_enumset1(sK1,sK1,sK0) = k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) ),
    inference(superposition,[],[f71,f61])).

fof(f61,plain,(
    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f28,f33,f57,f57])).

% (16986)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (16986)Refutation not found, incomplete strategy% (16986)------------------------------
% (16986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16986)Termination reason: Refutation not found, incomplete strategy

% (16986)Memory used [KB]: 1663
% (16986)Time elapsed: 0.139 s
% (16986)------------------------------
% (16986)------------------------------
% (16981)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (16978)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (16982)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (16967)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (16976)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (16980)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% (16973)Refutation not found, incomplete strategy% (16973)------------------------------
% (16973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16973)Termination reason: Refutation not found, incomplete strategy

% (16973)Memory used [KB]: 10618
% (16973)Time elapsed: 0.152 s
% (16973)------------------------------
% (16973)------------------------------
fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f54])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X2),k3_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X3),k3_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f35,f56,f57])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_enumset1(X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f57])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f180,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f177,f131])).

fof(f131,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | spl4_2 ),
    inference(superposition,[],[f75,f122])).

fof(f122,plain,
    ( k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | spl4_2 ),
    inference(forward_demodulation,[],[f121,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f121,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | spl4_2 ),
    inference(forward_demodulation,[],[f120,f68])).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X0) = k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f57,f57,f54])).

fof(f41,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f120,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK1)))
    | spl4_2 ),
    inference(resolution,[],[f117,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_enumset1(X0,X0,X0) = k5_xboole_0(k1_enumset1(X0,X0,X0),k3_xboole_0(k1_enumset1(X0,X0,X0),X1)) ) ),
    inference(definition_unfolding,[],[f30,f57,f33,f57])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f117,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f75,plain,(
    ! [X2] : r2_hidden(X2,k1_enumset1(X2,X2,X2)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_enumset1(X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f37,f57])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f177,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | spl4_2 ),
    inference(resolution,[],[f107,f117])).

fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_enumset1(sK0,sK0,sK1))
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_enumset1(sK0,sK0,sK1))
      | r2_hidden(X0,k1_enumset1(sK0,sK0,sK1))
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f101,f99])).

fof(f101,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_enumset1(sK0,sK0,sK1))
      | r2_hidden(X0,k1_enumset1(sK1,sK1,sK1))
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f49,f85])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n005.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 09:35:02 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (16965)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.48  % (16958)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (16962)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (16961)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (16959)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (16964)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (16960)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (16977)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (16966)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (16979)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (16957)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (16969)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (16973)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (16971)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (16974)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (16975)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (16985)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (16970)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (16968)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (16983)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (16984)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (16963)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (16972)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (16984)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f180,f230])).
% 0.21/0.54  fof(f230,plain,(
% 0.21/0.54    ~spl4_2),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f229])).
% 0.21/0.54  fof(f229,plain,(
% 0.21/0.54    $false | ~spl4_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f223,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    sK0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.54    inference(negated_conjecture,[],[f23])).
% 0.21/0.54  fof(f23,conjecture,(
% 0.21/0.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    sK0 = sK1 | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f159,f116])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_enumset1(sK0,sK0,sK1)) | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f115])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    spl4_2 <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ( ! [X9] : (~r2_hidden(X9,k1_enumset1(sK0,sK0,sK1)) | sK1 = X9) )),
% 0.21/0.54    inference(superposition,[],[f73,f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    k1_enumset1(sK1,sK1,sK1) = k1_enumset1(sK0,sK0,sK1)),
% 0.21/0.54    inference(superposition,[],[f85,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK0,sK0,sK1)),
% 0.21/0.54    inference(forward_demodulation,[],[f76,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f55,f54,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    k1_enumset1(sK1,sK1,sK0) = k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f71,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))),
% 0.21/0.54    inference(definition_unfolding,[],[f28,f33,f57,f57])).
% 0.21/0.54  % (16986)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (16986)Refutation not found, incomplete strategy% (16986)------------------------------
% 0.21/0.54  % (16986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16986)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16986)Memory used [KB]: 1663
% 0.21/0.54  % (16986)Time elapsed: 0.139 s
% 0.21/0.54  % (16986)------------------------------
% 0.21/0.54  % (16986)------------------------------
% 0.21/0.55  % (16981)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (16978)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (16982)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (16967)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (16976)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (16980)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (16973)Refutation not found, incomplete strategy% (16973)------------------------------
% 0.21/0.55  % (16973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (16973)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (16973)Memory used [KB]: 10618
% 0.21/0.55  % (16973)Time elapsed: 0.152 s
% 0.21/0.55  % (16973)------------------------------
% 0.21/0.55  % (16973)------------------------------
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f42,f54])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,axiom,(
% 0.21/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X2),k3_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f53,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X3,X3),k3_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X0,X1,X2))))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f35,f56,f57])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f34,f33])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_enumset1(X0,X0,X0)) | X0 = X2) )),
% 0.21/0.56    inference(equality_resolution,[],[f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.21/0.56    inference(definition_unfolding,[],[f38,f57])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.56  fof(f180,plain,(
% 0.21/0.56    spl4_2),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f179])).
% 0.21/0.56  fof(f179,plain,(
% 0.21/0.56    $false | spl4_2),
% 0.21/0.56    inference(subsumption_resolution,[],[f177,f131])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    r2_hidden(sK0,k1_xboole_0) | spl4_2),
% 0.21/0.56    inference(superposition,[],[f75,f122])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | spl4_2),
% 0.21/0.56    inference(forward_demodulation,[],[f121,f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    k1_enumset1(sK0,sK0,sK0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | spl4_2),
% 0.21/0.56    inference(forward_demodulation,[],[f120,f68])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f41,f57,f57,f54])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    k1_enumset1(sK0,sK0,sK0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK1))) | spl4_2),
% 0.21/0.56    inference(resolution,[],[f117,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_enumset1(X0,X0,X0) = k5_xboole_0(k1_enumset1(X0,X0,X0),k3_xboole_0(k1_enumset1(X0,X0,X0),X1))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f30,f57,f33,f57])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK1)) | spl4_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f115])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X2] : (r2_hidden(X2,k1_enumset1(X2,X2,X2))) )),
% 0.21/0.56    inference(equality_resolution,[],[f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_enumset1(X2,X2,X2) != X1) )),
% 0.21/0.56    inference(equality_resolution,[],[f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.21/0.56    inference(definition_unfolding,[],[f37,f57])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f177,plain,(
% 0.21/0.56    ~r2_hidden(sK0,k1_xboole_0) | spl4_2),
% 0.21/0.56    inference(resolution,[],[f107,f117])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(X0,k1_enumset1(sK0,sK0,sK1)) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f106])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(X0,k1_enumset1(sK0,sK0,sK1)) | r2_hidden(X0,k1_enumset1(sK0,sK0,sK1)) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f101,f99])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(X0,k1_enumset1(sK0,sK0,sK1)) | r2_hidden(X0,k1_enumset1(sK1,sK1,sK1)) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(superposition,[],[f49,f85])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (16984)------------------------------
% 0.21/0.56  % (16984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (16984)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (16984)Memory used [KB]: 6396
% 0.21/0.56  % (16984)Time elapsed: 0.145 s
% 0.21/0.56  % (16984)------------------------------
% 0.21/0.56  % (16984)------------------------------
% 0.21/0.56  % (16956)Success in time 0.2 s
%------------------------------------------------------------------------------
