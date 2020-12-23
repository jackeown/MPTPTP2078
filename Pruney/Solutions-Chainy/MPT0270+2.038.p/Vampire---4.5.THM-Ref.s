%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:01 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 269 expanded)
%              Number of leaves         :   16 (  92 expanded)
%              Depth                    :   11
%              Number of atoms          :  127 ( 403 expanded)
%              Number of equality atoms :   55 ( 222 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f341,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f68,f133,f301,f309,f329])).

fof(f329,plain,
    ( spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f328,f60,f130])).

fof(f130,plain,
    ( spl4_4
  <=> sK1 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f60,plain,
    ( spl4_1
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f328,plain,
    ( sK1 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f327,f135])).

fof(f135,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f81,f115])).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f94,f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f94,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k4_xboole_0(X0,X0)) ),
    inference(global_subsumption,[],[f74,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k4_xboole_0(X0,X0)) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k4_xboole_0(X0,X0)) ) ),
    inference(superposition,[],[f37,f81])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(X0,X0))
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f58,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f33,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f81,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f44,f20])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f327,plain,
    ( k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f321,f115])).

fof(f321,plain,
    ( k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl4_1 ),
    inference(superposition,[],[f97,f61])).

fof(f61,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f97,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f44,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f25,f25])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f309,plain,
    ( ~ spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f306,f64,f130])).

fof(f64,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f306,plain,
    ( sK1 != k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f66,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f66,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f301,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f300,f130,f60])).

fof(f300,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f299,f135])).

fof(f299,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f288,f115])).

fof(f288,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,sK1))
    | ~ spl4_4 ),
    inference(superposition,[],[f97,f132])).

fof(f132,plain,
    ( sK1 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f133,plain,
    ( spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f117,f64,f130])).

fof(f117,plain,
    ( sK1 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_2 ),
    inference(resolution,[],[f49,f65])).

fof(f65,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f27,f43])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f46,f64,f60])).

fof(f46,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f18,f43,f43])).

fof(f18,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f67,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f45,f64,f60])).

fof(f45,plain,
    ( r2_hidden(sK0,sK1)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f19,f43,f43])).

fof(f19,plain,
    ( r2_hidden(sK0,sK1)
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:42:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (11069)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (11074)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (11062)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (11090)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (11067)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (11062)Refutation not found, incomplete strategy% (11062)------------------------------
% 0.21/0.51  % (11062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11062)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11062)Memory used [KB]: 1663
% 0.21/0.51  % (11062)Time elapsed: 0.102 s
% 0.21/0.51  % (11062)------------------------------
% 0.21/0.51  % (11062)------------------------------
% 0.21/0.51  % (11071)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (11070)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (11071)Refutation not found, incomplete strategy% (11071)------------------------------
% 0.21/0.52  % (11071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11071)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11071)Memory used [KB]: 10618
% 0.21/0.52  % (11071)Time elapsed: 0.117 s
% 0.21/0.52  % (11071)------------------------------
% 0.21/0.52  % (11071)------------------------------
% 0.21/0.52  % (11063)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (11077)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (11077)Refutation not found, incomplete strategy% (11077)------------------------------
% 0.21/0.52  % (11077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11077)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11077)Memory used [KB]: 6140
% 0.21/0.52  % (11077)Time elapsed: 0.002 s
% 0.21/0.52  % (11077)------------------------------
% 0.21/0.52  % (11077)------------------------------
% 0.21/0.52  % (11066)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (11068)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (11073)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (11082)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (11084)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (11081)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (11084)Refutation not found, incomplete strategy% (11084)------------------------------
% 0.21/0.53  % (11084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11084)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11084)Memory used [KB]: 10618
% 0.21/0.53  % (11084)Time elapsed: 0.093 s
% 0.21/0.53  % (11084)------------------------------
% 0.21/0.53  % (11084)------------------------------
% 0.21/0.53  % (11091)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (11065)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (11064)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (11076)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (11089)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (11088)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (11083)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (11083)Refutation not found, incomplete strategy% (11083)------------------------------
% 0.21/0.54  % (11083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11083)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11083)Memory used [KB]: 1663
% 0.21/0.54  % (11083)Time elapsed: 0.140 s
% 0.21/0.54  % (11083)------------------------------
% 0.21/0.54  % (11083)------------------------------
% 0.21/0.55  % (11080)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (11075)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (11087)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.46/0.55  % (11073)Refutation not found, incomplete strategy% (11073)------------------------------
% 1.46/0.55  % (11073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (11073)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (11073)Memory used [KB]: 10618
% 1.46/0.55  % (11073)Time elapsed: 0.136 s
% 1.46/0.55  % (11073)------------------------------
% 1.46/0.55  % (11073)------------------------------
% 1.46/0.55  % (11079)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.55  % (11078)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.55  % (11085)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.46/0.55  % (11079)Refutation not found, incomplete strategy% (11079)------------------------------
% 1.46/0.55  % (11079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (11079)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (11079)Memory used [KB]: 10618
% 1.46/0.55  % (11079)Time elapsed: 0.160 s
% 1.46/0.55  % (11079)------------------------------
% 1.46/0.55  % (11079)------------------------------
% 1.46/0.56  % (11086)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.46/0.57  % (11072)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.57  % (11072)Refutation not found, incomplete strategy% (11072)------------------------------
% 1.46/0.57  % (11072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (11072)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (11072)Memory used [KB]: 10618
% 1.46/0.57  % (11072)Time elapsed: 0.170 s
% 1.46/0.57  % (11072)------------------------------
% 1.46/0.57  % (11072)------------------------------
% 1.66/0.57  % (11078)Refutation found. Thanks to Tanya!
% 1.66/0.57  % SZS status Theorem for theBenchmark
% 1.66/0.57  % SZS output start Proof for theBenchmark
% 1.66/0.57  fof(f341,plain,(
% 1.66/0.57    $false),
% 1.66/0.57    inference(avatar_sat_refutation,[],[f67,f68,f133,f301,f309,f329])).
% 1.66/0.57  fof(f329,plain,(
% 1.66/0.57    spl4_4 | ~spl4_1),
% 1.66/0.57    inference(avatar_split_clause,[],[f328,f60,f130])).
% 1.66/0.57  fof(f130,plain,(
% 1.66/0.57    spl4_4 <=> sK1 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.66/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.66/0.57  fof(f60,plain,(
% 1.66/0.57    spl4_1 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.66/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.66/0.57  fof(f328,plain,(
% 1.66/0.57    sK1 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_1),
% 1.66/0.57    inference(forward_demodulation,[],[f327,f135])).
% 1.66/0.57  fof(f135,plain,(
% 1.66/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.66/0.57    inference(backward_demodulation,[],[f81,f115])).
% 1.66/0.57  fof(f115,plain,(
% 1.66/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.66/0.57    inference(resolution,[],[f94,f22])).
% 1.66/0.57  fof(f22,plain,(
% 1.66/0.57    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.66/0.57    inference(cnf_transformation,[],[f16])).
% 1.66/0.57  fof(f16,plain,(
% 1.66/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.66/0.57    inference(ennf_transformation,[],[f4])).
% 1.66/0.57  fof(f4,axiom,(
% 1.66/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.66/0.57  fof(f94,plain,(
% 1.66/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0))) )),
% 1.66/0.57    inference(global_subsumption,[],[f74,f88])).
% 1.66/0.57  fof(f88,plain,(
% 1.66/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k4_xboole_0(X0,X0))) )),
% 1.66/0.57    inference(duplicate_literal_removal,[],[f86])).
% 1.66/0.57  fof(f86,plain,(
% 1.66/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,k4_xboole_0(X0,X0))) )),
% 1.66/0.57    inference(superposition,[],[f37,f81])).
% 1.66/0.57  fof(f37,plain,(
% 1.66/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f17])).
% 1.66/0.57  fof(f17,plain,(
% 1.66/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.66/0.57    inference(ennf_transformation,[],[f3])).
% 1.66/0.57  fof(f3,axiom,(
% 1.66/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.66/0.57  fof(f74,plain,(
% 1.66/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0)) | r2_hidden(X1,X0)) )),
% 1.66/0.57    inference(superposition,[],[f58,f20])).
% 1.66/0.57  fof(f20,plain,(
% 1.66/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.66/0.57    inference(cnf_transformation,[],[f6])).
% 1.66/0.57  fof(f6,axiom,(
% 1.66/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.66/0.57  fof(f58,plain,(
% 1.66/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 1.66/0.57    inference(equality_resolution,[],[f52])).
% 1.66/0.57  fof(f52,plain,(
% 1.66/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.66/0.57    inference(definition_unfolding,[],[f33,f25])).
% 1.66/0.57  fof(f25,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.66/0.57    inference(cnf_transformation,[],[f7])).
% 1.66/0.57  fof(f7,axiom,(
% 1.66/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.66/0.57  fof(f33,plain,(
% 1.66/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.66/0.57    inference(cnf_transformation,[],[f2])).
% 1.66/0.57  fof(f2,axiom,(
% 1.66/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.66/0.57  fof(f81,plain,(
% 1.66/0.57    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.66/0.57    inference(superposition,[],[f44,f20])).
% 1.66/0.57  fof(f44,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.66/0.57    inference(definition_unfolding,[],[f26,f25])).
% 1.66/0.57  fof(f26,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.66/0.57    inference(cnf_transformation,[],[f5])).
% 1.66/0.57  fof(f5,axiom,(
% 1.66/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.66/0.57  fof(f327,plain,(
% 1.66/0.57    k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k1_xboole_0) | ~spl4_1),
% 1.66/0.57    inference(forward_demodulation,[],[f321,f115])).
% 1.66/0.57  fof(f321,plain,(
% 1.66/0.57    k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~spl4_1),
% 1.66/0.57    inference(superposition,[],[f97,f61])).
% 1.66/0.57  fof(f61,plain,(
% 1.66/0.57    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl4_1),
% 1.66/0.57    inference(avatar_component_clause,[],[f60])).
% 1.66/0.57  fof(f97,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.66/0.57    inference(superposition,[],[f44,f47])).
% 1.66/0.57  fof(f47,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.66/0.57    inference(definition_unfolding,[],[f23,f25,f25])).
% 1.66/0.57  fof(f23,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f1])).
% 1.66/0.57  fof(f1,axiom,(
% 1.66/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.66/0.57  fof(f309,plain,(
% 1.66/0.57    ~spl4_4 | ~spl4_2),
% 1.66/0.57    inference(avatar_split_clause,[],[f306,f64,f130])).
% 1.66/0.57  fof(f64,plain,(
% 1.66/0.57    spl4_2 <=> r2_hidden(sK0,sK1)),
% 1.66/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.66/0.57  fof(f306,plain,(
% 1.66/0.57    sK1 != k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_2),
% 1.66/0.57    inference(resolution,[],[f66,f48])).
% 1.66/0.57  fof(f48,plain,(
% 1.66/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0) )),
% 1.66/0.57    inference(definition_unfolding,[],[f28,f43])).
% 1.66/0.57  fof(f43,plain,(
% 1.66/0.57    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.66/0.57    inference(definition_unfolding,[],[f21,f42])).
% 1.66/0.57  fof(f42,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.66/0.57    inference(definition_unfolding,[],[f24,f41])).
% 1.66/0.57  fof(f41,plain,(
% 1.66/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.66/0.57    inference(definition_unfolding,[],[f29,f40])).
% 1.66/0.57  fof(f40,plain,(
% 1.66/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f11])).
% 1.66/0.57  fof(f11,axiom,(
% 1.66/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.66/0.57  fof(f29,plain,(
% 1.66/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f10])).
% 1.66/0.57  fof(f10,axiom,(
% 1.66/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.66/0.57  fof(f24,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f9])).
% 1.66/0.57  fof(f9,axiom,(
% 1.66/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.66/0.57  fof(f21,plain,(
% 1.66/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f8])).
% 1.66/0.57  fof(f8,axiom,(
% 1.66/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.66/0.57  fof(f28,plain,(
% 1.66/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.66/0.57    inference(cnf_transformation,[],[f12])).
% 1.66/0.57  fof(f12,axiom,(
% 1.66/0.57    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.66/0.57  fof(f66,plain,(
% 1.66/0.57    r2_hidden(sK0,sK1) | ~spl4_2),
% 1.66/0.57    inference(avatar_component_clause,[],[f64])).
% 1.66/0.57  fof(f301,plain,(
% 1.66/0.57    spl4_1 | ~spl4_4),
% 1.66/0.57    inference(avatar_split_clause,[],[f300,f130,f60])).
% 1.66/0.57  fof(f300,plain,(
% 1.66/0.57    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl4_4),
% 1.66/0.57    inference(forward_demodulation,[],[f299,f135])).
% 1.66/0.57  fof(f299,plain,(
% 1.66/0.57    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) | ~spl4_4),
% 1.66/0.57    inference(forward_demodulation,[],[f288,f115])).
% 1.66/0.57  fof(f288,plain,(
% 1.66/0.57    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,sK1)) | ~spl4_4),
% 1.66/0.57    inference(superposition,[],[f97,f132])).
% 1.66/0.57  fof(f132,plain,(
% 1.66/0.57    sK1 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_4),
% 1.66/0.57    inference(avatar_component_clause,[],[f130])).
% 1.66/0.57  fof(f133,plain,(
% 1.66/0.57    spl4_4 | spl4_2),
% 1.66/0.57    inference(avatar_split_clause,[],[f117,f64,f130])).
% 1.66/0.57  fof(f117,plain,(
% 1.66/0.57    sK1 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl4_2),
% 1.66/0.57    inference(resolution,[],[f49,f65])).
% 1.66/0.57  fof(f65,plain,(
% 1.66/0.57    ~r2_hidden(sK0,sK1) | spl4_2),
% 1.66/0.57    inference(avatar_component_clause,[],[f64])).
% 1.66/0.57  fof(f49,plain,(
% 1.66/0.57    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0) )),
% 1.66/0.57    inference(definition_unfolding,[],[f27,f43])).
% 1.66/0.57  fof(f27,plain,(
% 1.66/0.57    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 1.66/0.57    inference(cnf_transformation,[],[f12])).
% 1.66/0.57  fof(f68,plain,(
% 1.66/0.57    spl4_1 | ~spl4_2),
% 1.66/0.57    inference(avatar_split_clause,[],[f46,f64,f60])).
% 1.66/0.57  fof(f46,plain,(
% 1.66/0.57    ~r2_hidden(sK0,sK1) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.66/0.57    inference(definition_unfolding,[],[f18,f43,f43])).
% 1.66/0.57  fof(f18,plain,(
% 1.66/0.57    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.66/0.57    inference(cnf_transformation,[],[f15])).
% 1.66/0.57  fof(f15,plain,(
% 1.66/0.57    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.66/0.57    inference(ennf_transformation,[],[f14])).
% 1.66/0.57  fof(f14,negated_conjecture,(
% 1.66/0.57    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.66/0.57    inference(negated_conjecture,[],[f13])).
% 1.66/0.57  fof(f13,conjecture,(
% 1.66/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.66/0.57  fof(f67,plain,(
% 1.66/0.57    ~spl4_1 | spl4_2),
% 1.66/0.57    inference(avatar_split_clause,[],[f45,f64,f60])).
% 1.66/0.57  fof(f45,plain,(
% 1.66/0.57    r2_hidden(sK0,sK1) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.66/0.57    inference(definition_unfolding,[],[f19,f43,f43])).
% 1.66/0.57  fof(f19,plain,(
% 1.66/0.57    r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.66/0.57    inference(cnf_transformation,[],[f15])).
% 1.66/0.57  % SZS output end Proof for theBenchmark
% 1.66/0.57  % (11078)------------------------------
% 1.66/0.57  % (11078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.57  % (11078)Termination reason: Refutation
% 1.66/0.57  
% 1.66/0.57  % (11078)Memory used [KB]: 10874
% 1.66/0.57  % (11078)Time elapsed: 0.165 s
% 1.66/0.57  % (11078)------------------------------
% 1.66/0.57  % (11078)------------------------------
% 1.66/0.57  % (11061)Success in time 0.212 s
%------------------------------------------------------------------------------
