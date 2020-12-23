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
% DateTime   : Thu Dec  3 12:50:43 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 200 expanded)
%              Number of leaves         :   16 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 288 expanded)
%              Number of equality atoms :   34 ( 134 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f798,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f305,f314,f344,f797])).

fof(f797,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f796,f341,f63,f53])).

fof(f53,plain,
    ( spl5_1
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f63,plain,
    ( spl5_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f341,plain,
    ( spl5_11
  <=> sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f796,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(superposition,[],[f325,f343])).

fof(f343,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f341])).

fof(f325,plain,
    ( ! [X12,X13] : r1_tarski(k10_relat_1(sK2,X12),k10_relat_1(sK2,k3_tarski(k1_enumset1(X12,X12,X13))))
    | ~ spl5_3 ),
    inference(superposition,[],[f44,f118])).

fof(f118,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)))
    | ~ spl5_3 ),
    inference(resolution,[],[f47,f65])).

fof(f65,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f34,f42,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f26,f42])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f344,plain,
    ( spl5_11
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f339,f311,f341])).

fof(f311,plain,
    ( spl5_10
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f339,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f338,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f27,f28,f28])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f338,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK1,sK1,sK0))
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f329,f98])).

fof(f98,plain,(
    ! [X1] : k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) = X1 ),
    inference(forward_demodulation,[],[f95,f43])).

fof(f43,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f25,f42])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f95,plain,(
    ! [X1] : k3_tarski(k1_enumset1(X1,X1,X1)) = k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) ),
    inference(superposition,[],[f46,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f80,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f48,f44])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f30,f42,f42])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f329,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0))
    | ~ spl5_10 ),
    inference(superposition,[],[f46,f313])).

fof(f313,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f311])).

fof(f314,plain,
    ( spl5_10
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f306,f302,f311])).

fof(f302,plain,
    ( spl5_9
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f306,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_9 ),
    inference(resolution,[],[f304,f24])).

fof(f304,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f302])).

fof(f305,plain,
    ( spl5_9
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f289,f58,f302])).

fof(f58,plain,
    ( spl5_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f289,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl5_2 ),
    inference(resolution,[],[f264,f60])).

fof(f60,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f258,f86])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r1_tarski(k4_xboole_0(X1,X0),k4_xboole_0(X0,X0)) ) ),
    inference(superposition,[],[f88,f43])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_tarski(k1_enumset1(X0,X0,X1)))
      | r1_tarski(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0)) ) ),
    inference(superposition,[],[f48,f46])).

fof(f66,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f21,f63])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f61,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f22,f58])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:46:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (24152)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (24141)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (24140)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (24160)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.52  % (24142)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.52  % (24144)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.53  % (24155)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.27/0.53  % (24139)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.53  % (24149)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.53  % (24159)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.53  % (24137)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.53  % (24147)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.27/0.53  % (24165)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.27/0.53  % (24151)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.54  % (24159)Refutation not found, incomplete strategy% (24159)------------------------------
% 1.27/0.54  % (24159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (24166)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.54  % (24159)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (24159)Memory used [KB]: 10618
% 1.40/0.54  % (24159)Time elapsed: 0.088 s
% 1.40/0.54  % (24159)------------------------------
% 1.40/0.54  % (24159)------------------------------
% 1.40/0.54  % (24146)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.54  % (24148)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.54  % (24143)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.54  % (24163)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.54  % (24162)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.54  % (24154)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.55  % (24138)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.55  % (24158)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.55  % (24156)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.55  % (24164)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.55  % (24157)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.55  % (24161)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.55  % (24150)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.56  % (24154)Refutation not found, incomplete strategy% (24154)------------------------------
% 1.40/0.56  % (24154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (24154)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (24154)Memory used [KB]: 10618
% 1.40/0.56  % (24154)Time elapsed: 0.148 s
% 1.40/0.56  % (24154)------------------------------
% 1.40/0.56  % (24154)------------------------------
% 1.40/0.56  % (24153)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.56  % (24145)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.59  % (24153)Refutation found. Thanks to Tanya!
% 1.40/0.59  % SZS status Theorem for theBenchmark
% 1.40/0.61  % SZS output start Proof for theBenchmark
% 1.40/0.61  fof(f798,plain,(
% 1.40/0.61    $false),
% 1.40/0.61    inference(avatar_sat_refutation,[],[f56,f61,f66,f305,f314,f344,f797])).
% 1.40/0.61  fof(f797,plain,(
% 1.40/0.61    spl5_1 | ~spl5_3 | ~spl5_11),
% 1.40/0.61    inference(avatar_split_clause,[],[f796,f341,f63,f53])).
% 1.40/0.61  fof(f53,plain,(
% 1.40/0.61    spl5_1 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.40/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.40/0.61  fof(f63,plain,(
% 1.40/0.61    spl5_3 <=> v1_relat_1(sK2)),
% 1.40/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.40/0.61  fof(f341,plain,(
% 1.40/0.61    spl5_11 <=> sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.40/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.40/0.61  fof(f796,plain,(
% 1.40/0.61    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | (~spl5_3 | ~spl5_11)),
% 1.40/0.61    inference(superposition,[],[f325,f343])).
% 1.40/0.61  fof(f343,plain,(
% 1.40/0.61    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl5_11),
% 1.40/0.61    inference(avatar_component_clause,[],[f341])).
% 1.40/0.61  fof(f325,plain,(
% 1.40/0.61    ( ! [X12,X13] : (r1_tarski(k10_relat_1(sK2,X12),k10_relat_1(sK2,k3_tarski(k1_enumset1(X12,X12,X13))))) ) | ~spl5_3),
% 1.40/0.61    inference(superposition,[],[f44,f118])).
% 1.40/0.61  fof(f118,plain,(
% 1.40/0.61    ( ! [X0,X1] : (k10_relat_1(sK2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)))) ) | ~spl5_3),
% 1.40/0.61    inference(resolution,[],[f47,f65])).
% 1.40/0.61  fof(f65,plain,(
% 1.40/0.61    v1_relat_1(sK2) | ~spl5_3),
% 1.40/0.61    inference(avatar_component_clause,[],[f63])).
% 1.40/0.61  fof(f47,plain,(
% 1.40/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) )),
% 1.40/0.61    inference(definition_unfolding,[],[f34,f42,f42])).
% 1.40/0.61  fof(f42,plain,(
% 1.40/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.40/0.61    inference(definition_unfolding,[],[f29,f28])).
% 1.40/0.61  fof(f28,plain,(
% 1.40/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.40/0.61    inference(cnf_transformation,[],[f9])).
% 1.40/0.61  fof(f9,axiom,(
% 1.40/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.40/0.61  fof(f29,plain,(
% 1.40/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.40/0.61    inference(cnf_transformation,[],[f10])).
% 1.40/0.61  fof(f10,axiom,(
% 1.40/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.40/0.61  fof(f34,plain,(
% 1.40/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 1.40/0.61    inference(cnf_transformation,[],[f19])).
% 1.40/0.61  fof(f19,plain,(
% 1.40/0.61    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.40/0.61    inference(ennf_transformation,[],[f11])).
% 1.40/0.61  fof(f11,axiom,(
% 1.40/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 1.40/0.61  fof(f44,plain,(
% 1.40/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 1.40/0.61    inference(definition_unfolding,[],[f26,f42])).
% 1.40/0.61  fof(f26,plain,(
% 1.40/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.40/0.61    inference(cnf_transformation,[],[f7])).
% 1.40/0.61  fof(f7,axiom,(
% 1.40/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.40/0.61  fof(f344,plain,(
% 1.40/0.61    spl5_11 | ~spl5_10),
% 1.40/0.61    inference(avatar_split_clause,[],[f339,f311,f341])).
% 1.40/0.61  fof(f311,plain,(
% 1.40/0.61    spl5_10 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.40/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.40/0.61  fof(f339,plain,(
% 1.40/0.61    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl5_10),
% 1.40/0.61    inference(forward_demodulation,[],[f338,f45])).
% 1.40/0.61  fof(f45,plain,(
% 1.40/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.40/0.61    inference(definition_unfolding,[],[f27,f28,f28])).
% 1.40/0.61  fof(f27,plain,(
% 1.40/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.40/0.61    inference(cnf_transformation,[],[f8])).
% 1.40/0.61  fof(f8,axiom,(
% 1.40/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.40/0.61  fof(f338,plain,(
% 1.40/0.61    sK1 = k3_tarski(k1_enumset1(sK1,sK1,sK0)) | ~spl5_10),
% 1.40/0.61    inference(forward_demodulation,[],[f329,f98])).
% 1.40/0.61  fof(f98,plain,(
% 1.40/0.61    ( ! [X1] : (k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) = X1) )),
% 1.40/0.61    inference(forward_demodulation,[],[f95,f43])).
% 1.40/0.61  fof(f43,plain,(
% 1.40/0.61    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 1.40/0.61    inference(definition_unfolding,[],[f25,f42])).
% 1.40/0.61  fof(f25,plain,(
% 1.40/0.61    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.40/0.61    inference(cnf_transformation,[],[f14])).
% 1.40/0.61  fof(f14,plain,(
% 1.40/0.61    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.40/0.61    inference(rectify,[],[f3])).
% 1.40/0.61  fof(f3,axiom,(
% 1.40/0.61    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.40/0.61  fof(f95,plain,(
% 1.40/0.61    ( ! [X1] : (k3_tarski(k1_enumset1(X1,X1,X1)) = k3_tarski(k1_enumset1(X1,X1,k1_xboole_0))) )),
% 1.40/0.61    inference(superposition,[],[f46,f86])).
% 1.40/0.61  fof(f86,plain,(
% 1.40/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.40/0.61    inference(resolution,[],[f80,f24])).
% 1.40/0.61  fof(f24,plain,(
% 1.40/0.61    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.40/0.61    inference(cnf_transformation,[],[f17])).
% 1.40/0.61  fof(f17,plain,(
% 1.40/0.61    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.40/0.61    inference(ennf_transformation,[],[f5])).
% 1.40/0.61  fof(f5,axiom,(
% 1.40/0.61    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.40/0.61  fof(f80,plain,(
% 1.40/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 1.40/0.61    inference(resolution,[],[f48,f44])).
% 1.40/0.61  fof(f48,plain,(
% 1.40/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.40/0.61    inference(definition_unfolding,[],[f35,f42])).
% 1.40/0.61  fof(f35,plain,(
% 1.40/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.40/0.61    inference(cnf_transformation,[],[f20])).
% 1.40/0.61  fof(f20,plain,(
% 1.40/0.61    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.40/0.61    inference(ennf_transformation,[],[f6])).
% 1.40/0.61  fof(f6,axiom,(
% 1.40/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.40/0.61  fof(f46,plain,(
% 1.40/0.61    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0)))) )),
% 1.40/0.61    inference(definition_unfolding,[],[f30,f42,f42])).
% 1.40/0.61  fof(f30,plain,(
% 1.40/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.40/0.61    inference(cnf_transformation,[],[f4])).
% 1.40/0.61  fof(f4,axiom,(
% 1.40/0.61    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.40/0.61  fof(f329,plain,(
% 1.40/0.61    k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0)) | ~spl5_10),
% 1.40/0.61    inference(superposition,[],[f46,f313])).
% 1.40/0.61  fof(f313,plain,(
% 1.40/0.61    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl5_10),
% 1.40/0.61    inference(avatar_component_clause,[],[f311])).
% 1.40/0.61  fof(f314,plain,(
% 1.40/0.61    spl5_10 | ~spl5_9),
% 1.40/0.61    inference(avatar_split_clause,[],[f306,f302,f311])).
% 1.40/0.61  fof(f302,plain,(
% 1.40/0.61    spl5_9 <=> r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.40/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.40/0.61  fof(f306,plain,(
% 1.40/0.61    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl5_9),
% 1.40/0.61    inference(resolution,[],[f304,f24])).
% 1.40/0.61  fof(f304,plain,(
% 1.40/0.61    r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl5_9),
% 1.40/0.61    inference(avatar_component_clause,[],[f302])).
% 1.40/0.61  fof(f305,plain,(
% 1.40/0.61    spl5_9 | ~spl5_2),
% 1.40/0.61    inference(avatar_split_clause,[],[f289,f58,f302])).
% 1.40/0.61  fof(f58,plain,(
% 1.40/0.61    spl5_2 <=> r1_tarski(sK0,sK1)),
% 1.40/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.40/0.61  fof(f289,plain,(
% 1.40/0.61    r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl5_2),
% 1.40/0.61    inference(resolution,[],[f264,f60])).
% 1.40/0.61  fof(f60,plain,(
% 1.40/0.61    r1_tarski(sK0,sK1) | ~spl5_2),
% 1.40/0.61    inference(avatar_component_clause,[],[f58])).
% 1.40/0.61  fof(f264,plain,(
% 1.40/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0)) )),
% 1.40/0.61    inference(forward_demodulation,[],[f258,f86])).
% 1.40/0.61  fof(f258,plain,(
% 1.40/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r1_tarski(k4_xboole_0(X1,X0),k4_xboole_0(X0,X0))) )),
% 1.40/0.61    inference(superposition,[],[f88,f43])).
% 1.40/0.61  fof(f88,plain,(
% 1.40/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_tarski(k1_enumset1(X0,X0,X1))) | r1_tarski(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0))) )),
% 1.40/0.61    inference(superposition,[],[f48,f46])).
% 1.40/0.61  fof(f66,plain,(
% 1.40/0.61    spl5_3),
% 1.40/0.61    inference(avatar_split_clause,[],[f21,f63])).
% 1.40/0.61  fof(f21,plain,(
% 1.40/0.61    v1_relat_1(sK2)),
% 1.40/0.61    inference(cnf_transformation,[],[f16])).
% 1.40/0.61  fof(f16,plain,(
% 1.40/0.61    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.40/0.61    inference(flattening,[],[f15])).
% 1.40/0.61  fof(f15,plain,(
% 1.40/0.61    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.40/0.61    inference(ennf_transformation,[],[f13])).
% 1.40/0.61  fof(f13,negated_conjecture,(
% 1.40/0.61    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 1.40/0.61    inference(negated_conjecture,[],[f12])).
% 1.40/0.61  fof(f12,conjecture,(
% 1.40/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 1.40/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 1.40/0.61  fof(f61,plain,(
% 1.40/0.61    spl5_2),
% 1.40/0.61    inference(avatar_split_clause,[],[f22,f58])).
% 1.40/0.61  fof(f22,plain,(
% 1.40/0.61    r1_tarski(sK0,sK1)),
% 1.40/0.61    inference(cnf_transformation,[],[f16])).
% 1.40/0.61  fof(f56,plain,(
% 1.40/0.61    ~spl5_1),
% 1.40/0.61    inference(avatar_split_clause,[],[f23,f53])).
% 1.40/0.61  fof(f23,plain,(
% 1.40/0.61    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.40/0.61    inference(cnf_transformation,[],[f16])).
% 1.40/0.61  % SZS output end Proof for theBenchmark
% 1.40/0.61  % (24153)------------------------------
% 1.40/0.61  % (24153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.61  % (24153)Termination reason: Refutation
% 1.40/0.61  
% 1.40/0.61  % (24153)Memory used [KB]: 11257
% 1.40/0.61  % (24153)Time elapsed: 0.171 s
% 1.40/0.61  % (24153)------------------------------
% 1.40/0.61  % (24153)------------------------------
% 1.40/0.61  % (24136)Success in time 0.248 s
%------------------------------------------------------------------------------
