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
% DateTime   : Thu Dec  3 12:32:36 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 177 expanded)
%              Number of leaves         :   17 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  133 ( 295 expanded)
%              Number of equality atoms :   39 ( 124 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f53,f72,f1116,f1129,f2134,f2195])).

fof(f2195,plain,
    ( spl3_2
    | ~ spl3_82 ),
    inference(avatar_split_clause,[],[f2187,f2128,f46])).

fof(f46,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f2128,plain,
    ( spl3_82
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f2187,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_82 ),
    inference(superposition,[],[f1400,f2130])).

fof(f2130,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_82 ),
    inference(avatar_component_clause,[],[f2128])).

fof(f1400,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(resolution,[],[f263,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f263,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(resolution,[],[f233,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f31,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f233,plain,(
    ! [X2] : r1_tarski(X2,X2) ),
    inference(trivial_inequality_removal,[],[f229])).

fof(f229,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X2,X2) ) ),
    inference(superposition,[],[f35,f147])).

fof(f147,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(resolution,[],[f34,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f24,f25,f25])).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f2134,plain,
    ( spl3_82
    | ~ spl3_5
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f2053,f1126,f69,f2128])).

fof(f69,plain,
    ( spl3_5
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1126,plain,
    ( spl3_49
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f2053,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_5
    | ~ spl3_49 ),
    inference(superposition,[],[f71,f1139])).

fof(f1139,plain,
    ( ! [X0] : k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))
    | ~ spl3_49 ),
    inference(superposition,[],[f37,f1128])).

fof(f1128,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f1126])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f30,f25,f25])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f71,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f1129,plain,
    ( spl3_49
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f1119,f50,f1126])).

fof(f50,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1119,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f51,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f51,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f1116,plain,
    ( spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f1104,f69,f50])).

fof(f1104,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_5 ),
    inference(superposition,[],[f559,f71])).

fof(f559,plain,(
    ! [X14,X15,X13] : r1_tarski(k3_xboole_0(X15,k5_xboole_0(X13,k3_xboole_0(X13,X14))),X13) ),
    inference(trivial_inequality_removal,[],[f558])).

fof(f558,plain,(
    ! [X14,X15,X13] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k3_xboole_0(X15,k5_xboole_0(X13,k3_xboole_0(X13,X14))),X13) ) ),
    inference(forward_demodulation,[],[f557,f315])).

fof(f315,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f262,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f262,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3) ),
    inference(resolution,[],[f230,f26])).

fof(f230,plain,(
    ! [X3] : r1_tarski(k1_xboole_0,X3) ),
    inference(superposition,[],[f33,f147])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f557,plain,(
    ! [X14,X15,X13] :
      ( k1_xboole_0 != k3_xboole_0(X15,k1_xboole_0)
      | r1_tarski(k3_xboole_0(X15,k5_xboole_0(X13,k3_xboole_0(X13,X14))),X13) ) ),
    inference(forward_demodulation,[],[f536,f344])).

fof(f344,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f147,f265])).

fof(f265,plain,(
    ! [X3] : k3_xboole_0(X3,X3) = X3 ),
    inference(resolution,[],[f233,f26])).

fof(f536,plain,(
    ! [X14,X15,X13] :
      ( k1_xboole_0 != k3_xboole_0(X15,k5_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,X14)),k5_xboole_0(X13,k3_xboole_0(X13,X14))))
      | r1_tarski(k3_xboole_0(X15,k5_xboole_0(X13,k3_xboole_0(X13,X14))),X13) ) ),
    inference(superposition,[],[f223,f66])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(resolution,[],[f26,f33])).

fof(f223,plain,(
    ! [X6,X8,X7] :
      ( k1_xboole_0 != k3_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X8)))
      | r1_tarski(k3_xboole_0(X6,X7),X8) ) ),
    inference(superposition,[],[f35,f37])).

fof(f72,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f65,f41,f69])).

fof(f41,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f65,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(resolution,[],[f26,f43])).

fof(f43,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f53,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f18,f50,f46])).

fof(f18,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f44,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f32,f41])).

fof(f32,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f19,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:07:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (22993)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (23010)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (22997)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (23001)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (22992)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (23011)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (23003)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (23011)Refutation not found, incomplete strategy% (23011)------------------------------
% 0.20/0.51  % (23011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23011)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23011)Memory used [KB]: 10618
% 0.20/0.51  % (23011)Time elapsed: 0.073 s
% 0.20/0.51  % (23011)------------------------------
% 0.20/0.51  % (23011)------------------------------
% 0.20/0.51  % (23013)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (22995)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (22990)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (22991)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (23005)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (23002)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (23000)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (23000)Refutation not found, incomplete strategy% (23000)------------------------------
% 0.20/0.52  % (23000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23000)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23000)Memory used [KB]: 10618
% 0.20/0.52  % (23000)Time elapsed: 0.120 s
% 0.20/0.53  % (23016)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (22989)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (22989)Refutation not found, incomplete strategy% (22989)------------------------------
% 0.20/0.53  % (22989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (22989)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (22989)Memory used [KB]: 1663
% 0.20/0.53  % (22989)Time elapsed: 0.127 s
% 0.20/0.53  % (22989)------------------------------
% 0.20/0.53  % (22989)------------------------------
% 0.20/0.54  % (23006)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (23009)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (23006)Refutation not found, incomplete strategy% (23006)------------------------------
% 0.20/0.54  % (23006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23006)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (23006)Memory used [KB]: 10618
% 0.20/0.54  % (23006)Time elapsed: 0.130 s
% 0.20/0.54  % (23006)------------------------------
% 0.20/0.54  % (23006)------------------------------
% 0.20/0.54  % (22994)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (23017)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (23018)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (22999)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (23000)------------------------------
% 0.20/0.54  % (23000)------------------------------
% 0.20/0.55  % (22996)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (23014)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (22999)Refutation not found, incomplete strategy% (22999)------------------------------
% 0.20/0.55  % (22999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22999)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (22999)Memory used [KB]: 10618
% 0.20/0.55  % (22999)Time elapsed: 0.141 s
% 0.20/0.55  % (22999)------------------------------
% 0.20/0.55  % (22999)------------------------------
% 0.20/0.55  % (23015)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (23008)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (22998)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (23012)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.56  % (22998)Refutation not found, incomplete strategy% (22998)------------------------------
% 0.20/0.56  % (22998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (22998)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (22998)Memory used [KB]: 10618
% 0.20/0.56  % (22998)Time elapsed: 0.151 s
% 0.20/0.56  % (22998)------------------------------
% 0.20/0.56  % (22998)------------------------------
% 0.20/0.56  % (23004)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.56  % (23007)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.79/0.62  % (23005)Refutation found. Thanks to Tanya!
% 1.79/0.62  % SZS status Theorem for theBenchmark
% 2.05/0.63  % SZS output start Proof for theBenchmark
% 2.05/0.63  fof(f2196,plain,(
% 2.05/0.63    $false),
% 2.05/0.63    inference(avatar_sat_refutation,[],[f44,f53,f72,f1116,f1129,f2134,f2195])).
% 2.05/0.63  fof(f2195,plain,(
% 2.05/0.63    spl3_2 | ~spl3_82),
% 2.05/0.63    inference(avatar_split_clause,[],[f2187,f2128,f46])).
% 2.05/0.63  fof(f46,plain,(
% 2.05/0.63    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.05/0.63  fof(f2128,plain,(
% 2.05/0.63    spl3_82 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 2.05/0.63  fof(f2187,plain,(
% 2.05/0.63    r1_xboole_0(sK0,sK2) | ~spl3_82),
% 2.05/0.63    inference(superposition,[],[f1400,f2130])).
% 2.05/0.63  fof(f2130,plain,(
% 2.05/0.63    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl3_82),
% 2.05/0.63    inference(avatar_component_clause,[],[f2128])).
% 2.05/0.63  fof(f1400,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.05/0.63    inference(resolution,[],[f263,f27])).
% 2.05/0.63  fof(f27,plain,(
% 2.05/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f16])).
% 2.05/0.63  fof(f16,plain,(
% 2.05/0.63    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.05/0.63    inference(ennf_transformation,[],[f2])).
% 2.05/0.63  fof(f2,axiom,(
% 2.05/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.05/0.63  fof(f263,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.05/0.63    inference(resolution,[],[f233,f38])).
% 2.05/0.63  fof(f38,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) )),
% 2.05/0.63    inference(definition_unfolding,[],[f31,f25])).
% 2.05/0.63  fof(f25,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f4])).
% 2.05/0.63  fof(f4,axiom,(
% 2.05/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.05/0.63  fof(f31,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f17])).
% 2.05/0.63  fof(f17,plain,(
% 2.05/0.63    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.05/0.63    inference(ennf_transformation,[],[f10])).
% 2.05/0.63  fof(f10,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 2.05/0.63  fof(f233,plain,(
% 2.05/0.63    ( ! [X2] : (r1_tarski(X2,X2)) )),
% 2.05/0.63    inference(trivial_inequality_removal,[],[f229])).
% 2.05/0.63  fof(f229,plain,(
% 2.05/0.63    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X2,X2)) )),
% 2.05/0.63    inference(superposition,[],[f35,f147])).
% 2.05/0.63  fof(f147,plain,(
% 2.05/0.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 2.05/0.63    inference(resolution,[],[f34,f20])).
% 2.05/0.63  fof(f20,plain,(
% 2.05/0.63    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 2.05/0.63    inference(cnf_transformation,[],[f14])).
% 2.05/0.63  fof(f14,plain,(
% 2.05/0.63    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.05/0.63    inference(ennf_transformation,[],[f8])).
% 2.05/0.63  fof(f8,axiom,(
% 2.05/0.63    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 2.05/0.63  fof(f34,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.05/0.63    inference(definition_unfolding,[],[f24,f25,f25])).
% 2.05/0.63  fof(f24,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f9])).
% 2.05/0.63  fof(f9,axiom,(
% 2.05/0.63    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).
% 2.05/0.63  fof(f35,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f29,f25])).
% 2.05/0.63  fof(f29,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.05/0.63    inference(cnf_transformation,[],[f3])).
% 2.05/0.63  fof(f3,axiom,(
% 2.05/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.05/0.63  fof(f2134,plain,(
% 2.05/0.63    spl3_82 | ~spl3_5 | ~spl3_49),
% 2.05/0.63    inference(avatar_split_clause,[],[f2053,f1126,f69,f2128])).
% 2.05/0.63  fof(f69,plain,(
% 2.05/0.63    spl3_5 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.05/0.63  fof(f1126,plain,(
% 2.05/0.63    spl3_49 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 2.05/0.63  fof(f2053,plain,(
% 2.05/0.63    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | (~spl3_5 | ~spl3_49)),
% 2.05/0.63    inference(superposition,[],[f71,f1139])).
% 2.05/0.63  fof(f1139,plain,(
% 2.05/0.63    ( ! [X0] : (k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))) ) | ~spl3_49),
% 2.05/0.63    inference(superposition,[],[f37,f1128])).
% 2.05/0.63  fof(f1128,plain,(
% 2.05/0.63    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_49),
% 2.05/0.63    inference(avatar_component_clause,[],[f1126])).
% 2.05/0.63  fof(f37,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 2.05/0.63    inference(definition_unfolding,[],[f30,f25,f25])).
% 2.05/0.63  fof(f30,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f7])).
% 2.05/0.63  fof(f7,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.05/0.63  fof(f71,plain,(
% 2.05/0.63    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_5),
% 2.05/0.63    inference(avatar_component_clause,[],[f69])).
% 2.05/0.63  fof(f1129,plain,(
% 2.05/0.63    spl3_49 | ~spl3_3),
% 2.05/0.63    inference(avatar_split_clause,[],[f1119,f50,f1126])).
% 2.05/0.63  fof(f50,plain,(
% 2.05/0.63    spl3_3 <=> r1_tarski(sK0,sK1)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.05/0.63  fof(f1119,plain,(
% 2.05/0.63    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_3),
% 2.05/0.63    inference(resolution,[],[f51,f26])).
% 2.05/0.63  fof(f26,plain,(
% 2.05/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.05/0.63    inference(cnf_transformation,[],[f15])).
% 2.05/0.63  fof(f15,plain,(
% 2.05/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.05/0.63    inference(ennf_transformation,[],[f5])).
% 2.05/0.63  fof(f5,axiom,(
% 2.05/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.05/0.63  fof(f51,plain,(
% 2.05/0.63    r1_tarski(sK0,sK1) | ~spl3_3),
% 2.05/0.63    inference(avatar_component_clause,[],[f50])).
% 2.05/0.63  fof(f1116,plain,(
% 2.05/0.63    spl3_3 | ~spl3_5),
% 2.05/0.63    inference(avatar_split_clause,[],[f1104,f69,f50])).
% 2.05/0.63  fof(f1104,plain,(
% 2.05/0.63    r1_tarski(sK0,sK1) | ~spl3_5),
% 2.05/0.63    inference(superposition,[],[f559,f71])).
% 2.05/0.63  fof(f559,plain,(
% 2.05/0.63    ( ! [X14,X15,X13] : (r1_tarski(k3_xboole_0(X15,k5_xboole_0(X13,k3_xboole_0(X13,X14))),X13)) )),
% 2.05/0.63    inference(trivial_inequality_removal,[],[f558])).
% 2.05/0.63  fof(f558,plain,(
% 2.05/0.63    ( ! [X14,X15,X13] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k3_xboole_0(X15,k5_xboole_0(X13,k3_xboole_0(X13,X14))),X13)) )),
% 2.05/0.63    inference(forward_demodulation,[],[f557,f315])).
% 2.05/0.63  fof(f315,plain,(
% 2.05/0.63    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 2.05/0.63    inference(superposition,[],[f262,f23])).
% 2.05/0.63  fof(f23,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f1])).
% 2.05/0.63  fof(f1,axiom,(
% 2.05/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.05/0.63  fof(f262,plain,(
% 2.05/0.63    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) )),
% 2.05/0.63    inference(resolution,[],[f230,f26])).
% 2.05/0.63  fof(f230,plain,(
% 2.05/0.63    ( ! [X3] : (r1_tarski(k1_xboole_0,X3)) )),
% 2.05/0.63    inference(superposition,[],[f33,f147])).
% 2.05/0.63  fof(f33,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f22,f25])).
% 2.05/0.63  fof(f22,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f6])).
% 2.05/0.63  fof(f6,axiom,(
% 2.05/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.05/0.63  fof(f557,plain,(
% 2.05/0.63    ( ! [X14,X15,X13] : (k1_xboole_0 != k3_xboole_0(X15,k1_xboole_0) | r1_tarski(k3_xboole_0(X15,k5_xboole_0(X13,k3_xboole_0(X13,X14))),X13)) )),
% 2.05/0.63    inference(forward_demodulation,[],[f536,f344])).
% 2.05/0.63  fof(f344,plain,(
% 2.05/0.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.05/0.63    inference(backward_demodulation,[],[f147,f265])).
% 2.05/0.63  fof(f265,plain,(
% 2.05/0.63    ( ! [X3] : (k3_xboole_0(X3,X3) = X3) )),
% 2.05/0.63    inference(resolution,[],[f233,f26])).
% 2.05/0.63  fof(f536,plain,(
% 2.05/0.63    ( ! [X14,X15,X13] : (k1_xboole_0 != k3_xboole_0(X15,k5_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,X14)),k5_xboole_0(X13,k3_xboole_0(X13,X14)))) | r1_tarski(k3_xboole_0(X15,k5_xboole_0(X13,k3_xboole_0(X13,X14))),X13)) )),
% 2.05/0.63    inference(superposition,[],[f223,f66])).
% 2.05/0.63  fof(f66,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.05/0.63    inference(resolution,[],[f26,f33])).
% 2.05/0.63  fof(f223,plain,(
% 2.05/0.63    ( ! [X6,X8,X7] : (k1_xboole_0 != k3_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X8))) | r1_tarski(k3_xboole_0(X6,X7),X8)) )),
% 2.05/0.63    inference(superposition,[],[f35,f37])).
% 2.05/0.63  fof(f72,plain,(
% 2.05/0.63    spl3_5 | ~spl3_1),
% 2.05/0.63    inference(avatar_split_clause,[],[f65,f41,f69])).
% 2.13/0.64  fof(f41,plain,(
% 2.13/0.64    spl3_1 <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.13/0.64  fof(f65,plain,(
% 2.13/0.64    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_1),
% 2.13/0.64    inference(resolution,[],[f26,f43])).
% 2.13/0.64  fof(f43,plain,(
% 2.13/0.64    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_1),
% 2.13/0.64    inference(avatar_component_clause,[],[f41])).
% 2.13/0.64  fof(f53,plain,(
% 2.13/0.64    ~spl3_2 | ~spl3_3),
% 2.13/0.64    inference(avatar_split_clause,[],[f18,f50,f46])).
% 2.13/0.64  fof(f18,plain,(
% 2.13/0.64    ~r1_tarski(sK0,sK1) | ~r1_xboole_0(sK0,sK2)),
% 2.13/0.64    inference(cnf_transformation,[],[f13])).
% 2.13/0.64  fof(f13,plain,(
% 2.13/0.64    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.13/0.64    inference(ennf_transformation,[],[f12])).
% 2.13/0.64  fof(f12,negated_conjecture,(
% 2.13/0.64    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.13/0.64    inference(negated_conjecture,[],[f11])).
% 2.13/0.64  fof(f11,conjecture,(
% 2.13/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.13/0.64  fof(f44,plain,(
% 2.13/0.64    spl3_1),
% 2.13/0.64    inference(avatar_split_clause,[],[f32,f41])).
% 2.13/0.64  fof(f32,plain,(
% 2.13/0.64    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 2.13/0.64    inference(definition_unfolding,[],[f19,f25])).
% 2.13/0.64  fof(f19,plain,(
% 2.13/0.64    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 2.13/0.64    inference(cnf_transformation,[],[f13])).
% 2.13/0.64  % SZS output end Proof for theBenchmark
% 2.13/0.64  % (23005)------------------------------
% 2.13/0.64  % (23005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.64  % (23005)Termination reason: Refutation
% 2.13/0.64  
% 2.13/0.64  % (23005)Memory used [KB]: 12025
% 2.13/0.64  % (23005)Time elapsed: 0.211 s
% 2.13/0.64  % (23005)------------------------------
% 2.13/0.64  % (23005)------------------------------
% 2.13/0.64  % (22988)Success in time 0.276 s
%------------------------------------------------------------------------------
