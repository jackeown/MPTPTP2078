%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  38 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   52 (  70 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f16,f21,f26,f31,f35])).

fof(f35,plain,
    ( spl2_1
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f34])).

fof(f34,plain,
    ( $false
    | spl2_1
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f33])).

fof(f33,plain,
    ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1)
    | spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f15,f30])).

fof(f30,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_4
  <=> ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f15,plain,
    ( k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f13])).

fof(f13,plain,
    ( spl2_1
  <=> k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f31,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f27,f24,f29])).

fof(f24,plain,
    ( spl2_3
  <=> ! [X1,X0] : k8_relat_1(X0,k8_relat_1(X1,sK1)) = k8_relat_1(k3_xboole_0(X0,X1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f27,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))
    | ~ spl2_3 ),
    inference(superposition,[],[f25,f10])).

fof(f10,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f25,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK1)) = k8_relat_1(k3_xboole_0(X0,X1),sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f24])).

fof(f26,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f22,f18,f24])).

fof(f18,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f22,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK1)) = k8_relat_1(k3_xboole_0(X0,X1),sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f11,f20])).

fof(f20,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f18])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(f21,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f8,f18])).

fof(f8,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_relat_1)).

fof(f16,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f9,f13])).

fof(f9,plain,(
    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (32016)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.13/0.41  % (32008)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.13/0.41  % (32012)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (32013)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.41  % (32008)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f16,f21,f26,f31,f35])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    spl2_1 | ~spl2_4),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f34])).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    $false | (spl2_1 | ~spl2_4)),
% 0.21/0.41    inference(trivial_inequality_removal,[],[f33])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1) | (spl2_1 | ~spl2_4)),
% 0.21/0.41    inference(superposition,[],[f15,f30])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    ( ! [X0] : (k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))) ) | ~spl2_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f29])).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    spl2_4 <=> ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) | spl2_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    spl2_1 <=> k8_relat_1(sK0,sK1) = k8_relat_1(sK0,k8_relat_1(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    spl2_4 | ~spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f24,f29])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    spl2_3 <=> ! [X1,X0] : k8_relat_1(X0,k8_relat_1(X1,sK1)) = k8_relat_1(k3_xboole_0(X0,X1),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0] : (k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))) ) | ~spl2_3),
% 0.21/0.42    inference(superposition,[],[f25,f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,plain,(
% 0.21/0.42    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.42    inference(rectify,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK1)) = k8_relat_1(k3_xboole_0(X0,X1),sK1)) ) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f24])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    spl2_3 | ~spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f18,f24])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK1)) = k8_relat_1(k3_xboole_0(X0,X1),sK1)) ) | ~spl2_2),
% 0.21/0.42    inference(resolution,[],[f11,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f18])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f8,f18])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    v1_relat_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0,X1] : (k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1)) & v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)))),
% 0.21/0.42    inference(negated_conjecture,[],[f3])).
% 0.21/0.42  fof(f3,conjecture,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_relat_1)).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f9,f13])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (32008)------------------------------
% 0.21/0.42  % (32008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (32008)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (32008)Memory used [KB]: 10490
% 0.21/0.42  % (32008)Time elapsed: 0.004 s
% 0.21/0.42  % (32008)------------------------------
% 0.21/0.42  % (32008)------------------------------
% 0.21/0.42  % (32006)Success in time 0.062 s
%------------------------------------------------------------------------------
