%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  46 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   70 (  98 expanded)
%              Number of equality atoms :   24 (  35 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f27,f31,f36,f40])).

fof(f40,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f39])).

fof(f39,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f38])).

fof(f38,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f37,f26])).

fof(f26,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_3
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f37,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(sK1,k3_xboole_0(sK0,sK0))
    | spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f17,f35])).

fof(f35,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k3_xboole_0(X0,X1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_5
  <=> ! [X1,X0] : k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f17,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl2_1
  <=> k2_wellord1(sK1,sK0) = k2_wellord1(k2_wellord1(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f36,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f32,f29,f20,f34])).

fof(f20,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f29,plain,
    ( spl2_4
  <=> ! [X1,X0,X2] :
        ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f32,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k3_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f30,f22])).

fof(f22,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f30,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f31,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

fof(f27,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f23,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f10,f20])).

fof(f10,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
        & v1_relat_1(X1) )
   => ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_wellord1)).

fof(f18,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f11,f15])).

fof(f11,plain,(
    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:57:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (23383)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  % (23382)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (23381)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (23381)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f18,f23,f27,f31,f36,f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    spl2_1 | ~spl2_3 | ~spl2_5),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    $false | (spl2_1 | ~spl2_3 | ~spl2_5)),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0) | (spl2_1 | ~spl2_3 | ~spl2_5)),
% 0.22/0.44    inference(forward_demodulation,[],[f37,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl2_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    spl2_3 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,k3_xboole_0(sK0,sK0)) | (spl2_1 | ~spl2_5)),
% 0.22/0.44    inference(superposition,[],[f17,f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k3_xboole_0(X0,X1))) ) | ~spl2_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    spl2_5 <=> ! [X1,X0] : k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k3_xboole_0(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) | spl2_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    spl2_1 <=> k2_wellord1(sK1,sK0) = k2_wellord1(k2_wellord1(sK1,sK0),sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    spl2_5 | ~spl2_2 | ~spl2_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f32,f29,f20,f34])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    spl2_2 <=> v1_relat_1(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    spl2_4 <=> ! [X1,X0,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k3_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_4)),
% 0.22/0.44    inference(resolution,[],[f30,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    v1_relat_1(sK1) | ~spl2_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f20])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))) ) | ~spl2_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f29])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    spl2_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f13,f29])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    spl2_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f12,f25])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,plain,(
% 0.22/0.44    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.44    inference(rectify,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    spl2_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f10,f20])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    v1_relat_1(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) & v1_relat_1(sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0,X1] : (k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0) & v1_relat_1(X1)) => (k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) & v1_relat_1(sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ? [X0,X1] : (k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0) & v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0))),
% 0.22/0.44    inference(negated_conjecture,[],[f3])).
% 0.22/0.44  fof(f3,conjecture,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_wellord1)).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ~spl2_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f11,f15])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (23381)------------------------------
% 0.22/0.44  % (23381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (23381)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (23381)Memory used [KB]: 10490
% 0.22/0.44  % (23381)Time elapsed: 0.004 s
% 0.22/0.44  % (23381)------------------------------
% 0.22/0.44  % (23381)------------------------------
% 0.22/0.44  % (23375)Success in time 0.078 s
%------------------------------------------------------------------------------
