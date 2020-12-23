%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  59 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f34,f47])).

fof(f47,plain,
    ( spl1_1
    | ~ spl1_3 ),
    inference(avatar_contradiction_clause,[],[f43])).

fof(f43,plain,
    ( $false
    | spl1_1
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f22,f39])).

fof(f39,plain,
    ( ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f37,f15])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f37,plain,
    ( ! [X0] : k8_relat_1(X0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),X0)))
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f33,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

fof(f33,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl1_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f22,plain,
    ( k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl1_1
  <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f34,plain,
    ( spl1_3
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f29,f25,f31])).

fof(f25,plain,
    ( spl1_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f29,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(superposition,[],[f14,f27])).

fof(f27,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f14,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f28,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f23,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f12,f20])).

fof(f12,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).

fof(f10,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (30886)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.43  % (30886)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f23,f28,f34,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl1_1 | ~spl1_3),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    $false | (spl1_1 | ~spl1_3)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f22,f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | ~spl1_3),
% 0.21/0.43    inference(forward_demodulation,[],[f37,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X0] : (k8_relat_1(X0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),X0)))) ) | ~spl1_3),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f33,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f17,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    v1_relat_1(k1_xboole_0) | ~spl1_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl1_3 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    spl1_1 <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    spl1_3 | ~spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f25,f31])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    spl1_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    v1_relat_1(k1_xboole_0) | ~spl1_2),
% 0.21/0.43    inference(superposition,[],[f14,f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f25])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f13,f25])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ~spl1_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f12,f20])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (30886)------------------------------
% 0.21/0.43  % (30886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (30886)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (30886)Memory used [KB]: 10618
% 0.21/0.43  % (30886)Time elapsed: 0.006 s
% 0.21/0.43  % (30886)------------------------------
% 0.21/0.43  % (30886)------------------------------
% 0.21/0.44  % (30870)Success in time 0.082 s
%------------------------------------------------------------------------------
