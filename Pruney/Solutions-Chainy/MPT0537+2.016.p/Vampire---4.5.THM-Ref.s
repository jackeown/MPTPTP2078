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
% DateTime   : Thu Dec  3 12:49:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  75 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :  104 ( 150 expanded)
%              Number of equality atoms :   40 (  61 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f43,f47,f59,f73,f77,f86,f94])).

fof(f94,plain,
    ( spl1_2
    | ~ spl1_11
    | ~ spl1_13 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl1_2
    | ~ spl1_11
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f38,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)
    | ~ spl1_11
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f88,f76])).

fof(f76,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f75])).

% (1951)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f75,plain,
    ( spl1_11
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f88,plain,
    ( ! [X2] : k1_xboole_0 = k8_relat_1(k4_xboole_0(X2,X2),sK0)
    | ~ spl1_11
    | ~ spl1_13 ),
    inference(superposition,[],[f76,f85])).

fof(f85,plain,
    ( ! [X0,X1] : k4_xboole_0(k8_relat_1(X0,sK0),k8_relat_1(X1,sK0)) = k8_relat_1(k4_xboole_0(X0,X1),sK0)
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl1_13
  <=> ! [X1,X0] : k4_xboole_0(k8_relat_1(X0,sK0),k8_relat_1(X1,sK0)) = k8_relat_1(k4_xboole_0(X0,X1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f38,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl1_2
  <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f86,plain,
    ( spl1_13
    | ~ spl1_1
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f82,f71,f31,f84])).

fof(f31,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f71,plain,
    ( spl1_10
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,X1),X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f82,plain,
    ( ! [X0,X1] : k4_xboole_0(k8_relat_1(X0,sK0),k8_relat_1(X1,sK0)) = k8_relat_1(k4_xboole_0(X0,X1),sK0)
    | ~ spl1_1
    | ~ spl1_10 ),
    inference(unit_resulting_resolution,[],[f33,f72])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,X1),X2)
        | ~ v1_relat_1(X2) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f33,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f77,plain,
    ( spl1_11
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f65,f57,f45,f41,f75])).

fof(f41,plain,
    ( spl1_3
  <=> ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f45,plain,
    ( spl1_4
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f57,plain,
    ( spl1_7
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f65,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f64,f42])).

fof(f42,plain,
    ( ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f64,plain,
    ( ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(superposition,[],[f58,f46])).

fof(f46,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f58,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f73,plain,(
    spl1_10 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f28,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(k6_subset_1(X0,X1),X2) = k4_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f25,f21])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_relat_1)).

fof(f59,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f43,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f39,plain,(
    ~ spl1_2 ),
    inference(avatar_split_clause,[],[f18,f36])).

fof(f18,plain,(
    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(f34,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f17,f31])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 14:34:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (1935)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (1935)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f34,f39,f43,f47,f59,f73,f77,f86,f94])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    spl1_2 | ~spl1_11 | ~spl1_13),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f93])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    $false | (spl1_2 | ~spl1_11 | ~spl1_13)),
% 0.21/0.46    inference(subsumption_resolution,[],[f38,f92])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) | (~spl1_11 | ~spl1_13)),
% 0.21/0.46    inference(forward_demodulation,[],[f88,f76])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl1_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f75])).
% 0.21/0.46  % (1951)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    spl1_11 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    ( ! [X2] : (k1_xboole_0 = k8_relat_1(k4_xboole_0(X2,X2),sK0)) ) | (~spl1_11 | ~spl1_13)),
% 0.21/0.46    inference(superposition,[],[f76,f85])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(k8_relat_1(X0,sK0),k8_relat_1(X1,sK0)) = k8_relat_1(k4_xboole_0(X0,X1),sK0)) ) | ~spl1_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f84])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    spl1_13 <=> ! [X1,X0] : k4_xboole_0(k8_relat_1(X0,sK0),k8_relat_1(X1,sK0)) = k8_relat_1(k4_xboole_0(X0,X1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) | spl1_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    spl1_2 <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    spl1_13 | ~spl1_1 | ~spl1_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f82,f71,f31,f84])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    spl1_1 <=> v1_relat_1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    spl1_10 <=> ! [X1,X0,X2] : (k4_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(k8_relat_1(X0,sK0),k8_relat_1(X1,sK0)) = k8_relat_1(k4_xboole_0(X0,X1),sK0)) ) | (~spl1_1 | ~spl1_10)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f33,f72])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) ) | ~spl1_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f71])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    v1_relat_1(sK0) | ~spl1_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f31])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl1_11 | ~spl1_3 | ~spl1_4 | ~spl1_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f65,f57,f45,f41,f75])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    spl1_3 <=> ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    spl1_4 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    spl1_7 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_7)),
% 0.21/0.46    inference(forward_demodulation,[],[f64,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) ) | ~spl1_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f41])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) ) | (~spl1_4 | ~spl1_7)),
% 0.21/0.46    inference(superposition,[],[f58,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl1_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f45])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl1_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f57])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    spl1_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f29,f71])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f28,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k8_relat_1(k6_subset_1(X0,X1),X2) = k4_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f25,f21])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_relat_1)).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    spl1_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f23,f57])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    spl1_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f45])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.46    inference(rectify,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    spl1_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f41])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ~spl1_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f36])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0)) => (k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.21/0.46    inference(negated_conjecture,[],[f10])).
% 0.21/0.46  fof(f10,conjecture,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl1_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f31])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    v1_relat_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (1935)------------------------------
% 0.21/0.46  % (1935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (1935)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (1935)Memory used [KB]: 6140
% 0.21/0.46  % (1935)Time elapsed: 0.009 s
% 0.21/0.46  % (1935)------------------------------
% 0.21/0.46  % (1935)------------------------------
% 0.21/0.46  % (1936)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (1926)Success in time 0.101 s
%------------------------------------------------------------------------------
