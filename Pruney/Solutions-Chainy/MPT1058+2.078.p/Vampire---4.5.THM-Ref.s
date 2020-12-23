%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:28 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 111 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 250 expanded)
%              Number of equality atoms :   48 (  96 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f48,f75,f83,f102,f108])).

fof(f108,plain,
    ( ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(global_subsumption,[],[f22,f104])).

fof(f104,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(superposition,[],[f82,f101])).

fof(f101,plain,
    ( k10_relat_1(sK0,sK2) = k1_setfam_1(k1_enumset1(sK1,sK1,k10_relat_1(sK0,sK2)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_9
  <=> k10_relat_1(sK0,sK2) = k1_setfam_1(k1_enumset1(sK1,sK1,k10_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f82,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_7
  <=> ! [X1,X0] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f22,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f102,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f97,f72,f99])).

fof(f72,plain,
    ( spl3_6
  <=> k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f97,plain,
    ( k10_relat_1(sK0,sK2) = k1_setfam_1(k1_enumset1(sK1,sK1,k10_relat_1(sK0,sK2)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f90,f59])).

fof(f59,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f58,f25])).

fof(f25,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f58,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f55,f26])).

fof(f26,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f23,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f90,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,k10_relat_1(sK0,sK2))) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | ~ spl3_6 ),
    inference(superposition,[],[f89,f74])).

fof(f74,plain,
    ( k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f89,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(superposition,[],[f77,f59])).

fof(f77,plain,(
    ! [X2,X0,X1] : k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(k6_relat_1(X0),X2))) ),
    inference(unit_resulting_resolution,[],[f23,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f83,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f76,f35,f81])).

fof(f35,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f76,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f37,f33])).

fof(f37,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f75,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f69,f45,f72])).

fof(f45,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f69,plain,
    ( k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f47,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(global_subsumption,[],[f23,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f30,f25])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f47,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f48,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f35])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:36:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (811565056)
% 0.14/0.37  ipcrm: permission denied for id (811597831)
% 0.21/0.40  ipcrm: permission denied for id (811663392)
% 0.21/0.41  ipcrm: permission denied for id (811696171)
% 0.21/0.44  ipcrm: permission denied for id (811794500)
% 0.21/0.45  ipcrm: permission denied for id (811860045)
% 0.21/0.46  ipcrm: permission denied for id (811925596)
% 0.21/0.49  ipcrm: permission denied for id (811958391)
% 0.36/0.57  % (6812)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.36/0.58  % (6812)Refutation not found, incomplete strategy% (6812)------------------------------
% 0.36/0.58  % (6812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.58  % (6812)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.58  
% 0.36/0.58  % (6812)Memory used [KB]: 10618
% 0.36/0.58  % (6812)Time elapsed: 0.004 s
% 0.36/0.58  % (6812)------------------------------
% 0.36/0.58  % (6812)------------------------------
% 0.36/0.58  % (6803)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.36/0.59  % (6818)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.36/0.59  % (6818)Refutation found. Thanks to Tanya!
% 0.36/0.59  % SZS status Theorem for theBenchmark
% 0.36/0.59  % SZS output start Proof for theBenchmark
% 0.36/0.59  fof(f109,plain,(
% 0.36/0.59    $false),
% 0.36/0.59    inference(avatar_sat_refutation,[],[f38,f48,f75,f83,f102,f108])).
% 0.36/0.59  fof(f108,plain,(
% 0.36/0.59    ~spl3_7 | ~spl3_9),
% 0.36/0.59    inference(avatar_contradiction_clause,[],[f107])).
% 0.36/0.59  fof(f107,plain,(
% 0.36/0.59    $false | (~spl3_7 | ~spl3_9)),
% 0.36/0.59    inference(global_subsumption,[],[f22,f104])).
% 0.36/0.59  fof(f104,plain,(
% 0.36/0.59    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) | (~spl3_7 | ~spl3_9)),
% 0.36/0.59    inference(superposition,[],[f82,f101])).
% 0.36/0.59  fof(f101,plain,(
% 0.36/0.59    k10_relat_1(sK0,sK2) = k1_setfam_1(k1_enumset1(sK1,sK1,k10_relat_1(sK0,sK2))) | ~spl3_9),
% 0.36/0.59    inference(avatar_component_clause,[],[f99])).
% 0.36/0.59  fof(f99,plain,(
% 0.36/0.59    spl3_9 <=> k10_relat_1(sK0,sK2) = k1_setfam_1(k1_enumset1(sK1,sK1,k10_relat_1(sK0,sK2)))),
% 0.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.36/0.59  fof(f82,plain,(
% 0.36/0.59    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1)))) ) | ~spl3_7),
% 0.36/0.59    inference(avatar_component_clause,[],[f81])).
% 0.36/0.59  fof(f81,plain,(
% 0.36/0.59    spl3_7 <=> ! [X1,X0] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1)))),
% 0.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.36/0.59  fof(f22,plain,(
% 0.36/0.59    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.36/0.59    inference(cnf_transformation,[],[f18])).
% 0.36/0.59  fof(f18,plain,(
% 0.36/0.59    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.36/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17,f16])).
% 0.36/0.59  fof(f16,plain,(
% 0.36/0.59    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.36/0.59    introduced(choice_axiom,[])).
% 0.36/0.59  fof(f17,plain,(
% 0.36/0.59    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 0.36/0.59    introduced(choice_axiom,[])).
% 0.36/0.59  fof(f11,plain,(
% 0.36/0.59    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.36/0.59    inference(flattening,[],[f10])).
% 0.36/0.59  fof(f10,plain,(
% 0.36/0.59    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.36/0.59    inference(ennf_transformation,[],[f9])).
% 0.36/0.59  fof(f9,negated_conjecture,(
% 0.36/0.59    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.36/0.59    inference(negated_conjecture,[],[f8])).
% 0.36/0.59  fof(f8,conjecture,(
% 0.36/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.36/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 0.36/0.59  fof(f102,plain,(
% 0.36/0.59    spl3_9 | ~spl3_6),
% 0.36/0.59    inference(avatar_split_clause,[],[f97,f72,f99])).
% 0.36/0.59  fof(f72,plain,(
% 0.36/0.59    spl3_6 <=> k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 0.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.36/0.59  fof(f97,plain,(
% 0.36/0.59    k10_relat_1(sK0,sK2) = k1_setfam_1(k1_enumset1(sK1,sK1,k10_relat_1(sK0,sK2))) | ~spl3_6),
% 0.36/0.59    inference(forward_demodulation,[],[f90,f59])).
% 0.36/0.59  fof(f59,plain,(
% 0.36/0.59    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 0.36/0.59    inference(forward_demodulation,[],[f58,f25])).
% 0.36/0.59  fof(f25,plain,(
% 0.36/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.36/0.59    inference(cnf_transformation,[],[f4])).
% 0.36/0.59  fof(f4,axiom,(
% 0.36/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.36/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.36/0.59  fof(f58,plain,(
% 0.36/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 0.36/0.59    inference(forward_demodulation,[],[f55,f26])).
% 0.36/0.59  fof(f26,plain,(
% 0.36/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.36/0.59    inference(cnf_transformation,[],[f4])).
% 0.36/0.59  fof(f55,plain,(
% 0.36/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 0.36/0.59    inference(unit_resulting_resolution,[],[f23,f27])).
% 0.36/0.59  fof(f27,plain,(
% 0.36/0.59    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.36/0.59    inference(cnf_transformation,[],[f12])).
% 0.36/0.59  fof(f12,plain,(
% 0.36/0.59    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.36/0.59    inference(ennf_transformation,[],[f3])).
% 0.36/0.59  fof(f3,axiom,(
% 0.36/0.59    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.36/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.36/0.59  fof(f23,plain,(
% 0.36/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.36/0.59    inference(cnf_transformation,[],[f6])).
% 0.36/0.59  fof(f6,axiom,(
% 0.36/0.59    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.36/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.36/0.59  fof(f90,plain,(
% 0.36/0.59    k1_setfam_1(k1_enumset1(sK1,sK1,k10_relat_1(sK0,sK2))) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | ~spl3_6),
% 0.36/0.59    inference(superposition,[],[f89,f74])).
% 0.36/0.59  fof(f74,plain,(
% 0.36/0.59    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl3_6),
% 0.36/0.59    inference(avatar_component_clause,[],[f72])).
% 0.36/0.59  fof(f89,plain,(
% 0.36/0.59    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k1_setfam_1(k1_enumset1(X1,X1,X0))) )),
% 0.36/0.59    inference(superposition,[],[f77,f59])).
% 0.36/0.59  fof(f77,plain,(
% 0.36/0.59    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(k6_relat_1(X0),X2)))) )),
% 0.36/0.59    inference(unit_resulting_resolution,[],[f23,f33])).
% 0.36/0.59  fof(f33,plain,(
% 0.36/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1)))) )),
% 0.36/0.59    inference(definition_unfolding,[],[f31,f32])).
% 0.36/0.59  fof(f32,plain,(
% 0.36/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.36/0.59    inference(definition_unfolding,[],[f28,f29])).
% 0.36/0.59  fof(f29,plain,(
% 0.36/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.36/0.59    inference(cnf_transformation,[],[f1])).
% 0.36/0.59  fof(f1,axiom,(
% 0.36/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.36/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.36/0.59  fof(f28,plain,(
% 0.36/0.59    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.36/0.59    inference(cnf_transformation,[],[f2])).
% 0.36/0.59  fof(f2,axiom,(
% 0.36/0.59    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.36/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.36/0.59  fof(f31,plain,(
% 0.36/0.59    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.36/0.59    inference(cnf_transformation,[],[f15])).
% 0.36/0.59  fof(f15,plain,(
% 0.36/0.59    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.36/0.59    inference(ennf_transformation,[],[f7])).
% 0.36/0.59  fof(f7,axiom,(
% 0.36/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.36/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 0.36/0.59  fof(f83,plain,(
% 0.36/0.59    spl3_7 | ~spl3_1),
% 0.36/0.59    inference(avatar_split_clause,[],[f76,f35,f81])).
% 0.36/0.59  fof(f35,plain,(
% 0.36/0.59    spl3_1 <=> v1_relat_1(sK0)),
% 0.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.36/0.59  fof(f76,plain,(
% 0.36/0.59    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1)))) ) | ~spl3_1),
% 0.36/0.59    inference(unit_resulting_resolution,[],[f37,f33])).
% 0.36/0.59  fof(f37,plain,(
% 0.36/0.59    v1_relat_1(sK0) | ~spl3_1),
% 0.36/0.59    inference(avatar_component_clause,[],[f35])).
% 0.36/0.59  fof(f75,plain,(
% 0.36/0.59    spl3_6 | ~spl3_3),
% 0.36/0.59    inference(avatar_split_clause,[],[f69,f45,f72])).
% 0.36/0.59  fof(f45,plain,(
% 0.36/0.59    spl3_3 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.36/0.59  fof(f69,plain,(
% 0.36/0.59    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl3_3),
% 0.36/0.59    inference(unit_resulting_resolution,[],[f47,f68])).
% 0.36/0.59  fof(f68,plain,(
% 0.36/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.36/0.59    inference(global_subsumption,[],[f23,f67])).
% 0.36/0.59  fof(f67,plain,(
% 0.36/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.36/0.59    inference(superposition,[],[f30,f25])).
% 0.36/0.59  fof(f30,plain,(
% 0.36/0.59    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.36/0.59    inference(cnf_transformation,[],[f14])).
% 0.36/0.59  fof(f14,plain,(
% 0.36/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.36/0.59    inference(flattening,[],[f13])).
% 0.36/0.59  fof(f13,plain,(
% 0.36/0.59    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.36/0.59    inference(ennf_transformation,[],[f5])).
% 0.36/0.59  fof(f5,axiom,(
% 0.36/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.36/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.36/0.59  fof(f47,plain,(
% 0.36/0.59    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_3),
% 0.36/0.59    inference(avatar_component_clause,[],[f45])).
% 0.36/0.59  fof(f48,plain,(
% 0.36/0.59    spl3_3),
% 0.36/0.59    inference(avatar_split_clause,[],[f21,f45])).
% 0.36/0.59  fof(f21,plain,(
% 0.36/0.59    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.36/0.59    inference(cnf_transformation,[],[f18])).
% 0.36/0.59  fof(f38,plain,(
% 0.36/0.59    spl3_1),
% 0.36/0.59    inference(avatar_split_clause,[],[f19,f35])).
% 0.36/0.59  fof(f19,plain,(
% 0.36/0.59    v1_relat_1(sK0)),
% 0.36/0.59    inference(cnf_transformation,[],[f18])).
% 0.36/0.59  % SZS output end Proof for theBenchmark
% 0.36/0.59  % (6818)------------------------------
% 0.36/0.59  % (6818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.59  % (6818)Termination reason: Refutation
% 0.36/0.59  
% 0.36/0.59  % (6818)Memory used [KB]: 10618
% 0.36/0.59  % (6818)Time elapsed: 0.059 s
% 0.36/0.59  % (6818)------------------------------
% 0.36/0.59  % (6818)------------------------------
% 0.36/0.60  % (6627)Success in time 0.237 s
%------------------------------------------------------------------------------
