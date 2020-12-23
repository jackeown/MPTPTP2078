%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 133 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :    7
%              Number of atoms          :  172 ( 292 expanded)
%              Number of equality atoms :   49 (  89 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f596,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f47,f116,f183,f208,f212,f224,f245,f257,f424,f554,f595])).

fof(f595,plain,
    ( ~ spl2_33
    | spl2_40 ),
    inference(avatar_contradiction_clause,[],[f591])).

fof(f591,plain,
    ( $false
    | ~ spl2_33
    | spl2_40 ),
    inference(unit_resulting_resolution,[],[f423,f553])).

fof(f553,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1))))
    | spl2_40 ),
    inference(avatar_component_clause,[],[f551])).

fof(f551,plain,
    ( spl2_40
  <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f423,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl2_33
  <=> ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f554,plain,
    ( ~ spl2_40
    | spl2_21
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f246,f242,f180,f551])).

fof(f180,plain,
    ( spl2_21
  <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f242,plain,
    ( spl2_26
  <=> k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f246,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1))))
    | spl2_21
    | ~ spl2_26 ),
    inference(superposition,[],[f182,f244])).

fof(f244,plain,
    ( k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f242])).

fof(f182,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    | spl2_21 ),
    inference(avatar_component_clause,[],[f180])).

fof(f424,plain,
    ( spl2_33
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f403,f255,f114,f33,f422])).

fof(f33,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f114,plain,
    ( spl2_11
  <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f255,plain,
    ( spl2_28
  <=> ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k7_relat_1(sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f403,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f288,f256])).

fof(f256,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f255])).

fof(f288,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f35,f115,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f115,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),X0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f35,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f257,plain,
    ( spl2_28
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f66,f45,f255])).

fof(f45,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k7_relat_1(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f66,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f46,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f46,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK0,X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f245,plain,
    ( spl2_26
    | ~ spl2_23
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f231,f222,f210,f242])).

fof(f210,plain,
    ( spl2_23
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f222,plain,
    ( spl2_24
  <=> ! [X1] : k1_setfam_1(k2_tarski(X1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f231,plain,
    ( k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl2_23
    | ~ spl2_24 ),
    inference(superposition,[],[f223,f211])).

fof(f211,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f210])).

fof(f223,plain,
    ( ! [X1] : k1_setfam_1(k2_tarski(X1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f222])).

fof(f224,plain,
    ( spl2_24
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f213,f206,f222])).

fof(f206,plain,
    ( spl2_22
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f213,plain,
    ( ! [X1] : k1_setfam_1(k2_tarski(X1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X1))
    | ~ spl2_22 ),
    inference(superposition,[],[f207,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f207,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f206])).

fof(f212,plain,
    ( spl2_23
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f185,f38,f210])).

fof(f38,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f185,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f40,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f40,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f208,plain,
    ( spl2_22
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f184,f33,f206])).

fof(f184,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f35,f31])).

fof(f183,plain,(
    ~ spl2_21 ),
    inference(avatar_split_clause,[],[f22,f180])).

fof(f22,plain,(
    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(f116,plain,
    ( spl2_11
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f93,f33,f114])).

fof(f93,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),X0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f35,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f47,plain,
    ( spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f42,f33,f45])).

fof(f42,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK0,X0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f35,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f41,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f20,f33])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (8042)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.44  % (8042)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f596,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f36,f41,f47,f116,f183,f208,f212,f224,f245,f257,f424,f554,f595])).
% 0.21/0.44  fof(f595,plain,(
% 0.21/0.44    ~spl2_33 | spl2_40),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f591])).
% 0.21/0.44  fof(f591,plain,(
% 0.21/0.44    $false | (~spl2_33 | spl2_40)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f423,f553])).
% 0.21/0.44  fof(f553,plain,(
% 0.21/0.44    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1)))) | spl2_40),
% 0.21/0.44    inference(avatar_component_clause,[],[f551])).
% 0.21/0.44  fof(f551,plain,(
% 0.21/0.44    spl2_40 <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.21/0.44  fof(f423,plain,(
% 0.21/0.44    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) ) | ~spl2_33),
% 0.21/0.44    inference(avatar_component_clause,[],[f422])).
% 0.21/0.44  fof(f422,plain,(
% 0.21/0.44    spl2_33 <=> ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.44  fof(f554,plain,(
% 0.21/0.44    ~spl2_40 | spl2_21 | ~spl2_26),
% 0.21/0.44    inference(avatar_split_clause,[],[f246,f242,f180,f551])).
% 0.21/0.44  fof(f180,plain,(
% 0.21/0.44    spl2_21 <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.44  fof(f242,plain,(
% 0.21/0.44    spl2_26 <=> k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.44  fof(f246,plain,(
% 0.21/0.44    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1)))) | (spl2_21 | ~spl2_26)),
% 0.21/0.44    inference(superposition,[],[f182,f244])).
% 0.21/0.44  fof(f244,plain,(
% 0.21/0.44    k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1))) | ~spl2_26),
% 0.21/0.44    inference(avatar_component_clause,[],[f242])).
% 0.21/0.44  fof(f182,plain,(
% 0.21/0.44    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) | spl2_21),
% 0.21/0.44    inference(avatar_component_clause,[],[f180])).
% 0.21/0.44  fof(f424,plain,(
% 0.21/0.44    spl2_33 | ~spl2_1 | ~spl2_11 | ~spl2_28),
% 0.21/0.44    inference(avatar_split_clause,[],[f403,f255,f114,f33,f422])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    spl2_1 <=> v1_relat_1(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    spl2_11 <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.44  fof(f255,plain,(
% 0.21/0.44    spl2_28 <=> ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k7_relat_1(sK0,X0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.44  fof(f403,plain,(
% 0.21/0.44    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) ) | (~spl2_1 | ~spl2_11 | ~spl2_28)),
% 0.21/0.44    inference(forward_demodulation,[],[f288,f256])).
% 0.21/0.44  fof(f256,plain,(
% 0.21/0.44    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k7_relat_1(sK0,X0)))) ) | ~spl2_28),
% 0.21/0.44    inference(avatar_component_clause,[],[f255])).
% 0.21/0.44  fof(f288,plain,(
% 0.21/0.44    ( ! [X0] : (k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) ) | (~spl2_1 | ~spl2_11)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f35,f115,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(flattening,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),X0)) ) | ~spl2_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f114])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    v1_relat_1(sK0) | ~spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f33])).
% 0.21/0.44  fof(f257,plain,(
% 0.21/0.44    spl2_28 | ~spl2_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f66,f45,f255])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl2_3 <=> ! [X0] : v1_relat_1(k7_relat_1(sK0,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k7_relat_1(sK0,X0)))) ) | ~spl2_3),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f46,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k7_relat_1(sK0,X0))) ) | ~spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f45])).
% 0.21/0.44  fof(f245,plain,(
% 0.21/0.44    spl2_26 | ~spl2_23 | ~spl2_24),
% 0.21/0.44    inference(avatar_split_clause,[],[f231,f222,f210,f242])).
% 0.21/0.44  fof(f210,plain,(
% 0.21/0.44    spl2_23 <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.44  fof(f222,plain,(
% 0.21/0.44    spl2_24 <=> ! [X1] : k1_setfam_1(k2_tarski(X1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.44  fof(f231,plain,(
% 0.21/0.44    k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1))) | (~spl2_23 | ~spl2_24)),
% 0.21/0.44    inference(superposition,[],[f223,f211])).
% 0.21/0.44  fof(f211,plain,(
% 0.21/0.44    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) ) | ~spl2_23),
% 0.21/0.44    inference(avatar_component_clause,[],[f210])).
% 0.21/0.44  fof(f223,plain,(
% 0.21/0.44    ( ! [X1] : (k1_setfam_1(k2_tarski(X1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X1))) ) | ~spl2_24),
% 0.21/0.44    inference(avatar_component_clause,[],[f222])).
% 0.21/0.44  fof(f224,plain,(
% 0.21/0.44    spl2_24 | ~spl2_22),
% 0.21/0.44    inference(avatar_split_clause,[],[f213,f206,f222])).
% 0.21/0.44  fof(f206,plain,(
% 0.21/0.44    spl2_22 <=> ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.44  fof(f213,plain,(
% 0.21/0.44    ( ! [X1] : (k1_setfam_1(k2_tarski(X1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,X1))) ) | ~spl2_22),
% 0.21/0.44    inference(superposition,[],[f207,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f24,f25,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.44  fof(f207,plain,(
% 0.21/0.44    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0))) ) | ~spl2_22),
% 0.21/0.44    inference(avatar_component_clause,[],[f206])).
% 0.21/0.44  fof(f212,plain,(
% 0.21/0.44    spl2_23 | ~spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f185,f38,f210])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f185,plain,(
% 0.21/0.44    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) ) | ~spl2_2),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f40,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f28,f25])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f38])).
% 0.21/0.44  fof(f208,plain,(
% 0.21/0.44    spl2_22 | ~spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f184,f33,f206])).
% 0.21/0.44  fof(f184,plain,(
% 0.21/0.44    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0))) ) | ~spl2_1),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f35,f31])).
% 0.21/0.44  fof(f183,plain,(
% 0.21/0.44    ~spl2_21),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f180])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    (k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f18,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ? [X1] : (k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))) & v1_relat_1(X1)) => (k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f8])).
% 0.21/0.44  fof(f8,conjecture,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    spl2_11 | ~spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f93,f33,f114])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),X0)) ) | ~spl2_1),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f35,f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl2_3 | ~spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f42,f33,f45])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k7_relat_1(sK0,X0))) ) | ~spl2_1),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f35,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f38])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f33])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    v1_relat_1(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (8042)------------------------------
% 0.21/0.44  % (8042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (8042)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (8042)Memory used [KB]: 11385
% 0.21/0.44  % (8042)Time elapsed: 0.022 s
% 0.21/0.44  % (8042)------------------------------
% 0.21/0.44  % (8042)------------------------------
% 0.21/0.45  % (8024)Success in time 0.089 s
%------------------------------------------------------------------------------
