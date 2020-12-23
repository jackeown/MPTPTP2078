%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  81 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 164 expanded)
%              Number of equality atoms :   40 (  68 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f62,f72,f82])).

fof(f82,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f80,f69,f42,f32])).

fof(f32,plain,
    ( spl2_1
  <=> sK0 = k2_relat_1(k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f42,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f69,plain,
    ( spl2_6
  <=> sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f80,plain,
    ( sK0 = k2_relat_1(k8_relat_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f71,f75])).

fof(f75,plain,
    ( ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK1)))
    | ~ spl2_3 ),
    inference(superposition,[],[f73,f28])).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f20,f22,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f73,plain,
    ( ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k1_setfam_1(k1_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),X0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f44,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f44,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f71,plain,
    ( sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK1)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f72,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f67,f58,f69])).

fof(f58,plain,
    ( spl2_5
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f67,plain,
    ( sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK1)))
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f66,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f66,plain,
    ( k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_5 ),
    inference(superposition,[],[f29,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f27])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f62,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f54,f37,f58])).

fof(f37,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f54,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f26,f39])).

fof(f39,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f45,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK0 != k2_relat_1(k8_relat_1(sK0,sK1))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(k8_relat_1(X0,X1)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK0 != k2_relat_1(k8_relat_1(sK0,sK1))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:44:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.40  % (15911)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.41  % (15917)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.41  % (15917)Refutation found. Thanks to Tanya!
% 0.22/0.41  % SZS status Theorem for theBenchmark
% 0.22/0.41  % SZS output start Proof for theBenchmark
% 0.22/0.41  fof(f83,plain,(
% 0.22/0.41    $false),
% 0.22/0.41    inference(avatar_sat_refutation,[],[f35,f40,f45,f62,f72,f82])).
% 0.22/0.41  fof(f82,plain,(
% 0.22/0.41    spl2_1 | ~spl2_3 | ~spl2_6),
% 0.22/0.41    inference(avatar_split_clause,[],[f80,f69,f42,f32])).
% 0.22/0.41  fof(f32,plain,(
% 0.22/0.41    spl2_1 <=> sK0 = k2_relat_1(k8_relat_1(sK0,sK1))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.41  fof(f42,plain,(
% 0.22/0.41    spl2_3 <=> v1_relat_1(sK1)),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.41  fof(f69,plain,(
% 0.22/0.41    spl2_6 <=> sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK1)))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.41  fof(f80,plain,(
% 0.22/0.41    sK0 = k2_relat_1(k8_relat_1(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 0.22/0.41    inference(superposition,[],[f71,f75])).
% 0.22/0.41  fof(f75,plain,(
% 0.22/0.41    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK1)) = k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK1)))) ) | ~spl2_3),
% 0.22/0.41    inference(superposition,[],[f73,f28])).
% 0.22/0.41  fof(f28,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.22/0.41    inference(definition_unfolding,[],[f20,f22,f22])).
% 0.22/0.41  fof(f22,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f5])).
% 0.22/0.41  fof(f5,axiom,(
% 0.22/0.41    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.41  fof(f20,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f4])).
% 0.22/0.41  fof(f4,axiom,(
% 0.22/0.41    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.41  fof(f73,plain,(
% 0.22/0.41    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK1)) = k1_setfam_1(k1_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),X0))) ) | ~spl2_3),
% 0.22/0.41    inference(unit_resulting_resolution,[],[f44,f30])).
% 0.22/0.41  fof(f30,plain,(
% 0.22/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0))) )),
% 0.22/0.41    inference(definition_unfolding,[],[f24,f27])).
% 0.22/0.41  fof(f27,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.41    inference(definition_unfolding,[],[f21,f22])).
% 0.22/0.41  fof(f21,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.41    inference(cnf_transformation,[],[f6])).
% 0.22/0.41  fof(f6,axiom,(
% 0.22/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.41  fof(f24,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f12])).
% 0.22/0.41  fof(f12,plain,(
% 0.22/0.41    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.41    inference(ennf_transformation,[],[f7])).
% 0.22/0.41  fof(f7,axiom,(
% 0.22/0.41    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 0.22/0.41  fof(f44,plain,(
% 0.22/0.41    v1_relat_1(sK1) | ~spl2_3),
% 0.22/0.41    inference(avatar_component_clause,[],[f42])).
% 0.22/0.41  fof(f71,plain,(
% 0.22/0.41    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK1))) | ~spl2_6),
% 0.22/0.41    inference(avatar_component_clause,[],[f69])).
% 0.22/0.41  fof(f72,plain,(
% 0.22/0.41    spl2_6 | ~spl2_5),
% 0.22/0.41    inference(avatar_split_clause,[],[f67,f58,f69])).
% 0.22/0.41  fof(f58,plain,(
% 0.22/0.41    spl2_5 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.41  fof(f67,plain,(
% 0.22/0.41    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK1))) | ~spl2_5),
% 0.22/0.41    inference(forward_demodulation,[],[f66,f19])).
% 0.22/0.41  fof(f19,plain,(
% 0.22/0.41    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.41    inference(cnf_transformation,[],[f2])).
% 0.22/0.41  fof(f2,axiom,(
% 0.22/0.41    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.41  fof(f66,plain,(
% 0.22/0.41    k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0) | ~spl2_5),
% 0.22/0.41    inference(superposition,[],[f29,f60])).
% 0.22/0.41  fof(f60,plain,(
% 0.22/0.41    k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1)) | ~spl2_5),
% 0.22/0.41    inference(avatar_component_clause,[],[f58])).
% 0.22/0.41  fof(f29,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.41    inference(definition_unfolding,[],[f23,f27])).
% 0.22/0.41  fof(f23,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f3])).
% 0.22/0.41  fof(f3,axiom,(
% 0.22/0.41    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.41  fof(f62,plain,(
% 0.22/0.41    spl2_5 | ~spl2_2),
% 0.22/0.41    inference(avatar_split_clause,[],[f54,f37,f58])).
% 0.22/0.41  fof(f37,plain,(
% 0.22/0.41    spl2_2 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.41  fof(f54,plain,(
% 0.22/0.41    k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1)) | ~spl2_2),
% 0.22/0.41    inference(resolution,[],[f26,f39])).
% 0.22/0.41  fof(f39,plain,(
% 0.22/0.41    r1_tarski(sK0,k2_relat_1(sK1)) | ~spl2_2),
% 0.22/0.41    inference(avatar_component_clause,[],[f37])).
% 0.22/0.41  fof(f26,plain,(
% 0.22/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.41    inference(cnf_transformation,[],[f15])).
% 0.22/0.41  fof(f15,plain,(
% 0.22/0.41    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.41    inference(nnf_transformation,[],[f1])).
% 0.22/0.41  fof(f1,axiom,(
% 0.22/0.41    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.41  fof(f45,plain,(
% 0.22/0.41    spl2_3),
% 0.22/0.41    inference(avatar_split_clause,[],[f16,f42])).
% 0.22/0.41  fof(f16,plain,(
% 0.22/0.41    v1_relat_1(sK1)),
% 0.22/0.41    inference(cnf_transformation,[],[f14])).
% 0.22/0.41  fof(f14,plain,(
% 0.22/0.41    sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.22/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13])).
% 0.22/0.41  fof(f13,plain,(
% 0.22/0.41    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1)) => (sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.22/0.41    introduced(choice_axiom,[])).
% 0.22/0.41  fof(f11,plain,(
% 0.22/0.41    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1))),
% 0.22/0.41    inference(flattening,[],[f10])).
% 0.22/0.41  fof(f10,plain,(
% 0.22/0.41    ? [X0,X1] : ((k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.41    inference(ennf_transformation,[],[f9])).
% 0.22/0.41  fof(f9,negated_conjecture,(
% 0.22/0.41    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.22/0.41    inference(negated_conjecture,[],[f8])).
% 0.22/0.41  fof(f8,conjecture,(
% 0.22/0.41    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).
% 0.22/0.41  fof(f40,plain,(
% 0.22/0.41    spl2_2),
% 0.22/0.41    inference(avatar_split_clause,[],[f17,f37])).
% 0.22/0.41  fof(f17,plain,(
% 0.22/0.41    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.41    inference(cnf_transformation,[],[f14])).
% 0.22/0.41  fof(f35,plain,(
% 0.22/0.41    ~spl2_1),
% 0.22/0.41    inference(avatar_split_clause,[],[f18,f32])).
% 0.22/0.41  fof(f18,plain,(
% 0.22/0.41    sK0 != k2_relat_1(k8_relat_1(sK0,sK1))),
% 0.22/0.41    inference(cnf_transformation,[],[f14])).
% 0.22/0.41  % SZS output end Proof for theBenchmark
% 0.22/0.41  % (15917)------------------------------
% 0.22/0.41  % (15917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.41  % (15917)Termination reason: Refutation
% 0.22/0.41  
% 0.22/0.41  % (15917)Memory used [KB]: 6140
% 0.22/0.41  % (15917)Time elapsed: 0.004 s
% 0.22/0.41  % (15917)------------------------------
% 0.22/0.41  % (15917)------------------------------
% 0.22/0.42  % (15910)Success in time 0.056 s
%------------------------------------------------------------------------------
