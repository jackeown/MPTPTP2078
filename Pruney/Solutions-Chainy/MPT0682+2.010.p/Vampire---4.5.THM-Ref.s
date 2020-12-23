%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 106 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  104 ( 174 expanded)
%              Number of equality atoms :   54 (  89 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f64,f252])).

fof(f252,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f250,f82])).

fof(f82,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k9_relat_1(sK2,X1)) = k9_relat_1(k8_relat_1(X0,sK2),X1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f77,f55])).

fof(f55,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f48,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f48,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f77,plain,
    ( ! [X0,X1] : k9_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1) = k9_relat_1(k6_relat_1(X0),k9_relat_1(sK2,X1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f48,f25,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f250,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k9_relat_1(k6_relat_1(sK0),k9_relat_1(sK2,sK1))
    | spl3_3 ),
    inference(superposition,[],[f63,f87])).

fof(f87,plain,(
    ! [X2,X3] : k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)) = k9_relat_1(k6_relat_1(X2),X3) ),
    inference(forward_demodulation,[],[f84,f72])).

fof(f72,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f71,f56])).

fof(f56,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(unit_resulting_resolution,[],[f25,f32])).

fof(f71,plain,(
    ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f68,f27])).

fof(f27,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f68,plain,(
    ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f25,f25,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f84,plain,(
    ! [X2,X3] : k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)) = k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))) ),
    inference(superposition,[],[f27,f59])).

fof(f59,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f44,f56])).

fof(f44,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f63,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k9_relat_1(sK2,sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_3
  <=> k9_relat_1(k8_relat_1(sK0,sK2),sK1) = k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f64,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f43,f61])).

fof(f43,plain,(
    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k9_relat_1(sK2,sK1))) ),
    inference(definition_unfolding,[],[f24,f42])).

fof(f24,plain,(
    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_funct_1)).

fof(f49,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f46])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:58:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (32470)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.43  % (32475)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.45  % (32475)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f253,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f49,f64,f252])).
% 0.21/0.45  fof(f252,plain,(
% 0.21/0.45    ~spl3_1 | spl3_3),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f251])).
% 0.21/0.45  fof(f251,plain,(
% 0.21/0.45    $false | (~spl3_1 | spl3_3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f250,f82])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k9_relat_1(sK2,X1)) = k9_relat_1(k8_relat_1(X0,sK2),X1)) ) | ~spl3_1),
% 0.21/0.45    inference(forward_demodulation,[],[f77,f55])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) ) | ~spl3_1),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f48,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    v1_relat_1(sK2) | ~spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    spl3_1 <=> v1_relat_1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k9_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1) = k9_relat_1(k6_relat_1(X0),k9_relat_1(sK2,X1))) ) | ~spl3_1),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f48,f25,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.45  fof(f250,plain,(
% 0.21/0.45    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k9_relat_1(k6_relat_1(sK0),k9_relat_1(sK2,sK1)) | spl3_3),
% 0.21/0.45    inference(superposition,[],[f63,f87])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)) = k9_relat_1(k6_relat_1(X2),X3)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f84,f72])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f71,f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f25,f32])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f68,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))) )),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f25,f25,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)) = k2_relat_1(k8_relat_1(X2,k6_relat_1(X3)))) )),
% 0.21/0.45    inference(superposition,[],[f27,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.21/0.45    inference(backward_demodulation,[],[f44,f56])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f31,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f29,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f30,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f34,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f35,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f36,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,axiom,(
% 0.21/0.45    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k9_relat_1(sK2,sK1))) | spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f61])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl3_3 <=> k9_relat_1(k8_relat_1(sK0,sK2),sK1) = k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k9_relat_1(sK2,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ~spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f43,f61])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k9_relat_1(sK2,sK1)))),
% 0.21/0.45    inference(definition_unfolding,[],[f24,f42])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.45    inference(flattening,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.21/0.45    inference(negated_conjecture,[],[f13])).
% 0.21/0.45  fof(f13,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_funct_1)).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f46])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    v1_relat_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (32475)------------------------------
% 0.21/0.45  % (32475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (32475)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (32475)Memory used [KB]: 10874
% 0.21/0.45  % (32475)Time elapsed: 0.021 s
% 0.21/0.45  % (32475)------------------------------
% 0.21/0.45  % (32475)------------------------------
% 0.21/0.45  % (32459)Success in time 0.099 s
%------------------------------------------------------------------------------
