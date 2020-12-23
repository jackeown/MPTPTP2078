%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 200 expanded)
%              Number of leaves         :   20 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  135 ( 295 expanded)
%              Number of equality atoms :   47 ( 150 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1041,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f684,f1040])).

fof(f1040,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f1038,f681,f66,f56])).

fof(f56,plain,
    ( spl3_1
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f66,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f681,plain,
    ( spl3_6
  <=> sK1 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1038,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(superposition,[],[f107,f683])).

fof(f683,plain,
    ( sK1 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f681])).

fof(f107,plain,
    ( ! [X6,X7] : r1_tarski(k10_relat_1(sK2,X6),k10_relat_1(sK2,k3_tarski(k2_enumset1(X6,X6,X6,X7))))
    | ~ spl3_3 ),
    inference(superposition,[],[f49,f88])).

fof(f88,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f68,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f43,f46,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(f68,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f46])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f684,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f679,f61,f681])).

fof(f61,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f679,plain,
    ( sK1 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f667,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f32,f45,f45])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f667,plain,
    ( sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0))
    | ~ spl3_2 ),
    inference(superposition,[],[f131,f176])).

fof(f176,plain,
    ( ! [X0] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK1))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f137,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f137,plain,
    ( ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,sK1))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f63,f111,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f111,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f90,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f90,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(unit_resulting_resolution,[],[f83,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f53,f48])).

fof(f48,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f30,f46])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f53,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f63,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f131,plain,(
    ! [X2,X3] : k3_tarski(k2_enumset1(X2,X2,X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) = X2 ),
    inference(forward_demodulation,[],[f123,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f123,plain,(
    ! [X2,X3] : k3_tarski(k2_enumset1(X2,X2,X2,k1_setfam_1(k2_enumset1(X3,X3,X3,X2)))) = X2 ),
    inference(superposition,[],[f78,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[],[f52,f50])).

fof(f78,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f51,f52])).

fof(f51,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f33,f46,f47])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f69,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f64,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f29,f56])).

fof(f29,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:44:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (19488)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (19485)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (19484)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (19488)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f1041,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f59,f64,f69,f684,f1040])).
% 0.21/0.47  fof(f1040,plain,(
% 0.21/0.47    spl3_1 | ~spl3_3 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f1038,f681,f66,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl3_1 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f681,plain,(
% 0.21/0.47    spl3_6 <=> sK1 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f1038,plain,(
% 0.21/0.47    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | (~spl3_3 | ~spl3_6)),
% 0.21/0.47    inference(superposition,[],[f107,f683])).
% 0.21/0.47  fof(f683,plain,(
% 0.21/0.47    sK1 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f681])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X6,X7] : (r1_tarski(k10_relat_1(sK2,X6),k10_relat_1(sK2,k3_tarski(k2_enumset1(X6,X6,X6,X7))))) ) | ~spl3_3),
% 0.21/0.47    inference(superposition,[],[f49,f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k10_relat_1(sK2,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)))) ) | ~spl3_3),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f68,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f43,f46,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f36,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f35,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f66])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f31,f46])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.47  fof(f684,plain,(
% 0.21/0.47    spl3_6 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f679,f61,f681])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f679,plain,(
% 0.21/0.47    sK1 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl3_2),
% 0.21/0.47    inference(forward_demodulation,[],[f667,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f32,f45,f45])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.47  fof(f667,plain,(
% 0.21/0.47    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) | ~spl3_2),
% 0.21/0.47    inference(superposition,[],[f131,f176])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    ( ! [X0] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK1))) ) | ~spl3_2),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f137,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(sK0,k4_xboole_0(X0,sK1))) ) | ~spl3_2),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f63,f111,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f90,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f83,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 0.21/0.47    inference(superposition,[],[f53,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f30,f46])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.47    inference(rectify,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f42,f46])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k3_tarski(k2_enumset1(X2,X2,X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) = X2) )),
% 0.21/0.47    inference(forward_demodulation,[],[f123,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f37,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f34,f45])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k3_tarski(k2_enumset1(X2,X2,X2,k1_setfam_1(k2_enumset1(X3,X3,X3,X2)))) = X2) )),
% 0.21/0.47    inference(superposition,[],[f78,f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 0.21/0.47    inference(superposition,[],[f52,f50])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 0.21/0.47    inference(forward_demodulation,[],[f51,f52])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f33,f46,f47])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f66])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.21/0.47    inference(negated_conjecture,[],[f15])).
% 0.21/0.47  fof(f15,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f61])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f56])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (19488)------------------------------
% 0.21/0.47  % (19488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19488)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (19488)Memory used [KB]: 6908
% 0.21/0.47  % (19488)Time elapsed: 0.036 s
% 0.21/0.47  % (19488)------------------------------
% 0.21/0.47  % (19488)------------------------------
% 0.21/0.47  % (19493)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (19498)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (19477)Success in time 0.113 s
%------------------------------------------------------------------------------
