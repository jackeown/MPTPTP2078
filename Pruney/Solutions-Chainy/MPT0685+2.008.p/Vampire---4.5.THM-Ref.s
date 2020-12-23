%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 482 expanded)
%              Number of leaves         :   18 ( 158 expanded)
%              Depth                    :   18
%              Number of atoms          :  130 ( 615 expanded)
%              Number of equality atoms :   72 ( 446 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f188,f576])).

fof(f576,plain,
    ( ~ spl3_1
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f575])).

fof(f575,plain,
    ( $false
    | ~ spl3_1
    | spl3_4 ),
    inference(subsumption_resolution,[],[f567,f160])).

fof(f160,plain,
    ( ! [X0,X1] : k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k7_relat_1(sK2,X0),X1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f140,f65])).

fof(f65,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f53,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f53,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f140,plain,
    ( ! [X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f26,f53,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f26,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f567,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,sK1))
    | spl3_4 ),
    inference(superposition,[],[f187,f282])).

fof(f282,plain,(
    ! [X2,X3] : k10_relat_1(k6_relat_1(X3),X2) = k10_relat_1(k6_relat_1(X2),X3) ),
    inference(superposition,[],[f136,f92])).

fof(f92,plain,(
    ! [X2,X3] : k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))) = k10_relat_1(k6_relat_1(X3),X2) ),
    inference(backward_demodulation,[],[f78,f91])).

fof(f91,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f90,f61])).

fof(f61,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(unit_resulting_resolution,[],[f26,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f90,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f87,f28])).

fof(f28,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f87,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f26,f26,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f78,plain,(
    ! [X2,X3] : k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))) = k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))) ),
    inference(forward_demodulation,[],[f72,f71])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(superposition,[],[f29,f64])).

fof(f64,plain,(
    ! [X0,X1] : k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f48,f61])).

fof(f48,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f43])).

% (13359)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f29,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))) ),
    inference(superposition,[],[f28,f64])).

fof(f136,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f129,f29])).

fof(f129,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f26,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(backward_demodulation,[],[f77,f92])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k2_relat_1(k8_relat_1(k2_relat_1(X1),k6_relat_1(X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(backward_demodulation,[],[f49,f71])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f47,f45])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k3_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f187,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl3_4
  <=> k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f188,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f107,f56,f185])).

fof(f56,plain,
    ( spl3_2
  <=> k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f107,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),sK0)
    | spl3_2 ),
    inference(superposition,[],[f58,f93])).

fof(f93,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(backward_demodulation,[],[f76,f92])).

fof(f76,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(backward_demodulation,[],[f45,f71])).

fof(f58,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f59,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f44,f56])).

fof(f44,plain,(
    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))) ),
    inference(definition_unfolding,[],[f25,f43])).

fof(f25,plain,(
    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f54,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (13358)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (13343)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (13350)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (13345)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (13346)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (13351)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (13347)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (13356)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (13344)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (13358)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f577,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f54,f59,f188,f576])).
% 0.20/0.48  fof(f576,plain,(
% 0.20/0.48    ~spl3_1 | spl3_4),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f575])).
% 0.20/0.48  fof(f575,plain,(
% 0.20/0.48    $false | (~spl3_1 | spl3_4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f567,f160])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k7_relat_1(sK2,X0),X1)) ) | ~spl3_1),
% 0.20/0.48    inference(forward_demodulation,[],[f140,f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | ~spl3_1),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f53,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1))) ) | ~spl3_1),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f26,f53,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.48  fof(f567,plain,(
% 0.20/0.48    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,sK1)) | spl3_4),
% 0.20/0.48    inference(superposition,[],[f187,f282])).
% 0.20/0.48  fof(f282,plain,(
% 0.20/0.48    ( ! [X2,X3] : (k10_relat_1(k6_relat_1(X3),X2) = k10_relat_1(k6_relat_1(X2),X3)) )),
% 0.20/0.48    inference(superposition,[],[f136,f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ( ! [X2,X3] : (k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))) = k10_relat_1(k6_relat_1(X3),X2)) )),
% 0.20/0.48    inference(backward_demodulation,[],[f78,f91])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f90,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f26,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f87,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f26,f26,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X2,X3] : (k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))) = k2_relat_1(k8_relat_1(X2,k6_relat_1(X3)))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f72,f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.20/0.48    inference(superposition,[],[f29,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.20/0.48    inference(backward_demodulation,[],[f48,f61])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f46,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f33,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f31,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f32,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f39,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f34,f43])).
% 0.20/0.48  % (13359)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k1_relat_1(k8_relat_1(X2,k6_relat_1(X3)))) )),
% 0.20/0.48    inference(superposition,[],[f28,f64])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f129,f29])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X1)))) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f26,f96])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(X1))) )),
% 0.20/0.48    inference(backward_demodulation,[],[f77,f92])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k2_relat_1(k8_relat_1(k2_relat_1(X1),k6_relat_1(X0))) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(backward_demodulation,[],[f49,f71])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f47,f45])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k3_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f37,f43])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),sK0) | spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f185])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    spl3_4 <=> k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    ~spl3_4 | spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f107,f56,f185])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    spl3_2 <=> k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),sK0) | spl3_2),
% 0.20/0.48    inference(superposition,[],[f58,f93])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k10_relat_1(k6_relat_1(X1),X0)) )),
% 0.20/0.48    inference(backward_demodulation,[],[f76,f92])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.20/0.48    inference(backward_demodulation,[],[f45,f71])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))) | spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f56])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ~spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f44,f56])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),
% 0.20/0.48    inference(definition_unfolding,[],[f25,f43])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1)) & v1_relat_1(X2)) => (k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f14])).
% 0.20/0.48  fof(f14,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f24,f51])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (13358)------------------------------
% 0.20/0.48  % (13358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (13358)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (13349)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (13358)Memory used [KB]: 11257
% 0.20/0.49  % (13358)Time elapsed: 0.067 s
% 0.20/0.49  % (13358)------------------------------
% 0.20/0.49  % (13358)------------------------------
% 0.20/0.49  % (13342)Success in time 0.129 s
%------------------------------------------------------------------------------
