%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:57 EST 2020

% Result     : Theorem 3.08s
% Output     : Refutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 479 expanded)
%              Number of leaves         :   29 ( 166 expanded)
%              Depth                    :   20
%              Number of atoms          :  162 ( 567 expanded)
%              Number of equality atoms :   93 ( 453 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4749,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f166,f251,f4747])).

fof(f4747,plain,
    ( ~ spl2_2
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f4712])).

fof(f4712,plain,
    ( $false
    | ~ spl2_2
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f250,f4571])).

fof(f4571,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0)
    | ~ spl2_2 ),
    inference(superposition,[],[f4056,f4073])).

fof(f4073,plain,
    ( ! [X6] : k7_relat_1(sK1,k1_relat_1(sK1)) = k7_relat_1(sK1,k2_xboole_0(k1_relat_1(sK1),X6))
    | ~ spl2_2 ),
    inference(superposition,[],[f3951,f105])).

fof(f105,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f89,f96,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f96,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f87,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(f87,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f89,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f87,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f3951,plain,
    ( ! [X2,X1] : k7_relat_1(sK1,X1) = k7_relat_1(k7_relat_1(sK1,k2_xboole_0(X1,X2)),X1)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f281,f1090])).

fof(f1090,plain,(
    ! [X6,X5] : k6_subset_1(k2_xboole_0(X5,X6),k6_subset_1(X6,X5)) = X5 ),
    inference(forward_demodulation,[],[f1089,f99])).

fof(f99,plain,(
    ! [X2,X1] : k6_subset_1(X1,X2) = k6_subset_1(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f74,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f74,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(k2_xboole_0(X0,X1),X1) ),
    inference(definition_unfolding,[],[f49,f43,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1089,plain,(
    ! [X6,X5] : k6_subset_1(k2_xboole_0(X5,X6),k6_subset_1(k2_xboole_0(X5,X6),X5)) = X5 ),
    inference(forward_demodulation,[],[f1088,f304])).

fof(f304,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f126,f92])).

fof(f92,plain,(
    ! [X1] : k5_xboole_0(o_0_0_xboole_0,X1) = X1 ),
    inference(superposition,[],[f45,f72])).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f39,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f126,plain,(
    ! [X0,X1] : k5_xboole_0(o_0_0_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f58,f71])).

fof(f71,plain,(
    ! [X0] : o_0_0_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1088,plain,(
    ! [X6,X5] : k6_subset_1(k2_xboole_0(X5,X6),k6_subset_1(k2_xboole_0(X5,X6),X5)) = k5_xboole_0(k2_xboole_0(X5,X6),k5_xboole_0(k2_xboole_0(X5,X6),X5)) ),
    inference(forward_demodulation,[],[f1040,f45])).

fof(f1040,plain,(
    ! [X6,X5] : k6_subset_1(k2_xboole_0(X5,X6),k6_subset_1(k2_xboole_0(X5,X6),X5)) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X5,X6),X5),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f193,f113])).

fof(f113,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f57,f42])).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f193,plain,(
    ! [X2,X1] : k6_subset_1(X1,k6_subset_1(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f177,f44])).

fof(f177,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(forward_demodulation,[],[f77,f76])).

fof(f76,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f51,f69,f43,f43])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f281,plain,
    ( ! [X2,X1] : k7_relat_1(k7_relat_1(sK1,k2_xboole_0(X1,X2)),X1) = k7_relat_1(sK1,k6_subset_1(k2_xboole_0(X1,X2),k6_subset_1(X2,X1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f220,f99])).

fof(f220,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k6_subset_1(X0,k6_subset_1(X0,X1)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f87,f219])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k6_subset_1(X0,k6_subset_1(X0,X1))) ) ),
    inference(forward_demodulation,[],[f78,f76])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f4056,plain,
    ( ! [X2,X1] : k7_relat_1(sK1,X1) = k7_relat_1(k7_relat_1(sK1,k2_xboole_0(X2,X1)),X1)
    | ~ spl2_2 ),
    inference(superposition,[],[f3951,f44])).

fof(f250,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl2_4
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f251,plain,
    ( ~ spl2_4
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f234,f163,f85,f248])).

fof(f163,plain,
    ( spl2_3
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f234,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0)
    | ~ spl2_2
    | spl2_3 ),
    inference(superposition,[],[f165,f220])).

fof(f165,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f163])).

fof(f166,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f159,f80,f163])).

fof(f80,plain,
    ( spl2_1
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f159,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),sK0)))
    | spl2_1 ),
    inference(backward_demodulation,[],[f82,f76])).

fof(f82,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f88,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f83,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f70,f80])).

fof(f70,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    inference(definition_unfolding,[],[f38,f69])).

fof(f38,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:54:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (12662)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (12678)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (12668)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (12664)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (12671)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (12666)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (12676)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (12672)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (12673)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (12663)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (12679)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (12674)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.52  % (12677)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.53  % (12669)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.54  % (12665)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.55  % (12670)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.56  % (12675)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.55/0.57  % (12667)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 3.08/0.78  % (12668)Refutation found. Thanks to Tanya!
% 3.08/0.78  % SZS status Theorem for theBenchmark
% 3.08/0.78  % SZS output start Proof for theBenchmark
% 3.08/0.78  fof(f4749,plain,(
% 3.08/0.78    $false),
% 3.08/0.78    inference(avatar_sat_refutation,[],[f83,f88,f166,f251,f4747])).
% 3.08/0.78  fof(f4747,plain,(
% 3.08/0.78    ~spl2_2 | spl2_4),
% 3.08/0.78    inference(avatar_contradiction_clause,[],[f4712])).
% 3.08/0.78  fof(f4712,plain,(
% 3.08/0.78    $false | (~spl2_2 | spl2_4)),
% 3.08/0.78    inference(unit_resulting_resolution,[],[f250,f4571])).
% 3.08/0.78  fof(f4571,plain,(
% 3.08/0.78    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0)) ) | ~spl2_2),
% 3.08/0.78    inference(superposition,[],[f4056,f4073])).
% 3.08/0.78  fof(f4073,plain,(
% 3.08/0.78    ( ! [X6] : (k7_relat_1(sK1,k1_relat_1(sK1)) = k7_relat_1(sK1,k2_xboole_0(k1_relat_1(sK1),X6))) ) | ~spl2_2),
% 3.08/0.78    inference(superposition,[],[f3951,f105])).
% 3.08/0.78  fof(f105,plain,(
% 3.08/0.78    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl2_2),
% 3.08/0.78    inference(unit_resulting_resolution,[],[f89,f96,f55])).
% 3.08/0.78  fof(f55,plain,(
% 3.08/0.78    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f33])).
% 3.08/0.78  fof(f33,plain,(
% 3.08/0.78    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.08/0.78    inference(flattening,[],[f32])).
% 3.08/0.78  fof(f32,plain,(
% 3.08/0.78    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.08/0.78    inference(ennf_transformation,[],[f25])).
% 3.08/0.78  fof(f25,axiom,(
% 3.08/0.78    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 3.08/0.78  fof(f96,plain,(
% 3.08/0.78    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))) ) | ~spl2_2),
% 3.08/0.78    inference(unit_resulting_resolution,[],[f87,f54])).
% 3.08/0.78  fof(f54,plain,(
% 3.08/0.78    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f31])).
% 3.08/0.78  fof(f31,plain,(
% 3.08/0.78    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.08/0.78    inference(ennf_transformation,[],[f24])).
% 3.08/0.78  fof(f24,axiom,(
% 3.08/0.78    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).
% 3.08/0.78  fof(f87,plain,(
% 3.08/0.78    v1_relat_1(sK1) | ~spl2_2),
% 3.08/0.78    inference(avatar_component_clause,[],[f85])).
% 3.08/0.78  fof(f85,plain,(
% 3.08/0.78    spl2_2 <=> v1_relat_1(sK1)),
% 3.08/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.08/0.78  fof(f89,plain,(
% 3.08/0.78    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_2),
% 3.08/0.78    inference(unit_resulting_resolution,[],[f87,f53])).
% 3.08/0.78  fof(f53,plain,(
% 3.08/0.78    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f30])).
% 3.08/0.78  fof(f30,plain,(
% 3.08/0.78    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.08/0.78    inference(ennf_transformation,[],[f22])).
% 3.08/0.78  fof(f22,axiom,(
% 3.08/0.78    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 3.08/0.78  fof(f3951,plain,(
% 3.08/0.78    ( ! [X2,X1] : (k7_relat_1(sK1,X1) = k7_relat_1(k7_relat_1(sK1,k2_xboole_0(X1,X2)),X1)) ) | ~spl2_2),
% 3.08/0.78    inference(backward_demodulation,[],[f281,f1090])).
% 3.08/0.78  fof(f1090,plain,(
% 3.08/0.78    ( ! [X6,X5] : (k6_subset_1(k2_xboole_0(X5,X6),k6_subset_1(X6,X5)) = X5) )),
% 3.08/0.78    inference(forward_demodulation,[],[f1089,f99])).
% 3.08/0.78  fof(f99,plain,(
% 3.08/0.78    ( ! [X2,X1] : (k6_subset_1(X1,X2) = k6_subset_1(k2_xboole_0(X2,X1),X2)) )),
% 3.08/0.78    inference(superposition,[],[f74,f44])).
% 3.08/0.78  fof(f44,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f1])).
% 3.08/0.78  fof(f1,axiom,(
% 3.08/0.78    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.08/0.78  fof(f74,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(k2_xboole_0(X0,X1),X1)) )),
% 3.08/0.78    inference(definition_unfolding,[],[f49,f43,f43])).
% 3.08/0.78  fof(f43,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f20])).
% 3.08/0.78  fof(f20,axiom,(
% 3.08/0.78    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.08/0.78  fof(f49,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f7])).
% 3.08/0.78  fof(f7,axiom,(
% 3.08/0.78    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 3.08/0.78  fof(f1089,plain,(
% 3.08/0.78    ( ! [X6,X5] : (k6_subset_1(k2_xboole_0(X5,X6),k6_subset_1(k2_xboole_0(X5,X6),X5)) = X5) )),
% 3.08/0.78    inference(forward_demodulation,[],[f1088,f304])).
% 3.08/0.78  fof(f304,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 3.08/0.78    inference(forward_demodulation,[],[f126,f92])).
% 3.08/0.78  fof(f92,plain,(
% 3.08/0.78    ( ! [X1] : (k5_xboole_0(o_0_0_xboole_0,X1) = X1) )),
% 3.08/0.78    inference(superposition,[],[f45,f72])).
% 3.08/0.78  fof(f72,plain,(
% 3.08/0.78    ( ! [X0] : (k5_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 3.08/0.78    inference(definition_unfolding,[],[f41,f39])).
% 3.08/0.78  fof(f39,plain,(
% 3.08/0.78    k1_xboole_0 = o_0_0_xboole_0),
% 3.08/0.78    inference(cnf_transformation,[],[f3])).
% 3.08/0.78  fof(f3,axiom,(
% 3.08/0.78    k1_xboole_0 = o_0_0_xboole_0),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 3.08/0.78  fof(f41,plain,(
% 3.08/0.78    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.08/0.78    inference(cnf_transformation,[],[f10])).
% 3.08/0.78  fof(f10,axiom,(
% 3.08/0.78    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 3.08/0.78  fof(f45,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f2])).
% 3.08/0.78  fof(f2,axiom,(
% 3.08/0.78    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 3.08/0.78  fof(f126,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k5_xboole_0(o_0_0_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 3.08/0.78    inference(superposition,[],[f58,f71])).
% 3.08/0.78  fof(f71,plain,(
% 3.08/0.78    ( ! [X0] : (o_0_0_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.08/0.78    inference(definition_unfolding,[],[f40,f39])).
% 3.08/0.78  fof(f40,plain,(
% 3.08/0.78    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f12])).
% 3.08/0.78  fof(f12,axiom,(
% 3.08/0.78    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 3.08/0.78  fof(f58,plain,(
% 3.08/0.78    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 3.08/0.78    inference(cnf_transformation,[],[f11])).
% 3.08/0.78  fof(f11,axiom,(
% 3.08/0.78    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 3.08/0.78  fof(f1088,plain,(
% 3.08/0.78    ( ! [X6,X5] : (k6_subset_1(k2_xboole_0(X5,X6),k6_subset_1(k2_xboole_0(X5,X6),X5)) = k5_xboole_0(k2_xboole_0(X5,X6),k5_xboole_0(k2_xboole_0(X5,X6),X5))) )),
% 3.08/0.78    inference(forward_demodulation,[],[f1040,f45])).
% 3.08/0.78  fof(f1040,plain,(
% 3.08/0.78    ( ! [X6,X5] : (k6_subset_1(k2_xboole_0(X5,X6),k6_subset_1(k2_xboole_0(X5,X6),X5)) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X5,X6),X5),k2_xboole_0(X5,X6))) )),
% 3.08/0.78    inference(superposition,[],[f193,f113])).
% 3.08/0.78  fof(f113,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.08/0.78    inference(superposition,[],[f57,f42])).
% 3.08/0.78  fof(f42,plain,(
% 3.08/0.78    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.08/0.78    inference(cnf_transformation,[],[f28])).
% 3.08/0.78  fof(f28,plain,(
% 3.08/0.78    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.08/0.78    inference(rectify,[],[f4])).
% 3.08/0.78  fof(f4,axiom,(
% 3.08/0.78    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 3.08/0.78  fof(f57,plain,(
% 3.08/0.78    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.08/0.78    inference(cnf_transformation,[],[f9])).
% 3.08/0.78  fof(f9,axiom,(
% 3.08/0.78    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 3.08/0.78  fof(f193,plain,(
% 3.08/0.78    ( ! [X2,X1] : (k6_subset_1(X1,k6_subset_1(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X2,X1))) )),
% 3.08/0.78    inference(superposition,[],[f177,f44])).
% 3.08/0.78  fof(f177,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 3.08/0.78    inference(forward_demodulation,[],[f77,f76])).
% 3.08/0.78  fof(f76,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 3.08/0.78    inference(definition_unfolding,[],[f51,f69,f43,f43])).
% 3.08/0.78  fof(f69,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.08/0.78    inference(definition_unfolding,[],[f47,f68])).
% 3.08/0.78  fof(f68,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.08/0.78    inference(definition_unfolding,[],[f48,f67])).
% 3.08/0.78  fof(f67,plain,(
% 3.08/0.78    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.08/0.78    inference(definition_unfolding,[],[f56,f66])).
% 3.08/0.78  fof(f66,plain,(
% 3.08/0.78    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.08/0.78    inference(definition_unfolding,[],[f60,f65])).
% 3.08/0.78  fof(f65,plain,(
% 3.08/0.78    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.08/0.78    inference(definition_unfolding,[],[f61,f64])).
% 3.08/0.78  fof(f64,plain,(
% 3.08/0.78    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.08/0.78    inference(definition_unfolding,[],[f62,f63])).
% 3.08/0.78  fof(f63,plain,(
% 3.08/0.78    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f19])).
% 3.08/0.78  fof(f19,axiom,(
% 3.08/0.78    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 3.08/0.78  fof(f62,plain,(
% 3.08/0.78    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f18])).
% 3.08/0.78  fof(f18,axiom,(
% 3.08/0.78    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 3.08/0.78  fof(f61,plain,(
% 3.08/0.78    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f17])).
% 3.08/0.78  fof(f17,axiom,(
% 3.08/0.78    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 3.08/0.78  fof(f60,plain,(
% 3.08/0.78    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f16])).
% 3.08/0.78  fof(f16,axiom,(
% 3.08/0.78    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 3.08/0.78  fof(f56,plain,(
% 3.08/0.78    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f15])).
% 3.08/0.78  fof(f15,axiom,(
% 3.08/0.78    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.08/0.78  fof(f48,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f14])).
% 3.08/0.78  fof(f14,axiom,(
% 3.08/0.78    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.08/0.78  fof(f47,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.08/0.78    inference(cnf_transformation,[],[f21])).
% 3.08/0.78  fof(f21,axiom,(
% 3.08/0.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.08/0.78  fof(f51,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.08/0.78    inference(cnf_transformation,[],[f8])).
% 3.08/0.78  fof(f8,axiom,(
% 3.08/0.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.08/0.78  fof(f77,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.08/0.78    inference(definition_unfolding,[],[f52,f69])).
% 3.08/0.78  fof(f52,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.08/0.78    inference(cnf_transformation,[],[f13])).
% 3.08/0.78  fof(f13,axiom,(
% 3.08/0.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 3.08/0.78  fof(f281,plain,(
% 3.08/0.78    ( ! [X2,X1] : (k7_relat_1(k7_relat_1(sK1,k2_xboole_0(X1,X2)),X1) = k7_relat_1(sK1,k6_subset_1(k2_xboole_0(X1,X2),k6_subset_1(X2,X1)))) ) | ~spl2_2),
% 3.08/0.78    inference(superposition,[],[f220,f99])).
% 3.08/0.78  fof(f220,plain,(
% 3.08/0.78    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k6_subset_1(X0,k6_subset_1(X0,X1)))) ) | ~spl2_2),
% 3.08/0.78    inference(unit_resulting_resolution,[],[f87,f219])).
% 3.08/0.78  fof(f219,plain,(
% 3.08/0.78    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 3.08/0.78    inference(forward_demodulation,[],[f78,f76])).
% 3.08/0.78  fof(f78,plain,(
% 3.08/0.78    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 3.08/0.78    inference(definition_unfolding,[],[f59,f69])).
% 3.08/0.78  fof(f59,plain,(
% 3.08/0.78    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 3.08/0.78    inference(cnf_transformation,[],[f34])).
% 3.08/0.78  fof(f34,plain,(
% 3.08/0.78    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.08/0.78    inference(ennf_transformation,[],[f23])).
% 3.08/0.78  fof(f23,axiom,(
% 3.08/0.78    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 3.08/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 3.08/0.78  fof(f4056,plain,(
% 3.08/0.78    ( ! [X2,X1] : (k7_relat_1(sK1,X1) = k7_relat_1(k7_relat_1(sK1,k2_xboole_0(X2,X1)),X1)) ) | ~spl2_2),
% 3.08/0.78    inference(superposition,[],[f3951,f44])).
% 3.08/0.78  fof(f250,plain,(
% 3.08/0.78    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0) | spl2_4),
% 3.08/0.78    inference(avatar_component_clause,[],[f248])).
% 3.08/0.78  fof(f248,plain,(
% 3.08/0.78    spl2_4 <=> k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0)),
% 3.08/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 3.08/0.78  fof(f251,plain,(
% 3.08/0.78    ~spl2_4 | ~spl2_2 | spl2_3),
% 3.08/0.78    inference(avatar_split_clause,[],[f234,f163,f85,f248])).
% 3.08/0.78  fof(f163,plain,(
% 3.08/0.78    spl2_3 <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),sK0)))),
% 3.08/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.08/0.78  fof(f234,plain,(
% 3.08/0.78    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0) | (~spl2_2 | spl2_3)),
% 3.08/0.78    inference(superposition,[],[f165,f220])).
% 3.08/0.78  fof(f165,plain,(
% 3.08/0.78    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),sK0))) | spl2_3),
% 3.08/0.78    inference(avatar_component_clause,[],[f163])).
% 3.08/0.78  fof(f166,plain,(
% 3.08/0.78    ~spl2_3 | spl2_1),
% 3.08/0.78    inference(avatar_split_clause,[],[f159,f80,f163])).
% 3.08/0.78  fof(f80,plain,(
% 3.08/0.78    spl2_1 <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)))),
% 3.08/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.08/0.78  fof(f159,plain,(
% 3.08/0.78    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),sK0))) | spl2_1),
% 3.08/0.78    inference(backward_demodulation,[],[f82,f76])).
% 3.08/0.78  fof(f82,plain,(
% 3.08/0.78    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) | spl2_1),
% 3.08/0.78    inference(avatar_component_clause,[],[f80])).
% 3.08/0.78  fof(f88,plain,(
% 3.08/0.78    spl2_2),
% 3.08/0.78    inference(avatar_split_clause,[],[f37,f85])).
% 3.08/0.78  fof(f37,plain,(
% 3.08/0.78    v1_relat_1(sK1)),
% 3.08/0.78    inference(cnf_transformation,[],[f36])).
% 3.08/0.78  fof(f36,plain,(
% 3.08/0.78    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 3.08/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f35])).
% 3.08/0.78  fof(f35,plain,(
% 3.08/0.78    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 3.08/0.78    introduced(choice_axiom,[])).
% 3.08/0.78  fof(f29,plain,(
% 3.08/0.78    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.08/0.78    inference(ennf_transformation,[],[f27])).
% 3.08/0.78  fof(f27,negated_conjecture,(
% 3.08/0.78    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 3.08/0.78    inference(negated_conjecture,[],[f26])).
% 3.08/0.79  fof(f26,conjecture,(
% 3.08/0.79    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 3.08/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 3.08/0.79  fof(f83,plain,(
% 3.08/0.79    ~spl2_1),
% 3.08/0.79    inference(avatar_split_clause,[],[f70,f80])).
% 3.08/0.79  fof(f70,plain,(
% 3.08/0.79    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)))),
% 3.08/0.79    inference(definition_unfolding,[],[f38,f69])).
% 3.08/0.79  fof(f38,plain,(
% 3.08/0.79    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 3.08/0.79    inference(cnf_transformation,[],[f36])).
% 3.08/0.79  % SZS output end Proof for theBenchmark
% 3.08/0.79  % (12668)------------------------------
% 3.08/0.79  % (12668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.08/0.79  % (12668)Termination reason: Refutation
% 3.08/0.79  
% 3.08/0.79  % (12668)Memory used [KB]: 9338
% 3.08/0.79  % (12668)Time elapsed: 0.331 s
% 3.08/0.79  % (12668)------------------------------
% 3.08/0.79  % (12668)------------------------------
% 3.08/0.80  % (12658)Success in time 0.431 s
%------------------------------------------------------------------------------
