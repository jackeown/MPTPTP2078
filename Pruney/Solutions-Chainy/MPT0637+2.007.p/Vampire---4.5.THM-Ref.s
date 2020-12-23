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
% DateTime   : Thu Dec  3 12:52:23 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 269 expanded)
%              Number of leaves         :   19 (  83 expanded)
%              Depth                    :   20
%              Number of atoms          :  176 ( 407 expanded)
%              Number of equality atoms :   69 ( 188 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1466,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f1454,f1465])).

fof(f1465,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f1464])).

fof(f1464,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f136,f164])).

fof(f164,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) ),
    inference(superposition,[],[f126,f146])).

fof(f146,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(forward_demodulation,[],[f143,f36])).

fof(f36,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f143,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))) ),
    inference(resolution,[],[f60,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f126,plain,(
    ! [X4,X3] : r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3)) ),
    inference(subsumption_resolution,[],[f124,f35])).

fof(f124,plain,(
    ! [X4,X3] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f47,f96])).

fof(f96,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f45,f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f136,plain,
    ( ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl2_4
  <=> r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1454,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f1432])).

fof(f1432,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f1197,f132])).

fof(f132,plain,
    ( ~ r1_tarski(k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl2_3
  <=> r1_tarski(k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1197,plain,(
    ! [X15,X16] : r1_tarski(k6_relat_1(k1_setfam_1(k1_enumset1(X15,X15,X16))),k7_relat_1(k6_relat_1(X15),X16)) ),
    inference(forward_demodulation,[],[f1183,f146])).

fof(f1183,plain,(
    ! [X15,X16] : r1_tarski(k6_relat_1(k1_setfam_1(k1_enumset1(X15,X15,X16))),k7_relat_1(k6_relat_1(X15),k1_setfam_1(k1_enumset1(X15,X15,X16)))) ),
    inference(superposition,[],[f1141,f156])).

fof(f156,plain,(
    ! [X2,X1] : k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2))),X1) ),
    inference(resolution,[],[f154,f57])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f40,f55])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f110,f96])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f109,f35])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f49,f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1141,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[],[f1128,f295])).

fof(f295,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2) ),
    inference(superposition,[],[f151,f162])).

fof(f162,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f146,f58])).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f41,f42,f42])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f151,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(resolution,[],[f62,f35])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f1128,plain,(
    ! [X4,X5,X3] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(subsumption_resolution,[],[f1117,f715])).

fof(f715,plain,(
    ! [X2,X3] : v1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(subsumption_resolution,[],[f690,f35])).

fof(f690,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X3),X2))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f59,f234])).

fof(f234,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k1_setfam_1(k1_enumset1(k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(forward_demodulation,[],[f231,f96])).

fof(f231,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k1_setfam_1(k1_enumset1(k6_relat_1(X0),k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ),
    inference(resolution,[],[f105,f35])).

fof(f105,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(X3,k6_relat_1(X4)) = k1_setfam_1(k1_enumset1(X3,X3,k5_relat_1(X3,k6_relat_1(X4)))) ) ),
    inference(forward_demodulation,[],[f101,f58])).

fof(f101,plain,(
    ! [X4,X3] :
      ( k5_relat_1(X3,k6_relat_1(X4)) = k1_setfam_1(k1_enumset1(k5_relat_1(X3,k6_relat_1(X4)),k5_relat_1(X3,k6_relat_1(X4)),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f61,f47])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f44,f55])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f1117,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(superposition,[],[f47,f1019])).

fof(f1019,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f1018,f96])).

fof(f1018,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f1010,f719])).

fof(f719,plain,(
    ! [X6,X8,X7] : k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8) = k5_relat_1(k6_relat_1(X8),k7_relat_1(k6_relat_1(X6),X7)) ),
    inference(resolution,[],[f715,f45])).

fof(f1010,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(resolution,[],[f339,f35])).

fof(f339,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(forward_demodulation,[],[f336,f96])).

fof(f336,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f166,f35])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f39,f35])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f138,plain,
    ( ~ spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f128,f130,f134])).

fof(f128,plain,
    ( ~ r1_tarski(k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))
    | ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))) ),
    inference(extensionality_resolution,[],[f53,f120])).

fof(f120,plain,(
    k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f56,f96])).

fof(f56,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f34,f55])).

fof(f34,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f30])).

fof(f30,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:50:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (30907)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (30924)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (30925)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (30917)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (30915)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (30915)Refutation not found, incomplete strategy% (30915)------------------------------
% 0.22/0.52  % (30915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30913)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (30915)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30915)Memory used [KB]: 1663
% 0.22/0.52  % (30915)Time elapsed: 0.107 s
% 0.22/0.52  % (30915)------------------------------
% 0.22/0.52  % (30915)------------------------------
% 1.25/0.52  % (30913)Refutation not found, incomplete strategy% (30913)------------------------------
% 1.25/0.52  % (30913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (30913)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (30913)Memory used [KB]: 10618
% 1.25/0.52  % (30913)Time elapsed: 0.105 s
% 1.25/0.52  % (30913)------------------------------
% 1.25/0.52  % (30913)------------------------------
% 1.25/0.53  % (30920)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.25/0.53  % (30920)Refutation not found, incomplete strategy% (30920)------------------------------
% 1.25/0.53  % (30920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (30920)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (30920)Memory used [KB]: 1663
% 1.25/0.53  % (30920)Time elapsed: 0.122 s
% 1.25/0.53  % (30920)------------------------------
% 1.25/0.53  % (30920)------------------------------
% 1.25/0.53  % (30903)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.25/0.54  % (30928)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.25/0.54  % (30928)Refutation not found, incomplete strategy% (30928)------------------------------
% 1.25/0.54  % (30928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (30928)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (30928)Memory used [KB]: 6140
% 1.25/0.54  % (30928)Time elapsed: 0.131 s
% 1.25/0.54  % (30928)------------------------------
% 1.25/0.54  % (30928)------------------------------
% 1.25/0.54  % (30904)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.25/0.54  % (30927)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.25/0.54  % (30901)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.25/0.54  % (30927)Refutation not found, incomplete strategy% (30927)------------------------------
% 1.25/0.54  % (30927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (30927)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (30927)Memory used [KB]: 6140
% 1.25/0.54  % (30927)Time elapsed: 0.126 s
% 1.25/0.54  % (30927)------------------------------
% 1.25/0.54  % (30927)------------------------------
% 1.25/0.54  % (30911)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.25/0.54  % (30905)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.25/0.54  % (30906)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.25/0.54  % (30911)Refutation not found, incomplete strategy% (30911)------------------------------
% 1.25/0.54  % (30911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (30911)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (30911)Memory used [KB]: 10618
% 1.25/0.54  % (30911)Time elapsed: 0.132 s
% 1.25/0.54  % (30911)------------------------------
% 1.25/0.54  % (30911)------------------------------
% 1.44/0.54  % (30902)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.44/0.54  % (30902)Refutation not found, incomplete strategy% (30902)------------------------------
% 1.44/0.54  % (30902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (30902)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (30902)Memory used [KB]: 1663
% 1.44/0.54  % (30902)Time elapsed: 0.123 s
% 1.44/0.54  % (30902)------------------------------
% 1.44/0.54  % (30902)------------------------------
% 1.44/0.54  % (30908)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.44/0.54  % (30914)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.44/0.55  % (30930)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.44/0.55  % (30929)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.44/0.55  % (30919)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.55  % (30929)Refutation not found, incomplete strategy% (30929)------------------------------
% 1.44/0.55  % (30929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (30929)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (30929)Memory used [KB]: 6140
% 1.44/0.55  % (30929)Time elapsed: 0.137 s
% 1.44/0.55  % (30929)------------------------------
% 1.44/0.55  % (30929)------------------------------
% 1.44/0.55  % (30930)Refutation not found, incomplete strategy% (30930)------------------------------
% 1.44/0.55  % (30930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (30930)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (30930)Memory used [KB]: 10746
% 1.44/0.55  % (30930)Time elapsed: 0.139 s
% 1.44/0.55  % (30930)------------------------------
% 1.44/0.55  % (30930)------------------------------
% 1.44/0.55  % (30910)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.44/0.55  % (30922)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.44/0.55  % (30919)Refutation not found, incomplete strategy% (30919)------------------------------
% 1.44/0.55  % (30919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (30909)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.44/0.55  % (30919)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (30919)Memory used [KB]: 1663
% 1.44/0.55  % (30919)Time elapsed: 0.137 s
% 1.44/0.55  % (30921)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.44/0.55  % (30919)------------------------------
% 1.44/0.55  % (30919)------------------------------
% 1.44/0.55  % (30931)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.44/0.55  % (30931)Refutation not found, incomplete strategy% (30931)------------------------------
% 1.44/0.55  % (30931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (30931)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (30931)Memory used [KB]: 1663
% 1.44/0.55  % (30931)Time elapsed: 0.148 s
% 1.44/0.55  % (30931)------------------------------
% 1.44/0.55  % (30931)------------------------------
% 1.44/0.56  % (30923)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.44/0.56  % (30912)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.44/0.56  % (30926)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.44/0.56  % (30912)Refutation not found, incomplete strategy% (30912)------------------------------
% 1.44/0.56  % (30912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (30912)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (30912)Memory used [KB]: 6140
% 1.44/0.56  % (30912)Time elapsed: 0.148 s
% 1.44/0.56  % (30912)------------------------------
% 1.44/0.56  % (30912)------------------------------
% 1.44/0.56  % (30926)Refutation not found, incomplete strategy% (30926)------------------------------
% 1.44/0.56  % (30926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (30926)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (30926)Memory used [KB]: 10618
% 1.44/0.56  % (30926)Time elapsed: 0.141 s
% 1.44/0.56  % (30926)------------------------------
% 1.44/0.56  % (30926)------------------------------
% 1.44/0.56  % (30918)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.44/0.56  % (30918)Refutation not found, incomplete strategy% (30918)------------------------------
% 1.44/0.56  % (30918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (30918)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  
% 1.44/0.57  % (30918)Memory used [KB]: 10618
% 1.44/0.57  % (30918)Time elapsed: 0.148 s
% 1.44/0.57  % (30918)------------------------------
% 1.44/0.57  % (30918)------------------------------
% 1.44/0.60  % (30907)Refutation found. Thanks to Tanya!
% 1.44/0.60  % SZS status Theorem for theBenchmark
% 1.44/0.60  % SZS output start Proof for theBenchmark
% 1.44/0.60  fof(f1466,plain,(
% 1.44/0.60    $false),
% 1.44/0.60    inference(avatar_sat_refutation,[],[f138,f1454,f1465])).
% 1.44/0.60  fof(f1465,plain,(
% 1.44/0.60    spl2_4),
% 1.44/0.60    inference(avatar_contradiction_clause,[],[f1464])).
% 1.44/0.60  fof(f1464,plain,(
% 1.44/0.60    $false | spl2_4),
% 1.44/0.60    inference(subsumption_resolution,[],[f136,f164])).
% 1.44/0.60  fof(f164,plain,(
% 1.44/0.60    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))))) )),
% 1.44/0.60    inference(superposition,[],[f126,f146])).
% 1.44/0.60  fof(f146,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 1.44/0.60    inference(forward_demodulation,[],[f143,f36])).
% 1.44/0.60  fof(f36,plain,(
% 1.44/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.44/0.60    inference(cnf_transformation,[],[f12])).
% 1.44/0.60  fof(f12,axiom,(
% 1.44/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.44/0.60  fof(f143,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)))) )),
% 1.44/0.60    inference(resolution,[],[f60,f35])).
% 1.44/0.60  fof(f35,plain,(
% 1.44/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.44/0.60    inference(cnf_transformation,[],[f7])).
% 1.44/0.60  fof(f7,axiom,(
% 1.44/0.60    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.44/0.60  fof(f60,plain,(
% 1.44/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)))) )),
% 1.44/0.60    inference(definition_unfolding,[],[f46,f55])).
% 1.44/0.60  fof(f55,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.44/0.60    inference(definition_unfolding,[],[f43,f42])).
% 1.44/0.60  fof(f42,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f5])).
% 1.44/0.60  fof(f5,axiom,(
% 1.44/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.60  fof(f43,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.44/0.60    inference(cnf_transformation,[],[f6])).
% 1.44/0.60  fof(f6,axiom,(
% 1.44/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.44/0.60  fof(f46,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f24])).
% 1.44/0.60  fof(f24,plain,(
% 1.44/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.44/0.60    inference(ennf_transformation,[],[f10])).
% 1.44/0.60  fof(f10,axiom,(
% 1.44/0.60    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 1.44/0.60  fof(f126,plain,(
% 1.44/0.60    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))) )),
% 1.44/0.60    inference(subsumption_resolution,[],[f124,f35])).
% 1.44/0.60  fof(f124,plain,(
% 1.44/0.60    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 1.44/0.60    inference(superposition,[],[f47,f96])).
% 1.44/0.60  fof(f96,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.44/0.60    inference(resolution,[],[f45,f35])).
% 1.44/0.60  fof(f45,plain,(
% 1.44/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f23])).
% 1.44/0.60  fof(f23,plain,(
% 1.44/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.44/0.60    inference(ennf_transformation,[],[f16])).
% 1.44/0.60  fof(f16,axiom,(
% 1.44/0.60    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.44/0.60  fof(f47,plain,(
% 1.44/0.60    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f25])).
% 1.44/0.60  fof(f25,plain,(
% 1.44/0.60    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.44/0.60    inference(ennf_transformation,[],[f13])).
% 1.44/0.60  fof(f13,axiom,(
% 1.44/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 1.44/0.60  fof(f136,plain,(
% 1.44/0.60    ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))) | spl2_4),
% 1.44/0.60    inference(avatar_component_clause,[],[f134])).
% 1.44/0.60  fof(f134,plain,(
% 1.44/0.60    spl2_4 <=> r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))))),
% 1.44/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.44/0.60  fof(f1454,plain,(
% 1.44/0.60    spl2_3),
% 1.44/0.60    inference(avatar_contradiction_clause,[],[f1432])).
% 1.44/0.60  fof(f1432,plain,(
% 1.44/0.60    $false | spl2_3),
% 1.44/0.60    inference(resolution,[],[f1197,f132])).
% 1.44/0.60  fof(f132,plain,(
% 1.44/0.60    ~r1_tarski(k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) | spl2_3),
% 1.44/0.60    inference(avatar_component_clause,[],[f130])).
% 1.44/0.60  fof(f130,plain,(
% 1.44/0.60    spl2_3 <=> r1_tarski(k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))),
% 1.44/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.44/0.60  fof(f1197,plain,(
% 1.44/0.60    ( ! [X15,X16] : (r1_tarski(k6_relat_1(k1_setfam_1(k1_enumset1(X15,X15,X16))),k7_relat_1(k6_relat_1(X15),X16))) )),
% 1.44/0.60    inference(forward_demodulation,[],[f1183,f146])).
% 1.44/0.60  fof(f1183,plain,(
% 1.44/0.60    ( ! [X15,X16] : (r1_tarski(k6_relat_1(k1_setfam_1(k1_enumset1(X15,X15,X16))),k7_relat_1(k6_relat_1(X15),k1_setfam_1(k1_enumset1(X15,X15,X16))))) )),
% 1.44/0.60    inference(superposition,[],[f1141,f156])).
% 1.44/0.60  fof(f156,plain,(
% 1.44/0.60    ( ! [X2,X1] : (k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2))),X1)) )),
% 1.44/0.60    inference(resolution,[],[f154,f57])).
% 1.44/0.60  fof(f57,plain,(
% 1.44/0.60    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 1.44/0.60    inference(definition_unfolding,[],[f40,f55])).
% 1.44/0.60  fof(f40,plain,(
% 1.44/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f2])).
% 1.44/0.60  fof(f2,axiom,(
% 1.44/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.44/0.60  fof(f154,plain,(
% 1.44/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.44/0.60    inference(forward_demodulation,[],[f110,f96])).
% 1.44/0.60  fof(f110,plain,(
% 1.44/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 1.44/0.60    inference(subsumption_resolution,[],[f109,f35])).
% 1.44/0.60  fof(f109,plain,(
% 1.44/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.44/0.60    inference(superposition,[],[f49,f36])).
% 1.44/0.60  fof(f49,plain,(
% 1.44/0.60    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f27])).
% 1.44/0.60  fof(f27,plain,(
% 1.44/0.60    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.44/0.60    inference(flattening,[],[f26])).
% 1.44/0.60  fof(f26,plain,(
% 1.44/0.60    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.44/0.60    inference(ennf_transformation,[],[f14])).
% 1.44/0.60  fof(f14,axiom,(
% 1.44/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 1.44/0.60  fof(f1141,plain,(
% 1.44/0.60    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.44/0.60    inference(superposition,[],[f1128,f295])).
% 1.44/0.60  fof(f295,plain,(
% 1.44/0.60    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)) )),
% 1.44/0.60    inference(superposition,[],[f151,f162])).
% 1.44/0.60  fof(f162,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X0)))) )),
% 1.44/0.60    inference(superposition,[],[f146,f58])).
% 1.44/0.60  fof(f58,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.44/0.60    inference(definition_unfolding,[],[f41,f42,f42])).
% 1.44/0.60  fof(f41,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f4])).
% 1.44/0.60  fof(f4,axiom,(
% 1.44/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.44/0.60  fof(f151,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X2)))) )),
% 1.44/0.60    inference(resolution,[],[f62,f35])).
% 1.44/0.60  fof(f62,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 1.44/0.60    inference(definition_unfolding,[],[f54,f55])).
% 1.44/0.60  fof(f54,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f29])).
% 1.44/0.60  fof(f29,plain,(
% 1.44/0.60    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.44/0.60    inference(ennf_transformation,[],[f9])).
% 1.44/0.60  fof(f9,axiom,(
% 1.44/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 1.44/0.60  fof(f1128,plain,(
% 1.44/0.60    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))) )),
% 1.44/0.60    inference(subsumption_resolution,[],[f1117,f715])).
% 1.44/0.60  fof(f715,plain,(
% 1.44/0.60    ( ! [X2,X3] : (v1_relat_1(k7_relat_1(k6_relat_1(X3),X2))) )),
% 1.44/0.60    inference(subsumption_resolution,[],[f690,f35])).
% 1.44/0.60  fof(f690,plain,(
% 1.44/0.60    ( ! [X2,X3] : (v1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 1.44/0.60    inference(superposition,[],[f59,f234])).
% 1.44/0.60  fof(f234,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k1_setfam_1(k1_enumset1(k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0)))) )),
% 1.44/0.60    inference(forward_demodulation,[],[f231,f96])).
% 1.44/0.60  fof(f231,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k1_setfam_1(k1_enumset1(k6_relat_1(X0),k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))))) )),
% 1.44/0.60    inference(resolution,[],[f105,f35])).
% 1.44/0.60  fof(f105,plain,(
% 1.44/0.60    ( ! [X4,X3] : (~v1_relat_1(X3) | k5_relat_1(X3,k6_relat_1(X4)) = k1_setfam_1(k1_enumset1(X3,X3,k5_relat_1(X3,k6_relat_1(X4))))) )),
% 1.44/0.60    inference(forward_demodulation,[],[f101,f58])).
% 1.44/0.60  fof(f101,plain,(
% 1.44/0.60    ( ! [X4,X3] : (k5_relat_1(X3,k6_relat_1(X4)) = k1_setfam_1(k1_enumset1(k5_relat_1(X3,k6_relat_1(X4)),k5_relat_1(X3,k6_relat_1(X4)),X3)) | ~v1_relat_1(X3)) )),
% 1.44/0.60    inference(resolution,[],[f61,f47])).
% 1.44/0.60  fof(f61,plain,(
% 1.44/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0) )),
% 1.44/0.60    inference(definition_unfolding,[],[f50,f55])).
% 1.44/0.60  fof(f50,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f28])).
% 1.44/0.60  fof(f28,plain,(
% 1.44/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.44/0.60    inference(ennf_transformation,[],[f3])).
% 1.44/0.60  fof(f3,axiom,(
% 1.44/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.44/0.60  fof(f59,plain,(
% 1.44/0.60    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 1.44/0.60    inference(definition_unfolding,[],[f44,f55])).
% 1.44/0.60  fof(f44,plain,(
% 1.44/0.60    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f22])).
% 1.44/0.60  fof(f22,plain,(
% 1.44/0.60    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.44/0.60    inference(ennf_transformation,[],[f8])).
% 1.44/0.60  fof(f8,axiom,(
% 1.44/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.44/0.60  fof(f1117,plain,(
% 1.44/0.60    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 1.44/0.60    inference(superposition,[],[f47,f1019])).
% 1.44/0.60  fof(f1019,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 1.44/0.60    inference(forward_demodulation,[],[f1018,f96])).
% 1.44/0.60  fof(f1018,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2))) )),
% 1.44/0.60    inference(forward_demodulation,[],[f1010,f719])).
% 1.44/0.60  fof(f719,plain,(
% 1.44/0.60    ( ! [X6,X8,X7] : (k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8) = k5_relat_1(k6_relat_1(X8),k7_relat_1(k6_relat_1(X6),X7))) )),
% 1.44/0.60    inference(resolution,[],[f715,f45])).
% 1.44/0.60  fof(f1010,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.44/0.60    inference(resolution,[],[f339,f35])).
% 1.44/0.60  fof(f339,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.44/0.60    inference(forward_demodulation,[],[f336,f96])).
% 1.44/0.60  fof(f336,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 1.44/0.60    inference(resolution,[],[f166,f35])).
% 1.44/0.60  fof(f166,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 1.44/0.60    inference(resolution,[],[f39,f35])).
% 1.44/0.60  fof(f39,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f21])).
% 1.44/0.60  fof(f21,plain,(
% 1.44/0.60    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.60    inference(ennf_transformation,[],[f11])).
% 1.44/0.60  fof(f11,axiom,(
% 1.44/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.44/0.60  fof(f138,plain,(
% 1.44/0.60    ~spl2_4 | ~spl2_3),
% 1.44/0.60    inference(avatar_split_clause,[],[f128,f130,f134])).
% 1.44/0.60  fof(f128,plain,(
% 1.44/0.60    ~r1_tarski(k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) | ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))))),
% 1.44/0.60    inference(extensionality_resolution,[],[f53,f120])).
% 1.44/0.60  fof(f120,plain,(
% 1.44/0.60    k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.44/0.60    inference(backward_demodulation,[],[f56,f96])).
% 1.44/0.60  fof(f56,plain,(
% 1.44/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 1.44/0.60    inference(definition_unfolding,[],[f34,f55])).
% 1.44/0.60  fof(f34,plain,(
% 1.44/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.44/0.60    inference(cnf_transformation,[],[f31])).
% 1.44/0.60  fof(f31,plain,(
% 1.44/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.44/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f30])).
% 1.44/0.60  fof(f30,plain,(
% 1.44/0.60    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.44/0.60    introduced(choice_axiom,[])).
% 1.44/0.61  fof(f19,plain,(
% 1.44/0.61    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.44/0.61    inference(ennf_transformation,[],[f18])).
% 1.44/0.61  fof(f18,negated_conjecture,(
% 1.44/0.61    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.44/0.61    inference(negated_conjecture,[],[f17])).
% 1.44/0.61  fof(f17,conjecture,(
% 1.44/0.61    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.44/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.44/0.61  fof(f53,plain,(
% 1.44/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.44/0.61    inference(cnf_transformation,[],[f33])).
% 1.44/0.61  fof(f33,plain,(
% 1.44/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.61    inference(flattening,[],[f32])).
% 1.44/0.61  fof(f32,plain,(
% 1.44/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.61    inference(nnf_transformation,[],[f1])).
% 1.44/0.61  fof(f1,axiom,(
% 1.44/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.61  % SZS output end Proof for theBenchmark
% 1.44/0.61  % (30907)------------------------------
% 1.44/0.61  % (30907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.61  % (30907)Termination reason: Refutation
% 1.44/0.61  
% 1.44/0.61  % (30907)Memory used [KB]: 11897
% 1.44/0.61  % (30907)Time elapsed: 0.187 s
% 1.44/0.61  % (30907)------------------------------
% 1.44/0.61  % (30907)------------------------------
% 1.44/0.61  % (30897)Success in time 0.236 s
%------------------------------------------------------------------------------
