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
% DateTime   : Thu Dec  3 12:52:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 279 expanded)
%              Number of leaves         :   20 (  86 expanded)
%              Depth                    :   17
%              Number of atoms          :  181 ( 427 expanded)
%              Number of equality atoms :   70 ( 200 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f912,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f145,f228,f907])).

fof(f907,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f906])).

fof(f906,plain,
    ( $false
    | spl2_6 ),
    inference(subsumption_resolution,[],[f143,f783])).

fof(f783,plain,(
    ! [X0,X1] : r1_tarski(k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f756,f211])).

fof(f211,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f207,f38])).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f207,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) ),
    inference(resolution,[],[f202,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) ) ),
    inference(forward_demodulation,[],[f64,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f48,plain,(
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

fof(f756,plain,(
    ! [X2,X3] : r1_tarski(k6_relat_1(k4_xboole_0(X2,X3)),k7_relat_1(k6_relat_1(X2),k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f732,f95])).

fof(f95,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(superposition,[],[f91,f70])).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f68,f39])).

fof(f39,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f40,f36])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f91,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f47,f36])).

fof(f47,plain,(
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

fof(f732,plain,(
    ! [X4,X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(k4_xboole_0(X2,X3)),X4),k7_relat_1(k6_relat_1(X2),X4)) ),
    inference(superposition,[],[f728,f157])).

fof(f157,plain,(
    ! [X6,X5] : k6_relat_1(k4_xboole_0(X5,X6)) = k7_relat_1(k6_relat_1(k4_xboole_0(X5,X6)),X5) ),
    inference(resolution,[],[f122,f150])).

fof(f150,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f131,f146])).

fof(f146,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f63,f62])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f131,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f61,f62])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f121,f91])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f120,f36])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f51,f38])).

fof(f51,plain,(
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

fof(f728,plain,(
    ! [X4,X5,X3] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(subsumption_resolution,[],[f719,f103])).

fof(f103,plain,(
    ! [X6,X5] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) ),
    inference(subsumption_resolution,[],[f102,f36])).

fof(f102,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(subsumption_resolution,[],[f99,f36])).

fof(f99,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
      | ~ v1_relat_1(k6_relat_1(X6))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(superposition,[],[f52,f91])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f719,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(superposition,[],[f49,f710])).

fof(f710,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f709,f91])).

fof(f709,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(forward_demodulation,[],[f702,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f103,f47])).

fof(f702,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(resolution,[],[f393,f36])).

fof(f393,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(forward_demodulation,[],[f387,f91])).

fof(f387,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f181,f36])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f41,f36])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f49,plain,(
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

fof(f143,plain,
    ( ~ r1_tarski(k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl2_6
  <=> r1_tarski(k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f228,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f213,f139])).

fof(f139,plain,
    ( ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl2_5
  <=> r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f213,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[],[f101,f211])).

fof(f101,plain,(
    ! [X4,X3] : r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3)) ),
    inference(subsumption_resolution,[],[f98,f36])).

fof(f98,plain,(
    ! [X4,X3] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f49,f91])).

fof(f145,plain,
    ( ~ spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f135,f137,f141])).

fof(f135,plain,
    ( ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ r1_tarski(k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(extensionality_resolution,[],[f55,f132])).

fof(f132,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f94,f62])).

fof(f94,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f60,f91])).

fof(f60,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f35,f59])).

fof(f35,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).

fof(f31,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:00:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (10595)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (10597)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (10594)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (10591)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (10603)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (10607)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (10602)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (10602)Refutation not found, incomplete strategy% (10602)------------------------------
% 0.20/0.54  % (10602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10602)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10602)Memory used [KB]: 1663
% 0.20/0.54  % (10602)Time elapsed: 0.107 s
% 0.20/0.54  % (10602)------------------------------
% 0.20/0.54  % (10602)------------------------------
% 0.20/0.54  % (10598)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (10590)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (10615)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (10611)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (10613)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (10615)Refutation not found, incomplete strategy% (10615)------------------------------
% 0.20/0.54  % (10615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10613)Refutation not found, incomplete strategy% (10613)------------------------------
% 0.20/0.54  % (10613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10613)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10613)Memory used [KB]: 6140
% 0.20/0.54  % (10613)Time elapsed: 0.119 s
% 0.20/0.54  % (10613)------------------------------
% 0.20/0.54  % (10613)------------------------------
% 0.20/0.54  % (10615)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10615)Memory used [KB]: 6140
% 0.20/0.54  % (10615)Time elapsed: 0.126 s
% 0.20/0.54  % (10615)------------------------------
% 0.20/0.54  % (10615)------------------------------
% 0.20/0.54  % (10614)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (10592)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.55  % (10610)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (10599)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (10596)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (10599)Refutation not found, incomplete strategy% (10599)------------------------------
% 0.20/0.55  % (10599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10599)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (10599)Memory used [KB]: 6140
% 0.20/0.55  % (10599)Time elapsed: 0.131 s
% 0.20/0.55  % (10599)------------------------------
% 0.20/0.55  % (10599)------------------------------
% 0.20/0.55  % (10600)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.55  % (10598)Refutation not found, incomplete strategy% (10598)------------------------------
% 0.20/0.55  % (10598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10598)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (10598)Memory used [KB]: 10618
% 0.20/0.55  % (10598)Time elapsed: 0.133 s
% 0.20/0.55  % (10598)------------------------------
% 0.20/0.55  % (10598)------------------------------
% 0.20/0.55  % (10608)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (10614)Refutation not found, incomplete strategy% (10614)------------------------------
% 0.20/0.55  % (10614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10614)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (10614)Memory used [KB]: 6140
% 0.20/0.55  % (10614)Time elapsed: 0.133 s
% 0.20/0.55  % (10614)------------------------------
% 0.20/0.55  % (10614)------------------------------
% 0.20/0.55  % (10616)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.56  % (10589)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.56  % (10616)Refutation not found, incomplete strategy% (10616)------------------------------
% 0.20/0.56  % (10616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (10616)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10616)Memory used [KB]: 10618
% 0.20/0.56  % (10616)Time elapsed: 0.136 s
% 0.20/0.56  % (10616)------------------------------
% 0.20/0.56  % (10616)------------------------------
% 0.20/0.56  % (10589)Refutation not found, incomplete strategy% (10589)------------------------------
% 0.20/0.56  % (10589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (10589)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10589)Memory used [KB]: 1663
% 0.20/0.56  % (10589)Time elapsed: 0.127 s
% 0.20/0.56  % (10589)------------------------------
% 0.20/0.56  % (10589)------------------------------
% 0.20/0.56  % (10601)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.56  % (10604)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.56  % (10606)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.56  % (10609)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (10604)Refutation not found, incomplete strategy% (10604)------------------------------
% 0.20/0.56  % (10604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (10604)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10604)Memory used [KB]: 10618
% 0.20/0.56  % (10604)Time elapsed: 0.143 s
% 0.20/0.56  % (10604)------------------------------
% 0.20/0.56  % (10604)------------------------------
% 0.20/0.56  % (10606)Refutation not found, incomplete strategy% (10606)------------------------------
% 0.20/0.56  % (10606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (10606)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10606)Memory used [KB]: 1663
% 0.20/0.56  % (10606)Time elapsed: 0.144 s
% 0.20/0.56  % (10606)------------------------------
% 0.20/0.56  % (10606)------------------------------
% 0.20/0.56  % (10600)Refutation not found, incomplete strategy% (10600)------------------------------
% 0.20/0.56  % (10600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (10605)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.56  % (10600)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10600)Memory used [KB]: 10618
% 0.20/0.56  % (10600)Time elapsed: 0.142 s
% 0.20/0.56  % (10600)------------------------------
% 0.20/0.56  % (10600)------------------------------
% 0.20/0.56  % (10612)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.56  % (10605)Refutation not found, incomplete strategy% (10605)------------------------------
% 0.20/0.56  % (10605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (10605)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10605)Memory used [KB]: 1663
% 0.20/0.56  % (10605)Time elapsed: 0.136 s
% 0.20/0.56  % (10605)------------------------------
% 0.20/0.56  % (10605)------------------------------
% 0.20/0.56  % (10612)Refutation not found, incomplete strategy% (10612)------------------------------
% 0.20/0.56  % (10612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (10612)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10612)Memory used [KB]: 10618
% 0.20/0.56  % (10612)Time elapsed: 0.145 s
% 0.20/0.56  % (10612)------------------------------
% 0.20/0.56  % (10612)------------------------------
% 0.20/0.56  % (10593)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.57  % (10617)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.57  % (10617)Refutation not found, incomplete strategy% (10617)------------------------------
% 0.20/0.57  % (10617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (10617)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (10617)Memory used [KB]: 1663
% 0.20/0.57  % (10617)Time elapsed: 0.001 s
% 0.20/0.57  % (10617)------------------------------
% 0.20/0.57  % (10617)------------------------------
% 0.20/0.57  % (10588)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.59  % (10594)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 1.81/0.60  % SZS output start Proof for theBenchmark
% 1.81/0.60  fof(f912,plain,(
% 1.81/0.60    $false),
% 1.81/0.60    inference(avatar_sat_refutation,[],[f145,f228,f907])).
% 1.81/0.60  fof(f907,plain,(
% 1.81/0.60    spl2_6),
% 1.81/0.60    inference(avatar_contradiction_clause,[],[f906])).
% 1.81/0.60  fof(f906,plain,(
% 1.81/0.60    $false | spl2_6),
% 1.81/0.60    inference(subsumption_resolution,[],[f143,f783])).
% 1.81/0.60  fof(f783,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))),k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.81/0.60    inference(superposition,[],[f756,f211])).
% 1.81/0.60  fof(f211,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.81/0.60    inference(forward_demodulation,[],[f207,f38])).
% 1.81/0.60  fof(f38,plain,(
% 1.81/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.81/0.60    inference(cnf_transformation,[],[f12])).
% 1.81/0.60  fof(f12,axiom,(
% 1.81/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.81/0.60  fof(f207,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)))) )),
% 1.81/0.60    inference(resolution,[],[f202,f36])).
% 1.81/0.60  fof(f36,plain,(
% 1.81/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.81/0.60    inference(cnf_transformation,[],[f17])).
% 1.81/0.60  fof(f17,axiom,(
% 1.81/0.60    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.81/0.60  fof(f202,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))) )),
% 1.81/0.60    inference(forward_demodulation,[],[f64,f62])).
% 1.81/0.60  fof(f62,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.81/0.60    inference(definition_unfolding,[],[f45,f59])).
% 1.81/0.60  fof(f59,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.81/0.60    inference(definition_unfolding,[],[f43,f58])).
% 1.81/0.60  fof(f58,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.81/0.60    inference(definition_unfolding,[],[f44,f56])).
% 1.81/0.60  fof(f56,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f6])).
% 1.81/0.60  fof(f6,axiom,(
% 1.81/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.81/0.60  fof(f44,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f5])).
% 1.81/0.60  fof(f5,axiom,(
% 1.81/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.81/0.60  fof(f43,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.81/0.60    inference(cnf_transformation,[],[f7])).
% 1.81/0.60  fof(f7,axiom,(
% 1.81/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.81/0.60  fof(f45,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.81/0.60    inference(cnf_transformation,[],[f4])).
% 1.81/0.60  fof(f4,axiom,(
% 1.81/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.81/0.60  fof(f64,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.81/0.60    inference(definition_unfolding,[],[f48,f59])).
% 1.81/0.60  fof(f48,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f24])).
% 1.81/0.60  fof(f24,plain,(
% 1.81/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f10])).
% 1.81/0.60  fof(f10,axiom,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 1.81/0.60  fof(f756,plain,(
% 1.81/0.60    ( ! [X2,X3] : (r1_tarski(k6_relat_1(k4_xboole_0(X2,X3)),k7_relat_1(k6_relat_1(X2),k4_xboole_0(X2,X3)))) )),
% 1.81/0.60    inference(superposition,[],[f732,f95])).
% 1.81/0.60  fof(f95,plain,(
% 1.81/0.60    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.81/0.60    inference(superposition,[],[f91,f70])).
% 1.81/0.60  fof(f70,plain,(
% 1.81/0.60    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.81/0.60    inference(forward_demodulation,[],[f68,f39])).
% 1.81/0.60  fof(f39,plain,(
% 1.81/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.81/0.60    inference(cnf_transformation,[],[f12])).
% 1.81/0.60  fof(f68,plain,(
% 1.81/0.60    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 1.81/0.60    inference(resolution,[],[f40,f36])).
% 1.81/0.60  fof(f40,plain,(
% 1.81/0.60    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.81/0.60    inference(cnf_transformation,[],[f21])).
% 1.81/0.60  fof(f21,plain,(
% 1.81/0.60    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.81/0.60    inference(ennf_transformation,[],[f15])).
% 1.81/0.60  fof(f15,axiom,(
% 1.81/0.60    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.81/0.60  fof(f91,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.81/0.60    inference(resolution,[],[f47,f36])).
% 1.81/0.60  fof(f47,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f23])).
% 1.81/0.60  fof(f23,plain,(
% 1.81/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f16])).
% 1.81/0.60  fof(f16,axiom,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.81/0.60  fof(f732,plain,(
% 1.81/0.60    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(k4_xboole_0(X2,X3)),X4),k7_relat_1(k6_relat_1(X2),X4))) )),
% 1.81/0.60    inference(superposition,[],[f728,f157])).
% 1.81/0.60  fof(f157,plain,(
% 1.81/0.60    ( ! [X6,X5] : (k6_relat_1(k4_xboole_0(X5,X6)) = k7_relat_1(k6_relat_1(k4_xboole_0(X5,X6)),X5)) )),
% 1.81/0.60    inference(resolution,[],[f122,f150])).
% 1.81/0.60  fof(f150,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.81/0.60    inference(superposition,[],[f131,f146])).
% 1.81/0.60  fof(f146,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.81/0.60    inference(forward_demodulation,[],[f63,f62])).
% 1.81/0.60  fof(f63,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.81/0.60    inference(definition_unfolding,[],[f46,f59])).
% 1.81/0.60  fof(f46,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f3])).
% 1.81/0.60  fof(f3,axiom,(
% 1.81/0.60    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.81/0.60  fof(f131,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.81/0.60    inference(backward_demodulation,[],[f61,f62])).
% 1.81/0.60  fof(f61,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.81/0.60    inference(definition_unfolding,[],[f42,f59])).
% 1.81/0.60  fof(f42,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f2])).
% 1.81/0.60  fof(f2,axiom,(
% 1.81/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.81/0.60  fof(f122,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.81/0.60    inference(forward_demodulation,[],[f121,f91])).
% 1.81/0.60  fof(f121,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 1.81/0.60    inference(subsumption_resolution,[],[f120,f36])).
% 1.81/0.60  fof(f120,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.81/0.60    inference(superposition,[],[f51,f38])).
% 1.81/0.60  fof(f51,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f27])).
% 1.81/0.60  fof(f27,plain,(
% 1.81/0.60    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(flattening,[],[f26])).
% 1.81/0.60  fof(f26,plain,(
% 1.81/0.60    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f14])).
% 1.81/0.60  fof(f14,axiom,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 1.81/0.60  fof(f728,plain,(
% 1.81/0.60    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))) )),
% 1.81/0.60    inference(subsumption_resolution,[],[f719,f103])).
% 1.81/0.60  fof(f103,plain,(
% 1.81/0.60    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))) )),
% 1.81/0.60    inference(subsumption_resolution,[],[f102,f36])).
% 1.81/0.60  fof(f102,plain,(
% 1.81/0.60    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 1.81/0.60    inference(subsumption_resolution,[],[f99,f36])).
% 1.81/0.60  fof(f99,plain,(
% 1.81/0.60    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 1.81/0.60    inference(superposition,[],[f52,f91])).
% 1.81/0.60  fof(f52,plain,(
% 1.81/0.60    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f29])).
% 1.81/0.60  fof(f29,plain,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.81/0.60    inference(flattening,[],[f28])).
% 1.81/0.60  fof(f28,plain,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.81/0.60    inference(ennf_transformation,[],[f8])).
% 1.81/0.60  fof(f8,axiom,(
% 1.81/0.60    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.81/0.60  fof(f719,plain,(
% 1.81/0.60    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 1.81/0.60    inference(superposition,[],[f49,f710])).
% 1.81/0.60  fof(f710,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 1.81/0.60    inference(forward_demodulation,[],[f709,f91])).
% 1.81/0.60  fof(f709,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) )),
% 1.81/0.60    inference(forward_demodulation,[],[f702,f116])).
% 1.81/0.60  fof(f116,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.81/0.60    inference(resolution,[],[f103,f47])).
% 1.81/0.60  fof(f702,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.81/0.60    inference(resolution,[],[f393,f36])).
% 1.81/0.60  fof(f393,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.81/0.60    inference(forward_demodulation,[],[f387,f91])).
% 1.81/0.60  fof(f387,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 1.81/0.60    inference(resolution,[],[f181,f36])).
% 1.81/0.60  fof(f181,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 1.81/0.60    inference(resolution,[],[f41,f36])).
% 1.81/0.60  fof(f41,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f22])).
% 1.81/0.60  fof(f22,plain,(
% 1.81/0.60    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.81/0.60    inference(ennf_transformation,[],[f11])).
% 1.81/0.60  fof(f11,axiom,(
% 1.81/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.81/0.60  fof(f49,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f25])).
% 1.81/0.60  fof(f25,plain,(
% 1.81/0.60    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f13])).
% 1.81/0.60  fof(f13,axiom,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 1.81/0.60  fof(f143,plain,(
% 1.81/0.60    ~r1_tarski(k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) | spl2_6),
% 1.81/0.60    inference(avatar_component_clause,[],[f141])).
% 1.81/0.60  fof(f141,plain,(
% 1.81/0.60    spl2_6 <=> r1_tarski(k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.81/0.60  fof(f228,plain,(
% 1.81/0.60    spl2_5),
% 1.81/0.60    inference(avatar_contradiction_clause,[],[f220])).
% 1.81/0.60  fof(f220,plain,(
% 1.81/0.60    $false | spl2_5),
% 1.81/0.60    inference(resolution,[],[f213,f139])).
% 1.81/0.60  fof(f139,plain,(
% 1.81/0.60    ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_5),
% 1.81/0.60    inference(avatar_component_clause,[],[f137])).
% 1.81/0.60  fof(f137,plain,(
% 1.81/0.60    spl2_5 <=> r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.81/0.60  fof(f213,plain,(
% 1.81/0.60    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(k4_xboole_0(X2,k4_xboole_0(X2,X3))))) )),
% 1.81/0.60    inference(superposition,[],[f101,f211])).
% 1.81/0.60  fof(f101,plain,(
% 1.81/0.60    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3))) )),
% 1.81/0.60    inference(subsumption_resolution,[],[f98,f36])).
% 1.81/0.60  fof(f98,plain,(
% 1.81/0.60    ( ! [X4,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 1.81/0.60    inference(superposition,[],[f49,f91])).
% 1.81/0.60  fof(f145,plain,(
% 1.81/0.60    ~spl2_6 | ~spl2_5),
% 1.81/0.60    inference(avatar_split_clause,[],[f135,f137,f141])).
% 1.81/0.60  fof(f135,plain,(
% 1.81/0.60    ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~r1_tarski(k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))),
% 1.81/0.60    inference(extensionality_resolution,[],[f55,f132])).
% 1.81/0.60  fof(f132,plain,(
% 1.81/0.60    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.81/0.60    inference(backward_demodulation,[],[f94,f62])).
% 1.81/0.60  fof(f94,plain,(
% 1.81/0.60    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.81/0.60    inference(backward_demodulation,[],[f60,f91])).
% 1.81/0.60  fof(f60,plain,(
% 1.81/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.81/0.60    inference(definition_unfolding,[],[f35,f59])).
% 1.81/0.60  fof(f35,plain,(
% 1.81/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.81/0.60    inference(cnf_transformation,[],[f32])).
% 1.81/0.60  fof(f32,plain,(
% 1.81/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.81/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).
% 1.81/0.60  fof(f31,plain,(
% 1.81/0.60    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.81/0.60    introduced(choice_axiom,[])).
% 1.81/0.60  fof(f20,plain,(
% 1.81/0.60    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f19])).
% 1.81/0.60  fof(f19,negated_conjecture,(
% 1.81/0.60    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.81/0.60    inference(negated_conjecture,[],[f18])).
% 1.81/0.60  fof(f18,conjecture,(
% 1.81/0.60    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.81/0.60  fof(f55,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f34])).
% 1.81/0.60  fof(f34,plain,(
% 1.81/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.60    inference(flattening,[],[f33])).
% 1.81/0.60  fof(f33,plain,(
% 1.81/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.60    inference(nnf_transformation,[],[f1])).
% 1.81/0.60  fof(f1,axiom,(
% 1.81/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.81/0.60  % SZS output end Proof for theBenchmark
% 1.81/0.60  % (10594)------------------------------
% 1.81/0.60  % (10594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (10594)Termination reason: Refutation
% 1.81/0.60  
% 1.81/0.60  % (10594)Memory used [KB]: 11513
% 1.81/0.60  % (10594)Time elapsed: 0.164 s
% 1.81/0.60  % (10594)------------------------------
% 1.81/0.60  % (10594)------------------------------
% 1.81/0.61  % (10587)Success in time 0.235 s
%------------------------------------------------------------------------------
