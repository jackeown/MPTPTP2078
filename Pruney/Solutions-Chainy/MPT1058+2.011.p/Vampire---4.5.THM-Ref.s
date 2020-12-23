%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:18 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  108 (1557 expanded)
%              Number of leaves         :   20 ( 474 expanded)
%              Depth                    :   29
%              Number of atoms          :  235 (2473 expanded)
%              Number of equality atoms :   78 (1290 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1266,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f77,f121,f1265])).

fof(f1265,plain,
    ( ~ spl3_2
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f1264])).

fof(f1264,plain,
    ( $false
    | ~ spl3_2
    | spl3_8 ),
    inference(subsumption_resolution,[],[f1257,f66])).

fof(f66,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_2
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1257,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | spl3_8 ),
    inference(trivial_inequality_removal,[],[f1256])).

fof(f1256,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2)
    | ~ r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | spl3_8 ),
    inference(superposition,[],[f120,f1087])).

fof(f1087,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X2,X1) = X1
      | ~ r1_tarski(X1,X2) ) ),
    inference(subsumption_resolution,[],[f1079,f605])).

fof(f605,plain,(
    ! [X14,X13] : r1_tarski(k3_xboole_0(X14,X13),X13) ),
    inference(superposition,[],[f98,f435])).

fof(f435,plain,(
    ! [X2,X3] : k3_xboole_0(X3,X2) = k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f423,f141])).

fof(f141,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k9_relat_1(k6_relat_1(X3),X4) ),
    inference(forward_demodulation,[],[f140,f53])).

fof(f53,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f140,plain,(
    ! [X4,X3] : k9_relat_1(k6_relat_1(X3),X4) = k2_relat_1(k6_relat_1(k3_xboole_0(X3,X4))) ),
    inference(subsumption_resolution,[],[f138,f49])).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f138,plain,(
    ! [X4,X3] :
      ( k9_relat_1(k6_relat_1(X3),X4) = k2_relat_1(k6_relat_1(k3_xboole_0(X3,X4)))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f44,f113])).

fof(f113,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k3_xboole_0(X3,X2)) ),
    inference(subsumption_resolution,[],[f111,f49])).

fof(f111,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k3_xboole_0(X3,X2))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f51,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f51,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f423,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(backward_demodulation,[],[f180,f408])).

fof(f408,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f398,f55])).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f398,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f134,f339])).

fof(f339,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f338,f97])).

fof(f97,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f43,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f48,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f338,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f332,f141])).

fof(f332,plain,(
    ! [X2] : k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k9_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f180,f307])).

fof(f307,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(k6_relat_1(k1_xboole_0),X2) ),
    inference(superposition,[],[f279,f55])).

fof(f279,plain,(
    ! [X8,X7] : k1_xboole_0 = k10_relat_1(k6_relat_1(k4_xboole_0(X7,X7)),X8) ),
    inference(forward_demodulation,[],[f272,f97])).

fof(f272,plain,(
    ! [X8,X7] : k3_xboole_0(k1_xboole_0,k10_relat_1(k6_relat_1(X7),X8)) = k10_relat_1(k6_relat_1(k4_xboole_0(X7,X7)),X8) ),
    inference(superposition,[],[f139,f94])).

fof(f94,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f43,f55])).

fof(f139,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) ),
    inference(subsumption_resolution,[],[f137,f49])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f38,f113])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f134,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f43,f94])).

fof(f180,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) ),
    inference(backward_demodulation,[],[f128,f141])).

fof(f128,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0)) ),
    inference(subsumption_resolution,[],[f127,f49])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f122,f50])).

fof(f50,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f42,f52])).

fof(f52,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f98,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f47,f43])).

fof(f1079,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k3_xboole_0(X2,X1) = X1
      | ~ r1_tarski(k3_xboole_0(X2,X1),X1) ) ),
    inference(resolution,[],[f955,f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f955,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,k3_xboole_0(X3,X2))
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f746,f408])).

fof(f746,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k3_xboole_0(X7,X6),k3_xboole_0(X8,X6))
      | ~ r1_tarski(k3_xboole_0(X7,X6),X8) ) ),
    inference(subsumption_resolution,[],[f745,f605])).

fof(f745,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k3_xboole_0(X7,X6),X6)
      | r1_tarski(k3_xboole_0(X7,X6),k3_xboole_0(X8,X6))
      | ~ r1_tarski(k3_xboole_0(X7,X6),X8) ) ),
    inference(forward_demodulation,[],[f744,f723])).

fof(f723,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f425,f435])).

fof(f425,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f139,f408])).

fof(f744,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k3_xboole_0(X7,X6),k3_xboole_0(X8,X6))
      | ~ r1_tarski(k3_xboole_0(X7,X6),X8)
      | ~ r1_tarski(k10_relat_1(k6_relat_1(X6),X7),X6) ) ),
    inference(forward_demodulation,[],[f726,f723])).

fof(f726,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k3_xboole_0(X7,X6),k10_relat_1(k6_relat_1(X6),X8))
      | ~ r1_tarski(k3_xboole_0(X7,X6),X8)
      | ~ r1_tarski(k10_relat_1(k6_relat_1(X6),X7),X6) ) ),
    inference(backward_demodulation,[],[f421,f723])).

fof(f421,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k10_relat_1(k6_relat_1(X6),X8))
      | ~ r1_tarski(k3_xboole_0(X7,X6),X8)
      | ~ r1_tarski(k10_relat_1(k6_relat_1(X6),X7),X6) ) ),
    inference(backward_demodulation,[],[f212,f408])).

fof(f212,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k10_relat_1(k6_relat_1(X6),X8))
      | ~ r1_tarski(k3_xboole_0(X7,k3_xboole_0(X6,X6)),X8)
      | ~ r1_tarski(k10_relat_1(k6_relat_1(X6),X7),X6) ) ),
    inference(forward_demodulation,[],[f211,f52])).

fof(f211,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k3_xboole_0(X7,k3_xboole_0(X6,X6)),X8)
      | r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k10_relat_1(k6_relat_1(X6),X8))
      | ~ r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k1_relat_1(k6_relat_1(X6))) ) ),
    inference(subsumption_resolution,[],[f210,f49])).

fof(f210,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k3_xboole_0(X7,k3_xboole_0(X6,X6)),X8)
      | r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k10_relat_1(k6_relat_1(X6),X8))
      | ~ r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k1_relat_1(k6_relat_1(X6)))
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(subsumption_resolution,[],[f202,f50])).

fof(f202,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k3_xboole_0(X7,k3_xboole_0(X6,X6)),X8)
      | r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k10_relat_1(k6_relat_1(X6),X8))
      | ~ r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k1_relat_1(k6_relat_1(X6)))
      | ~ v1_funct_1(k6_relat_1(X6))
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(superposition,[],[f46,f180])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f120,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_8
  <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f121,plain,
    ( ~ spl3_8
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f116,f74,f59,f118])).

fof(f59,plain,
    ( spl3_1
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f74,plain,
    ( spl3_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f116,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f115,f76])).

fof(f76,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f115,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(superposition,[],[f61,f38])).

fof(f61,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f77,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f34,f74])).

fof(f34,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f67,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f36,f64])).

fof(f36,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f37,f59])).

fof(f37,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (23659)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.49  % (23667)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (23654)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (23652)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (23657)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (23653)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (23673)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (23676)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (23672)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (23664)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (23664)Refutation not found, incomplete strategy% (23664)------------------------------
% 0.21/0.52  % (23664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23664)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23664)Memory used [KB]: 1663
% 0.21/0.52  % (23664)Time elapsed: 0.081 s
% 0.21/0.52  % (23664)------------------------------
% 0.21/0.52  % (23664)------------------------------
% 0.21/0.52  % (23675)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (23663)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (23650)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (23656)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (23660)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (23680)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (23660)Refutation not found, incomplete strategy% (23660)------------------------------
% 0.21/0.53  % (23660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23660)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23660)Memory used [KB]: 10746
% 0.21/0.53  % (23660)Time elapsed: 0.115 s
% 0.21/0.53  % (23660)------------------------------
% 0.21/0.53  % (23660)------------------------------
% 0.21/0.53  % (23680)Refutation not found, incomplete strategy% (23680)------------------------------
% 0.21/0.53  % (23680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23680)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23680)Memory used [KB]: 1663
% 0.21/0.53  % (23680)Time elapsed: 0.129 s
% 0.21/0.53  % (23680)------------------------------
% 0.21/0.53  % (23680)------------------------------
% 0.21/0.53  % (23655)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (23679)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (23678)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (23666)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (23679)Refutation not found, incomplete strategy% (23679)------------------------------
% 0.21/0.53  % (23679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23679)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23679)Memory used [KB]: 10746
% 0.21/0.53  % (23679)Time elapsed: 0.125 s
% 0.21/0.53  % (23679)------------------------------
% 0.21/0.53  % (23679)------------------------------
% 0.21/0.54  % (23666)Refutation not found, incomplete strategy% (23666)------------------------------
% 0.21/0.54  % (23666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23666)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23666)Memory used [KB]: 10618
% 0.21/0.54  % (23666)Time elapsed: 0.105 s
% 0.21/0.54  % (23666)------------------------------
% 0.21/0.54  % (23666)------------------------------
% 0.21/0.54  % (23658)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (23674)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (23670)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (23669)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (23665)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (23662)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (23651)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (23661)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (23651)Refutation not found, incomplete strategy% (23651)------------------------------
% 0.21/0.55  % (23651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23651)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23651)Memory used [KB]: 1663
% 0.21/0.55  % (23651)Time elapsed: 0.145 s
% 0.21/0.55  % (23651)------------------------------
% 0.21/0.55  % (23651)------------------------------
% 0.21/0.55  % (23662)Refutation not found, incomplete strategy% (23662)------------------------------
% 0.21/0.55  % (23662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23662)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23662)Memory used [KB]: 10618
% 0.21/0.55  % (23662)Time elapsed: 0.149 s
% 0.21/0.55  % (23662)------------------------------
% 0.21/0.55  % (23662)------------------------------
% 1.51/0.55  % (23667)Refutation not found, incomplete strategy% (23667)------------------------------
% 1.51/0.55  % (23667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (23667)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (23667)Memory used [KB]: 2558
% 1.51/0.55  % (23667)Time elapsed: 0.143 s
% 1.51/0.55  % (23667)------------------------------
% 1.51/0.55  % (23667)------------------------------
% 1.51/0.56  % (23677)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.51/0.56  % (23677)Refutation not found, incomplete strategy% (23677)------------------------------
% 1.51/0.56  % (23677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (23677)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (23677)Memory used [KB]: 6268
% 1.51/0.56  % (23677)Time elapsed: 0.159 s
% 1.51/0.56  % (23677)------------------------------
% 1.51/0.56  % (23677)------------------------------
% 1.51/0.56  % (23668)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.51/0.57  % (23668)Refutation not found, incomplete strategy% (23668)------------------------------
% 1.51/0.57  % (23668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (23668)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (23668)Memory used [KB]: 1791
% 1.51/0.57  % (23668)Time elapsed: 0.161 s
% 1.51/0.57  % (23668)------------------------------
% 1.51/0.57  % (23668)------------------------------
% 1.70/0.59  % (23672)Refutation found. Thanks to Tanya!
% 1.70/0.59  % SZS status Theorem for theBenchmark
% 1.70/0.59  % SZS output start Proof for theBenchmark
% 1.70/0.59  fof(f1266,plain,(
% 1.70/0.59    $false),
% 1.70/0.59    inference(avatar_sat_refutation,[],[f62,f67,f77,f121,f1265])).
% 1.70/0.59  fof(f1265,plain,(
% 1.70/0.59    ~spl3_2 | spl3_8),
% 1.70/0.59    inference(avatar_contradiction_clause,[],[f1264])).
% 1.70/0.59  fof(f1264,plain,(
% 1.70/0.59    $false | (~spl3_2 | spl3_8)),
% 1.70/0.59    inference(subsumption_resolution,[],[f1257,f66])).
% 1.70/0.59  fof(f66,plain,(
% 1.70/0.59    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_2),
% 1.70/0.59    inference(avatar_component_clause,[],[f64])).
% 1.70/0.59  fof(f64,plain,(
% 1.70/0.59    spl3_2 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.70/0.59  fof(f1257,plain,(
% 1.70/0.59    ~r1_tarski(k10_relat_1(sK0,sK2),sK1) | spl3_8),
% 1.70/0.59    inference(trivial_inequality_removal,[],[f1256])).
% 1.70/0.59  fof(f1256,plain,(
% 1.70/0.59    k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) | ~r1_tarski(k10_relat_1(sK0,sK2),sK1) | spl3_8),
% 1.70/0.59    inference(superposition,[],[f120,f1087])).
% 1.70/0.59  fof(f1087,plain,(
% 1.70/0.59    ( ! [X2,X1] : (k3_xboole_0(X2,X1) = X1 | ~r1_tarski(X1,X2)) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f1079,f605])).
% 1.70/0.59  fof(f605,plain,(
% 1.70/0.59    ( ! [X14,X13] : (r1_tarski(k3_xboole_0(X14,X13),X13)) )),
% 1.70/0.59    inference(superposition,[],[f98,f435])).
% 1.70/0.59  fof(f435,plain,(
% 1.70/0.59    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3))) )),
% 1.70/0.59    inference(superposition,[],[f423,f141])).
% 1.70/0.59  fof(f141,plain,(
% 1.70/0.59    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k9_relat_1(k6_relat_1(X3),X4)) )),
% 1.70/0.59    inference(forward_demodulation,[],[f140,f53])).
% 1.70/0.59  fof(f53,plain,(
% 1.70/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f10])).
% 1.70/0.59  fof(f10,axiom,(
% 1.70/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.70/0.59  fof(f140,plain,(
% 1.70/0.59    ( ! [X4,X3] : (k9_relat_1(k6_relat_1(X3),X4) = k2_relat_1(k6_relat_1(k3_xboole_0(X3,X4)))) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f138,f49])).
% 1.70/0.59  fof(f49,plain,(
% 1.70/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f12])).
% 1.70/0.59  fof(f12,axiom,(
% 1.70/0.59    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.70/0.59  fof(f138,plain,(
% 1.70/0.59    ( ! [X4,X3] : (k9_relat_1(k6_relat_1(X3),X4) = k2_relat_1(k6_relat_1(k3_xboole_0(X3,X4))) | ~v1_relat_1(k6_relat_1(X3))) )),
% 1.70/0.59    inference(superposition,[],[f44,f113])).
% 1.70/0.59  fof(f113,plain,(
% 1.70/0.59    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k3_xboole_0(X3,X2))) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f111,f49])).
% 1.70/0.59  fof(f111,plain,(
% 1.70/0.59    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k3_xboole_0(X3,X2)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 1.70/0.59    inference(superposition,[],[f51,f45])).
% 1.70/0.59  fof(f45,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f25])).
% 1.70/0.59  fof(f25,plain,(
% 1.70/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.70/0.59    inference(ennf_transformation,[],[f11])).
% 1.70/0.59  fof(f11,axiom,(
% 1.70/0.59    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.70/0.59  fof(f51,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f16])).
% 1.70/0.59  fof(f16,axiom,(
% 1.70/0.59    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.70/0.59  fof(f44,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f24])).
% 1.70/0.59  fof(f24,plain,(
% 1.70/0.59    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.70/0.59    inference(ennf_transformation,[],[f9])).
% 1.70/0.59  fof(f9,axiom,(
% 1.70/0.59    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.70/0.59  fof(f423,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1))) )),
% 1.70/0.59    inference(backward_demodulation,[],[f180,f408])).
% 1.70/0.59  fof(f408,plain,(
% 1.70/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.70/0.59    inference(forward_demodulation,[],[f398,f55])).
% 1.70/0.59  fof(f55,plain,(
% 1.70/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f4])).
% 1.70/0.59  fof(f4,axiom,(
% 1.70/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.70/0.59  fof(f398,plain,(
% 1.70/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 1.70/0.59    inference(backward_demodulation,[],[f134,f339])).
% 1.70/0.59  fof(f339,plain,(
% 1.70/0.59    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) )),
% 1.70/0.59    inference(forward_demodulation,[],[f338,f97])).
% 1.70/0.59  fof(f97,plain,(
% 1.70/0.59    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 1.70/0.59    inference(superposition,[],[f43,f80])).
% 1.70/0.59  fof(f80,plain,(
% 1.70/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.70/0.59    inference(resolution,[],[f48,f47])).
% 1.70/0.59  fof(f47,plain,(
% 1.70/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f3])).
% 1.70/0.59  fof(f3,axiom,(
% 1.70/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.70/0.59  fof(f48,plain,(
% 1.70/0.59    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f28])).
% 1.70/0.59  fof(f28,plain,(
% 1.70/0.59    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.70/0.59    inference(ennf_transformation,[],[f5])).
% 1.70/0.59  fof(f5,axiom,(
% 1.70/0.59    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.70/0.59  fof(f43,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f6])).
% 1.70/0.59  fof(f6,axiom,(
% 1.70/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.70/0.59  fof(f338,plain,(
% 1.70/0.59    ( ! [X2] : (k3_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.70/0.59    inference(forward_demodulation,[],[f332,f141])).
% 1.70/0.59  fof(f332,plain,(
% 1.70/0.59    ( ! [X2] : (k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k9_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0)) )),
% 1.70/0.59    inference(superposition,[],[f180,f307])).
% 1.70/0.59  fof(f307,plain,(
% 1.70/0.59    ( ! [X2] : (k1_xboole_0 = k10_relat_1(k6_relat_1(k1_xboole_0),X2)) )),
% 1.70/0.59    inference(superposition,[],[f279,f55])).
% 1.70/0.59  fof(f279,plain,(
% 1.70/0.59    ( ! [X8,X7] : (k1_xboole_0 = k10_relat_1(k6_relat_1(k4_xboole_0(X7,X7)),X8)) )),
% 1.70/0.59    inference(forward_demodulation,[],[f272,f97])).
% 1.70/0.59  fof(f272,plain,(
% 1.70/0.59    ( ! [X8,X7] : (k3_xboole_0(k1_xboole_0,k10_relat_1(k6_relat_1(X7),X8)) = k10_relat_1(k6_relat_1(k4_xboole_0(X7,X7)),X8)) )),
% 1.70/0.59    inference(superposition,[],[f139,f94])).
% 1.70/0.59  fof(f94,plain,(
% 1.70/0.59    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.70/0.59    inference(superposition,[],[f43,f55])).
% 1.70/0.59  fof(f139,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2)) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f137,f49])).
% 1.70/0.59  fof(f137,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.70/0.59    inference(superposition,[],[f38,f113])).
% 1.70/0.59  fof(f38,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f21])).
% 1.70/0.59  fof(f21,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.70/0.59    inference(ennf_transformation,[],[f13])).
% 1.70/0.59  fof(f13,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.70/0.59  fof(f134,plain,(
% 1.70/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 1.70/0.59    inference(superposition,[],[f43,f94])).
% 1.70/0.59  fof(f180,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0))) )),
% 1.70/0.59    inference(backward_demodulation,[],[f128,f141])).
% 1.70/0.59  fof(f128,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0))) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f127,f49])).
% 1.70/0.59  fof(f127,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f122,f50])).
% 1.70/0.59  fof(f50,plain,(
% 1.70/0.59    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f12])).
% 1.70/0.59  fof(f122,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.70/0.59    inference(superposition,[],[f42,f52])).
% 1.70/0.59  fof(f52,plain,(
% 1.70/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f10])).
% 1.70/0.59  fof(f42,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f23])).
% 1.70/0.59  fof(f23,plain,(
% 1.70/0.59    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.70/0.59    inference(flattening,[],[f22])).
% 1.70/0.59  fof(f22,plain,(
% 1.70/0.59    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.70/0.59    inference(ennf_transformation,[],[f14])).
% 1.70/0.59  fof(f14,axiom,(
% 1.70/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 1.70/0.59  fof(f98,plain,(
% 1.70/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.70/0.59    inference(superposition,[],[f47,f43])).
% 1.70/0.59  fof(f1079,plain,(
% 1.70/0.59    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k3_xboole_0(X2,X1) = X1 | ~r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 1.70/0.59    inference(resolution,[],[f955,f41])).
% 1.70/0.59  fof(f41,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f33])).
% 1.70/0.59  fof(f33,plain,(
% 1.70/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.70/0.59    inference(flattening,[],[f32])).
% 1.70/0.59  fof(f32,plain,(
% 1.70/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.70/0.59    inference(nnf_transformation,[],[f1])).
% 1.70/0.59  fof(f1,axiom,(
% 1.70/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.70/0.59  fof(f955,plain,(
% 1.70/0.59    ( ! [X2,X3] : (r1_tarski(X2,k3_xboole_0(X3,X2)) | ~r1_tarski(X2,X3)) )),
% 1.70/0.59    inference(superposition,[],[f746,f408])).
% 1.70/0.59  fof(f746,plain,(
% 1.70/0.59    ( ! [X6,X8,X7] : (r1_tarski(k3_xboole_0(X7,X6),k3_xboole_0(X8,X6)) | ~r1_tarski(k3_xboole_0(X7,X6),X8)) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f745,f605])).
% 1.70/0.59  fof(f745,plain,(
% 1.70/0.59    ( ! [X6,X8,X7] : (~r1_tarski(k3_xboole_0(X7,X6),X6) | r1_tarski(k3_xboole_0(X7,X6),k3_xboole_0(X8,X6)) | ~r1_tarski(k3_xboole_0(X7,X6),X8)) )),
% 1.70/0.59    inference(forward_demodulation,[],[f744,f723])).
% 1.70/0.59  fof(f723,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 1.70/0.59    inference(forward_demodulation,[],[f425,f435])).
% 1.70/0.59  fof(f425,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 1.70/0.59    inference(superposition,[],[f139,f408])).
% 1.70/0.59  fof(f744,plain,(
% 1.70/0.59    ( ! [X6,X8,X7] : (r1_tarski(k3_xboole_0(X7,X6),k3_xboole_0(X8,X6)) | ~r1_tarski(k3_xboole_0(X7,X6),X8) | ~r1_tarski(k10_relat_1(k6_relat_1(X6),X7),X6)) )),
% 1.70/0.59    inference(forward_demodulation,[],[f726,f723])).
% 1.70/0.59  fof(f726,plain,(
% 1.70/0.59    ( ! [X6,X8,X7] : (r1_tarski(k3_xboole_0(X7,X6),k10_relat_1(k6_relat_1(X6),X8)) | ~r1_tarski(k3_xboole_0(X7,X6),X8) | ~r1_tarski(k10_relat_1(k6_relat_1(X6),X7),X6)) )),
% 1.70/0.59    inference(backward_demodulation,[],[f421,f723])).
% 1.70/0.59  fof(f421,plain,(
% 1.70/0.59    ( ! [X6,X8,X7] : (r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k10_relat_1(k6_relat_1(X6),X8)) | ~r1_tarski(k3_xboole_0(X7,X6),X8) | ~r1_tarski(k10_relat_1(k6_relat_1(X6),X7),X6)) )),
% 1.70/0.59    inference(backward_demodulation,[],[f212,f408])).
% 1.70/0.59  fof(f212,plain,(
% 1.70/0.59    ( ! [X6,X8,X7] : (r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k10_relat_1(k6_relat_1(X6),X8)) | ~r1_tarski(k3_xboole_0(X7,k3_xboole_0(X6,X6)),X8) | ~r1_tarski(k10_relat_1(k6_relat_1(X6),X7),X6)) )),
% 1.70/0.59    inference(forward_demodulation,[],[f211,f52])).
% 1.70/0.59  fof(f211,plain,(
% 1.70/0.59    ( ! [X6,X8,X7] : (~r1_tarski(k3_xboole_0(X7,k3_xboole_0(X6,X6)),X8) | r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k10_relat_1(k6_relat_1(X6),X8)) | ~r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k1_relat_1(k6_relat_1(X6)))) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f210,f49])).
% 1.70/0.59  fof(f210,plain,(
% 1.70/0.59    ( ! [X6,X8,X7] : (~r1_tarski(k3_xboole_0(X7,k3_xboole_0(X6,X6)),X8) | r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k10_relat_1(k6_relat_1(X6),X8)) | ~r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k1_relat_1(k6_relat_1(X6))) | ~v1_relat_1(k6_relat_1(X6))) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f202,f50])).
% 1.70/0.59  fof(f202,plain,(
% 1.70/0.59    ( ! [X6,X8,X7] : (~r1_tarski(k3_xboole_0(X7,k3_xboole_0(X6,X6)),X8) | r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k10_relat_1(k6_relat_1(X6),X8)) | ~r1_tarski(k10_relat_1(k6_relat_1(X6),X7),k1_relat_1(k6_relat_1(X6))) | ~v1_funct_1(k6_relat_1(X6)) | ~v1_relat_1(k6_relat_1(X6))) )),
% 1.70/0.59    inference(superposition,[],[f46,f180])).
% 1.70/0.59  fof(f46,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f27])).
% 1.70/0.59  fof(f27,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.70/0.59    inference(flattening,[],[f26])).
% 1.70/0.59  fof(f26,plain,(
% 1.70/0.59    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.70/0.59    inference(ennf_transformation,[],[f15])).
% 1.70/0.59  fof(f15,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 1.70/0.59  fof(f120,plain,(
% 1.70/0.59    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | spl3_8),
% 1.70/0.59    inference(avatar_component_clause,[],[f118])).
% 1.70/0.59  fof(f118,plain,(
% 1.70/0.59    spl3_8 <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.70/0.59  fof(f121,plain,(
% 1.70/0.59    ~spl3_8 | spl3_1 | ~spl3_4),
% 1.70/0.59    inference(avatar_split_clause,[],[f116,f74,f59,f118])).
% 1.70/0.59  fof(f59,plain,(
% 1.70/0.59    spl3_1 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.70/0.59  fof(f74,plain,(
% 1.70/0.59    spl3_4 <=> v1_relat_1(sK0)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.70/0.59  fof(f116,plain,(
% 1.70/0.59    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | (spl3_1 | ~spl3_4)),
% 1.70/0.59    inference(subsumption_resolution,[],[f115,f76])).
% 1.70/0.59  fof(f76,plain,(
% 1.70/0.59    v1_relat_1(sK0) | ~spl3_4),
% 1.70/0.59    inference(avatar_component_clause,[],[f74])).
% 1.70/0.59  fof(f115,plain,(
% 1.70/0.59    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~v1_relat_1(sK0) | spl3_1),
% 1.70/0.59    inference(superposition,[],[f61,f38])).
% 1.70/0.59  fof(f61,plain,(
% 1.70/0.59    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_1),
% 1.70/0.59    inference(avatar_component_clause,[],[f59])).
% 1.70/0.59  fof(f77,plain,(
% 1.70/0.59    spl3_4),
% 1.70/0.59    inference(avatar_split_clause,[],[f34,f74])).
% 1.70/0.59  fof(f34,plain,(
% 1.70/0.59    v1_relat_1(sK0)),
% 1.70/0.59    inference(cnf_transformation,[],[f31])).
% 1.70/0.59  fof(f31,plain,(
% 1.70/0.59    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.70/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f30,f29])).
% 1.70/0.59  fof(f29,plain,(
% 1.70/0.59    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.59  fof(f30,plain,(
% 1.70/0.59    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.60  fof(f20,plain,(
% 1.70/0.60    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.70/0.60    inference(flattening,[],[f19])).
% 1.70/0.61  fof(f19,plain,(
% 1.70/0.61    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.70/0.61    inference(ennf_transformation,[],[f18])).
% 1.70/0.61  fof(f18,negated_conjecture,(
% 1.70/0.61    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.70/0.61    inference(negated_conjecture,[],[f17])).
% 1.70/0.61  fof(f17,conjecture,(
% 1.70/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.70/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 1.70/0.61  fof(f67,plain,(
% 1.70/0.61    spl3_2),
% 1.70/0.61    inference(avatar_split_clause,[],[f36,f64])).
% 1.70/0.61  fof(f36,plain,(
% 1.70/0.61    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.70/0.61    inference(cnf_transformation,[],[f31])).
% 1.70/0.61  fof(f62,plain,(
% 1.70/0.61    ~spl3_1),
% 1.70/0.61    inference(avatar_split_clause,[],[f37,f59])).
% 1.70/0.61  fof(f37,plain,(
% 1.70/0.61    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.70/0.61    inference(cnf_transformation,[],[f31])).
% 1.70/0.61  % SZS output end Proof for theBenchmark
% 1.70/0.61  % (23672)------------------------------
% 1.70/0.61  % (23672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.61  % (23672)Termination reason: Refutation
% 1.70/0.61  
% 1.70/0.61  % (23672)Memory used [KB]: 7036
% 1.70/0.61  % (23672)Time elapsed: 0.198 s
% 1.70/0.61  % (23672)------------------------------
% 1.70/0.61  % (23672)------------------------------
% 1.70/0.61  % (23649)Success in time 0.251 s
%------------------------------------------------------------------------------
