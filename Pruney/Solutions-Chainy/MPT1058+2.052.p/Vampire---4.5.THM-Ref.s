%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 424 expanded)
%              Number of leaves         :   17 ( 127 expanded)
%              Depth                    :   14
%              Number of atoms          :  186 ( 731 expanded)
%              Number of equality atoms :   63 ( 334 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f596,plain,(
    $false ),
    inference(subsumption_resolution,[],[f586,f476])).

fof(f476,plain,(
    ! [X0] : ~ r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),X0)) ),
    inference(unit_resulting_resolution,[],[f122,f203,f400,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X0)
      | ~ r1_tarski(X1,X2)
      | X1 = X2 ) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f400,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(backward_demodulation,[],[f69,f389])).

fof(f389,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k3_xboole_0(X2,X1) ),
    inference(forward_demodulation,[],[f378,f324])).

fof(f324,plain,(
    ! [X2,X3] : k3_xboole_0(X3,X2) = k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f267,f106])).

fof(f106,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f105,f60])).

fof(f60,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f105,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f101,f104])).

fof(f104,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f103,f57])).

fof(f57,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f103,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f55,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f55,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f101,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f55,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f267,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(backward_demodulation,[],[f138,f262])).

fof(f262,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f106,f131])).

fof(f131,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f130,f95])).

fof(f95,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f94,f59])).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f94,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f91,f60])).

fof(f91,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f55,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f130,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0 ),
    inference(forward_demodulation,[],[f125,f60])).

fof(f125,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f55,f56,f64,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f138,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f137,f59])).

fof(f137,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_relat_1(k6_relat_1(X0)))) ),
    inference(forward_demodulation,[],[f134,f106])).

fof(f134,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f56,f55,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f378,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(superposition,[],[f113,f262])).

fof(f113,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) ),
    inference(forward_demodulation,[],[f110,f104])).

fof(f110,plain,(
    ! [X2,X0,X1] : k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) ),
    inference(unit_resulting_resolution,[],[f55,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(forward_demodulation,[],[f67,f59])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f55,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f203,plain,(
    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f39,f109])).

fof(f109,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1)) ),
    inference(unit_resulting_resolution,[],[f40,f45])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f39,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f122,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f63,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f58,f61,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f586,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),sK1)) ),
    inference(unit_resulting_resolution,[],[f38,f64,f402])).

fof(f402,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(X3,k3_xboole_0(X4,X2))
      | ~ r1_tarski(k3_xboole_0(X2,X3),X4)
      | ~ r1_tarski(X3,X2) ) ),
    inference(backward_demodulation,[],[f166,f389])).

fof(f166,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X2,X3),X4)
      | ~ r1_tarski(X3,X2)
      | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4)) ) ),
    inference(forward_demodulation,[],[f165,f106])).

fof(f165,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | ~ r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4)
      | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4)) ) ),
    inference(forward_demodulation,[],[f164,f59])).

fof(f164,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,k1_relat_1(k6_relat_1(X2)))
      | ~ r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4)
      | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4)) ) ),
    inference(subsumption_resolution,[],[f155,f55])).

fof(f155,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(k6_relat_1(X2))
      | ~ r1_tarski(X3,k1_relat_1(k6_relat_1(X2)))
      | ~ r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4)
      | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4)) ) ),
    inference(resolution,[],[f49,f56])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f38,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:02:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (31756)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (31765)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (31772)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (31752)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (31771)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (31749)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (31775)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (31773)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (31750)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (31751)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (31754)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (31763)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (31757)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (31776)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (31755)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (31767)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (31758)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (31769)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (31777)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (31764)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (31768)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (31766)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (31770)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (31759)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (31761)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.56  % (31762)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.56  % (31774)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.56  % (31760)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (31753)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.56  % (31778)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.56  % (31775)Refutation not found, incomplete strategy% (31775)------------------------------
% 0.20/0.56  % (31775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (31775)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (31775)Memory used [KB]: 6268
% 0.20/0.56  % (31775)Time elapsed: 0.149 s
% 0.20/0.56  % (31775)------------------------------
% 0.20/0.56  % (31775)------------------------------
% 0.20/0.61  % (31768)Refutation found. Thanks to Tanya!
% 0.20/0.61  % SZS status Theorem for theBenchmark
% 0.20/0.61  % SZS output start Proof for theBenchmark
% 0.20/0.61  fof(f596,plain,(
% 0.20/0.61    $false),
% 0.20/0.61    inference(subsumption_resolution,[],[f586,f476])).
% 0.20/0.61  fof(f476,plain,(
% 0.20/0.61    ( ! [X0] : (~r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),X0))) )),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f122,f203,f400,f88])).
% 0.20/0.61  fof(f88,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X0) | ~r1_tarski(X1,X2) | X1 = X2) )),
% 0.20/0.61    inference(resolution,[],[f48,f44])).
% 0.20/0.61  fof(f44,plain,(
% 0.20/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.61    inference(cnf_transformation,[],[f1])).
% 0.20/0.61  fof(f1,axiom,(
% 0.20/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.61  fof(f48,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f29])).
% 0.20/0.61  fof(f29,plain,(
% 0.20/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.61    inference(flattening,[],[f28])).
% 0.20/0.61  fof(f28,plain,(
% 0.20/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.61    inference(ennf_transformation,[],[f3])).
% 0.20/0.61  fof(f3,axiom,(
% 0.20/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.61  fof(f400,plain,(
% 0.20/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.20/0.61    inference(backward_demodulation,[],[f69,f389])).
% 0.20/0.61  fof(f389,plain,(
% 0.20/0.61    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k3_xboole_0(X2,X1)) )),
% 0.20/0.61    inference(forward_demodulation,[],[f378,f324])).
% 0.20/0.61  fof(f324,plain,(
% 0.20/0.61    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3))) )),
% 0.20/0.61    inference(superposition,[],[f267,f106])).
% 0.20/0.61  fof(f106,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.61    inference(forward_demodulation,[],[f105,f60])).
% 0.20/0.61  fof(f60,plain,(
% 0.20/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.61    inference(cnf_transformation,[],[f13])).
% 0.20/0.61  fof(f13,axiom,(
% 0.20/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.61  fof(f105,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1)))) )),
% 0.20/0.61    inference(backward_demodulation,[],[f101,f104])).
% 0.20/0.61  fof(f104,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.61    inference(forward_demodulation,[],[f103,f57])).
% 0.20/0.61  fof(f57,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f20])).
% 0.20/0.61  fof(f20,axiom,(
% 0.20/0.61    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.61  fof(f103,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f55,f47])).
% 0.20/0.61  fof(f47,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f27])).
% 0.20/0.61  fof(f27,plain,(
% 0.20/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.61    inference(ennf_transformation,[],[f14])).
% 0.20/0.61  fof(f14,axiom,(
% 0.20/0.61    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.61  fof(f55,plain,(
% 0.20/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f15])).
% 0.20/0.61  fof(f15,axiom,(
% 0.20/0.61    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.61  fof(f101,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f55,f46])).
% 0.20/0.61  fof(f46,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f26])).
% 0.20/0.61  fof(f26,plain,(
% 0.20/0.61    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.61    inference(ennf_transformation,[],[f10])).
% 0.20/0.61  fof(f10,axiom,(
% 0.20/0.61    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.61  fof(f267,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1))) )),
% 0.20/0.61    inference(backward_demodulation,[],[f138,f262])).
% 0.20/0.61  fof(f262,plain,(
% 0.20/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.61    inference(superposition,[],[f106,f131])).
% 0.20/0.61  fof(f131,plain,(
% 0.20/0.61    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 0.20/0.61    inference(forward_demodulation,[],[f130,f95])).
% 0.20/0.61  fof(f95,plain,(
% 0.20/0.61    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 0.20/0.61    inference(forward_demodulation,[],[f94,f59])).
% 0.20/0.61  fof(f59,plain,(
% 0.20/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.61    inference(cnf_transformation,[],[f13])).
% 0.20/0.61  fof(f94,plain,(
% 0.20/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 0.20/0.61    inference(forward_demodulation,[],[f91,f60])).
% 0.20/0.61  fof(f91,plain,(
% 0.20/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f55,f54])).
% 0.20/0.61  fof(f54,plain,(
% 0.20/0.61    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f37])).
% 0.20/0.61  fof(f37,plain,(
% 0.20/0.61    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.61    inference(ennf_transformation,[],[f12])).
% 0.20/0.61  fof(f12,axiom,(
% 0.20/0.61    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.61  fof(f130,plain,(
% 0.20/0.61    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0) )),
% 0.20/0.61    inference(forward_demodulation,[],[f125,f60])).
% 0.20/0.61  fof(f125,plain,(
% 0.20/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))))) )),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f55,f56,f64,f50])).
% 0.20/0.61  fof(f50,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f33])).
% 0.20/0.61  fof(f33,plain,(
% 0.20/0.61    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.61    inference(flattening,[],[f32])).
% 0.20/0.61  fof(f32,plain,(
% 0.20/0.61    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.61    inference(ennf_transformation,[],[f17])).
% 0.20/0.61  fof(f17,axiom,(
% 0.20/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.61  fof(f64,plain,(
% 0.20/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.61    inference(equality_resolution,[],[f43])).
% 0.20/0.61  fof(f43,plain,(
% 0.20/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.61    inference(cnf_transformation,[],[f1])).
% 0.20/0.61  fof(f56,plain,(
% 0.20/0.61    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f15])).
% 0.20/0.61  fof(f138,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0))) )),
% 0.20/0.61    inference(forward_demodulation,[],[f137,f59])).
% 0.20/0.61  fof(f137,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_relat_1(k6_relat_1(X0))))) )),
% 0.20/0.61    inference(forward_demodulation,[],[f134,f106])).
% 0.20/0.61  fof(f134,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) )),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f56,f55,f53])).
% 0.20/0.61  fof(f53,plain,(
% 0.20/0.61    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f36])).
% 0.20/0.61  fof(f36,plain,(
% 0.20/0.61    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.61    inference(flattening,[],[f35])).
% 0.20/0.61  fof(f35,plain,(
% 0.20/0.61    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.61    inference(ennf_transformation,[],[f18])).
% 0.20/0.61  fof(f18,axiom,(
% 0.20/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 0.20/0.61  fof(f378,plain,(
% 0.20/0.61    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X2))) )),
% 0.20/0.61    inference(superposition,[],[f113,f262])).
% 0.20/0.61  fof(f113,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2)) )),
% 0.20/0.61    inference(forward_demodulation,[],[f110,f104])).
% 0.20/0.61  fof(f110,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2))) )),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f55,f45])).
% 0.20/0.61  fof(f45,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f25])).
% 0.20/0.61  fof(f25,plain,(
% 0.20/0.61    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.61    inference(ennf_transformation,[],[f16])).
% 0.20/0.61  fof(f16,axiom,(
% 0.20/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 0.20/0.61  fof(f69,plain,(
% 0.20/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 0.20/0.61    inference(forward_demodulation,[],[f67,f59])).
% 0.20/0.61  fof(f67,plain,(
% 0.20/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0)))) )),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f55,f51])).
% 0.20/0.61  fof(f51,plain,(
% 0.20/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f34])).
% 0.20/0.61  fof(f34,plain,(
% 0.20/0.61    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.61    inference(ennf_transformation,[],[f11])).
% 0.20/0.61  fof(f11,axiom,(
% 0.20/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.20/0.61  fof(f203,plain,(
% 0.20/0.61    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 0.20/0.61    inference(superposition,[],[f39,f109])).
% 0.20/0.61  fof(f109,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1))) )),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f40,f45])).
% 0.20/0.61  fof(f40,plain,(
% 0.20/0.61    v1_relat_1(sK0)),
% 0.20/0.61    inference(cnf_transformation,[],[f24])).
% 0.20/0.61  fof(f24,plain,(
% 0.20/0.61    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.61    inference(flattening,[],[f23])).
% 0.20/0.61  fof(f23,plain,(
% 0.20/0.61    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.61    inference(ennf_transformation,[],[f22])).
% 0.20/0.61  fof(f22,negated_conjecture,(
% 0.20/0.61    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.20/0.61    inference(negated_conjecture,[],[f21])).
% 0.20/0.61  fof(f21,conjecture,(
% 0.20/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 0.20/0.61  fof(f39,plain,(
% 0.20/0.61    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.20/0.61    inference(cnf_transformation,[],[f24])).
% 0.20/0.61  fof(f122,plain,(
% 0.20/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.61    inference(superposition,[],[f63,f62])).
% 0.20/0.61  fof(f62,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 0.20/0.61    inference(definition_unfolding,[],[f58,f61,f61])).
% 0.20/0.61  fof(f61,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f2])).
% 0.20/0.61  fof(f2,axiom,(
% 0.20/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.61  fof(f58,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f5])).
% 0.20/0.61  fof(f5,axiom,(
% 0.20/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.61  fof(f63,plain,(
% 0.20/0.61    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.20/0.61    inference(definition_unfolding,[],[f52,f61])).
% 0.20/0.61  fof(f52,plain,(
% 0.20/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f4])).
% 0.20/0.61  fof(f4,axiom,(
% 0.20/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.61  fof(f586,plain,(
% 0.20/0.61    r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),sK1))),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f38,f64,f402])).
% 0.20/0.61  fof(f402,plain,(
% 0.20/0.61    ( ! [X4,X2,X3] : (r1_tarski(X3,k3_xboole_0(X4,X2)) | ~r1_tarski(k3_xboole_0(X2,X3),X4) | ~r1_tarski(X3,X2)) )),
% 0.20/0.61    inference(backward_demodulation,[],[f166,f389])).
% 0.20/0.61  fof(f166,plain,(
% 0.20/0.61    ( ! [X4,X2,X3] : (~r1_tarski(k3_xboole_0(X2,X3),X4) | ~r1_tarski(X3,X2) | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4))) )),
% 0.20/0.61    inference(forward_demodulation,[],[f165,f106])).
% 0.20/0.61  fof(f165,plain,(
% 0.20/0.61    ( ! [X4,X2,X3] : (~r1_tarski(X3,X2) | ~r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4) | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4))) )),
% 0.20/0.61    inference(forward_demodulation,[],[f164,f59])).
% 0.20/0.61  fof(f164,plain,(
% 0.20/0.61    ( ! [X4,X2,X3] : (~r1_tarski(X3,k1_relat_1(k6_relat_1(X2))) | ~r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4) | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4))) )),
% 0.20/0.61    inference(subsumption_resolution,[],[f155,f55])).
% 0.20/0.61  fof(f155,plain,(
% 0.20/0.61    ( ! [X4,X2,X3] : (~v1_relat_1(k6_relat_1(X2)) | ~r1_tarski(X3,k1_relat_1(k6_relat_1(X2))) | ~r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4) | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4))) )),
% 0.20/0.61    inference(resolution,[],[f49,f56])).
% 0.20/0.61  fof(f49,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f31])).
% 0.20/0.61  fof(f31,plain,(
% 0.20/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.61    inference(flattening,[],[f30])).
% 0.20/0.61  fof(f30,plain,(
% 0.20/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.61    inference(ennf_transformation,[],[f19])).
% 0.20/0.61  fof(f19,axiom,(
% 0.20/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.20/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 0.20/0.61  fof(f38,plain,(
% 0.20/0.61    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.20/0.61    inference(cnf_transformation,[],[f24])).
% 0.20/0.61  % SZS output end Proof for theBenchmark
% 0.20/0.61  % (31768)------------------------------
% 0.20/0.61  % (31768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.61  % (31768)Termination reason: Refutation
% 0.20/0.61  
% 0.20/0.61  % (31768)Memory used [KB]: 2174
% 0.20/0.61  % (31768)Time elapsed: 0.201 s
% 0.20/0.61  % (31768)------------------------------
% 0.20/0.61  % (31768)------------------------------
% 0.20/0.61  % (31740)Success in time 0.243 s
%------------------------------------------------------------------------------
