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
% DateTime   : Thu Dec  3 12:52:23 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 470 expanded)
%              Number of leaves         :   17 ( 133 expanded)
%              Depth                    :   19
%              Number of atoms          :  186 ( 760 expanded)
%              Number of equality atoms :   71 ( 258 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2490,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2359])).

fof(f2359,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f148,f1943])).

fof(f1943,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) ),
    inference(forward_demodulation,[],[f1942,f262])).

fof(f262,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) ),
    inference(subsumption_resolution,[],[f257,f145])).

fof(f145,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f108,f141])).

fof(f141,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f91,f94])).

fof(f94,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f54,f43])).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f91,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f53,f43])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f108,plain,(
    ! [X0,X1] : v1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(backward_demodulation,[],[f77,f91])).

fof(f77,plain,(
    ! [X0,X1] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(resolution,[],[f76,f43])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) ) ),
    inference(resolution,[],[f61,f43])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f257,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f243,f58])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f243,plain,(
    ! [X4,X3] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)),X4) ),
    inference(forward_demodulation,[],[f242,f44])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f242,plain,(
    ! [X4,X3] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k1_relat_1(k6_relat_1(X4))) ),
    inference(subsumption_resolution,[],[f241,f145])).

fof(f241,plain,(
    ! [X4,X3] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k1_relat_1(k6_relat_1(X4)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(subsumption_resolution,[],[f234,f43])).

fof(f234,plain,(
    ! [X4,X3] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k1_relat_1(k6_relat_1(X4)))
      | ~ v1_relat_1(k6_relat_1(X4))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(resolution,[],[f47,f144])).

fof(f144,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f107,f141])).

fof(f107,plain,(
    ! [X0,X1] : r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f74,f91])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f55,f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f1942,plain,(
    ! [X4,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X4) = k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) ),
    inference(forward_demodulation,[],[f1941,f73])).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f72,f44])).

fof(f72,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f46,f43])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f1941,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4),X4) ),
    inference(forward_demodulation,[],[f1940,f1056])).

fof(f1056,plain,(
    ! [X116,X117,X115] : k7_relat_1(k7_relat_1(k6_relat_1(X115),X116),X117) = k7_relat_1(k6_relat_1(X115),k1_setfam_1(k2_enumset1(X116,X116,X116,X117))) ),
    inference(resolution,[],[f71,f43])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f64,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f1940,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X3),k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X4) ),
    inference(forward_demodulation,[],[f1868,f1407])).

fof(f1407,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(superposition,[],[f1349,f254])).

fof(f254,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f249,f145])).

fof(f249,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f238,f58])).

fof(f238,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(forward_demodulation,[],[f237,f44])).

fof(f237,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0))) ),
    inference(subsumption_resolution,[],[f236,f145])).

fof(f236,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(subsumption_resolution,[],[f232,f43])).

fof(f232,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f47,f143])).

fof(f143,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f106,f141])).

fof(f106,plain,(
    ! [X0,X1] : r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f75,f91])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1)) ),
    inference(resolution,[],[f56,f43])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1349,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X3) ),
    inference(superposition,[],[f1033,f327])).

fof(f327,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(X4)) ),
    inference(subsumption_resolution,[],[f324,f145])).

fof(f324,plain,(
    ! [X4,X3] :
      ( k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(X4))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(resolution,[],[f57,f307])).

fof(f307,plain,(
    ! [X4,X3] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),X4) ),
    inference(forward_demodulation,[],[f306,f45])).

fof(f45,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f306,plain,(
    ! [X4,X3] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k2_relat_1(k6_relat_1(X4))) ),
    inference(subsumption_resolution,[],[f305,f145])).

fof(f305,plain,(
    ! [X4,X3] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k2_relat_1(k6_relat_1(X4)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(subsumption_resolution,[],[f296,f43])).

fof(f296,plain,(
    ! [X4,X3] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k2_relat_1(k6_relat_1(X4)))
      | ~ v1_relat_1(k6_relat_1(X4))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(resolution,[],[f48,f144])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f1033,plain,(
    ! [X4,X2,X3] : k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) ),
    inference(forward_demodulation,[],[f1032,f413])).

fof(f413,plain,(
    ! [X47,X48,X46] : k8_relat_1(X46,k7_relat_1(k6_relat_1(X47),X48)) = k7_relat_1(k7_relat_1(k6_relat_1(X46),X47),X48) ),
    inference(forward_demodulation,[],[f411,f141])).

fof(f411,plain,(
    ! [X47,X48,X46] : k7_relat_1(k8_relat_1(X46,k6_relat_1(X47)),X48) = k8_relat_1(X46,k7_relat_1(k6_relat_1(X47),X48)) ),
    inference(resolution,[],[f63,f43])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f1032,plain,(
    ! [X4,X2,X3] : k8_relat_1(X2,k7_relat_1(k6_relat_1(X3),X4)) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f111,f141])).

fof(f111,plain,(
    ! [X4,X2,X3] : k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(X4))) = k5_relat_1(k8_relat_1(X3,k6_relat_1(X4)),k6_relat_1(X2)) ),
    inference(resolution,[],[f108,f53])).

fof(f1868,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3),X4) ),
    inference(superposition,[],[f1056,f73])).

fof(f148,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f109,f141])).

fof(f109,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f67,f91])).

fof(f67,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f42,f66])).

fof(f42,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f40])).

fof(f40,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (25098)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (25114)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (25105)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (25101)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (25104)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (25106)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (25102)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.52  % (25115)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (25109)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.53  % (25107)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (25108)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.53  % (25100)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.53  % (25099)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.53  % (25111)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.53  % (25097)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.54  % (25110)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.54  % (25108)Refutation not found, incomplete strategy% (25108)------------------------------
% 0.21/0.54  % (25108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25108)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25108)Memory used [KB]: 10618
% 0.21/0.54  % (25108)Time elapsed: 0.093 s
% 0.21/0.54  % (25108)------------------------------
% 0.21/0.54  % (25108)------------------------------
% 0.21/0.55  % (25103)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (25113)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 2.22/0.64  % (25109)Refutation found. Thanks to Tanya!
% 2.22/0.64  % SZS status Theorem for theBenchmark
% 2.22/0.64  % SZS output start Proof for theBenchmark
% 2.22/0.64  fof(f2490,plain,(
% 2.22/0.64    $false),
% 2.22/0.64    inference(trivial_inequality_removal,[],[f2359])).
% 2.22/0.64  fof(f2359,plain,(
% 2.22/0.64    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 2.22/0.64    inference(superposition,[],[f148,f1943])).
% 2.22/0.64  fof(f1943,plain,(
% 2.22/0.64    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4)))) )),
% 2.22/0.64    inference(forward_demodulation,[],[f1942,f262])).
% 2.22/0.64  fof(f262,plain,(
% 2.22/0.64    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1)) )),
% 2.22/0.64    inference(subsumption_resolution,[],[f257,f145])).
% 2.22/0.64  fof(f145,plain,(
% 2.22/0.64    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 2.22/0.64    inference(backward_demodulation,[],[f108,f141])).
% 2.22/0.64  fof(f141,plain,(
% 2.22/0.64    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.22/0.64    inference(backward_demodulation,[],[f91,f94])).
% 2.22/0.64  fof(f94,plain,(
% 2.22/0.64    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.22/0.64    inference(resolution,[],[f54,f43])).
% 2.22/0.64  fof(f43,plain,(
% 2.22/0.64    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.22/0.64    inference(cnf_transformation,[],[f7])).
% 2.22/0.64  fof(f7,axiom,(
% 2.22/0.64    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 2.22/0.64  fof(f54,plain,(
% 2.22/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.22/0.64    inference(cnf_transformation,[],[f28])).
% 2.22/0.64  fof(f28,plain,(
% 2.22/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.22/0.64    inference(ennf_transformation,[],[f17])).
% 2.22/0.64  fof(f17,axiom,(
% 2.22/0.64    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.22/0.64  fof(f91,plain,(
% 2.22/0.64    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 2.22/0.64    inference(resolution,[],[f53,f43])).
% 2.22/0.64  fof(f53,plain,(
% 2.22/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 2.22/0.64    inference(cnf_transformation,[],[f27])).
% 2.22/0.64  fof(f27,plain,(
% 2.22/0.64    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 2.22/0.64    inference(ennf_transformation,[],[f11])).
% 2.22/0.64  fof(f11,axiom,(
% 2.22/0.64    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 2.22/0.64  fof(f108,plain,(
% 2.22/0.64    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 2.22/0.64    inference(backward_demodulation,[],[f77,f91])).
% 2.22/0.64  fof(f77,plain,(
% 2.22/0.64    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 2.22/0.64    inference(resolution,[],[f76,f43])).
% 2.22/0.64  fof(f76,plain,(
% 2.22/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))) )),
% 2.22/0.64    inference(resolution,[],[f61,f43])).
% 2.22/0.64  fof(f61,plain,(
% 2.22/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.22/0.64    inference(cnf_transformation,[],[f37])).
% 2.22/0.64  fof(f37,plain,(
% 2.22/0.64    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.22/0.64    inference(flattening,[],[f36])).
% 2.22/0.64  fof(f36,plain,(
% 2.22/0.64    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.22/0.64    inference(ennf_transformation,[],[f6])).
% 2.22/0.64  fof(f6,axiom,(
% 2.22/0.64    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.22/0.64  fof(f257,plain,(
% 2.22/0.64    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.22/0.64    inference(resolution,[],[f243,f58])).
% 2.22/0.64  fof(f58,plain,(
% 2.22/0.64    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.22/0.64    inference(cnf_transformation,[],[f33])).
% 2.22/0.64  fof(f33,plain,(
% 2.22/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.22/0.64    inference(flattening,[],[f32])).
% 2.22/0.64  fof(f32,plain,(
% 2.22/0.64    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.22/0.64    inference(ennf_transformation,[],[f18])).
% 2.22/0.64  fof(f18,axiom,(
% 2.22/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 2.22/0.64  fof(f243,plain,(
% 2.22/0.64    ( ! [X4,X3] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)),X4)) )),
% 2.22/0.64    inference(forward_demodulation,[],[f242,f44])).
% 2.22/0.64  fof(f44,plain,(
% 2.22/0.64    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.22/0.64    inference(cnf_transformation,[],[f14])).
% 2.22/0.64  fof(f14,axiom,(
% 2.22/0.64    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.22/0.64  fof(f242,plain,(
% 2.22/0.64    ( ! [X4,X3] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k1_relat_1(k6_relat_1(X4)))) )),
% 2.22/0.64    inference(subsumption_resolution,[],[f241,f145])).
% 2.22/0.64  fof(f241,plain,(
% 2.22/0.64    ( ! [X4,X3] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k1_relat_1(k6_relat_1(X4))) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 2.22/0.64    inference(subsumption_resolution,[],[f234,f43])).
% 2.22/0.64  fof(f234,plain,(
% 2.22/0.64    ( ! [X4,X3] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k1_relat_1(k6_relat_1(X4))) | ~v1_relat_1(k6_relat_1(X4)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 2.22/0.64    inference(resolution,[],[f47,f144])).
% 2.22/0.64  fof(f144,plain,(
% 2.22/0.64    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0))) )),
% 2.22/0.64    inference(backward_demodulation,[],[f107,f141])).
% 2.22/0.64  fof(f107,plain,(
% 2.22/0.64    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X0))) )),
% 2.22/0.64    inference(backward_demodulation,[],[f74,f91])).
% 2.22/0.64  fof(f74,plain,(
% 2.22/0.64    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0))) )),
% 2.22/0.64    inference(resolution,[],[f55,f43])).
% 2.22/0.64  fof(f55,plain,(
% 2.22/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 2.22/0.64    inference(cnf_transformation,[],[f29])).
% 2.22/0.64  fof(f29,plain,(
% 2.22/0.64    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 2.22/0.64    inference(ennf_transformation,[],[f15])).
% 2.22/0.64  fof(f15,axiom,(
% 2.22/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 2.22/0.64  fof(f47,plain,(
% 2.22/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.22/0.64    inference(cnf_transformation,[],[f25])).
% 2.22/0.64  fof(f25,plain,(
% 2.22/0.64    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.22/0.64    inference(flattening,[],[f24])).
% 2.22/0.64  fof(f24,plain,(
% 2.22/0.64    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.22/0.64    inference(ennf_transformation,[],[f13])).
% 2.22/0.64  fof(f13,axiom,(
% 2.22/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 2.22/0.64  fof(f1942,plain,(
% 2.22/0.64    ( ! [X4,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X4) = k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4)))) )),
% 2.22/0.64    inference(forward_demodulation,[],[f1941,f73])).
% 2.22/0.64  fof(f73,plain,(
% 2.22/0.64    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 2.22/0.64    inference(forward_demodulation,[],[f72,f44])).
% 2.22/0.64  fof(f72,plain,(
% 2.22/0.64    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 2.22/0.64    inference(resolution,[],[f46,f43])).
% 2.22/0.64  fof(f46,plain,(
% 2.22/0.64    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 2.22/0.64    inference(cnf_transformation,[],[f23])).
% 2.22/0.64  fof(f23,plain,(
% 2.22/0.64    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.22/0.64    inference(ennf_transformation,[],[f19])).
% 2.22/0.64  fof(f19,axiom,(
% 2.22/0.64    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 2.22/0.64  fof(f1941,plain,(
% 2.22/0.64    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4),X4)) )),
% 2.22/0.64    inference(forward_demodulation,[],[f1940,f1056])).
% 2.22/0.64  fof(f1056,plain,(
% 2.22/0.64    ( ! [X116,X117,X115] : (k7_relat_1(k7_relat_1(k6_relat_1(X115),X116),X117) = k7_relat_1(k6_relat_1(X115),k1_setfam_1(k2_enumset1(X116,X116,X116,X117)))) )),
% 2.22/0.64    inference(resolution,[],[f71,f43])).
% 2.22/0.64  fof(f71,plain,(
% 2.22/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.22/0.64    inference(definition_unfolding,[],[f64,f66])).
% 2.22/0.64  fof(f66,plain,(
% 2.22/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.22/0.64    inference(definition_unfolding,[],[f51,f65])).
% 2.22/0.64  fof(f65,plain,(
% 2.22/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.22/0.64    inference(definition_unfolding,[],[f50,f62])).
% 2.22/0.64  fof(f62,plain,(
% 2.22/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.22/0.64    inference(cnf_transformation,[],[f4])).
% 2.22/0.64  fof(f4,axiom,(
% 2.22/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.22/0.64  fof(f50,plain,(
% 2.22/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.22/0.64    inference(cnf_transformation,[],[f3])).
% 2.22/0.64  fof(f3,axiom,(
% 2.22/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.22/0.64  fof(f51,plain,(
% 2.22/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.22/0.64    inference(cnf_transformation,[],[f5])).
% 2.22/0.64  fof(f5,axiom,(
% 2.22/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.22/0.64  fof(f64,plain,(
% 2.22/0.64    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 2.22/0.64    inference(cnf_transformation,[],[f39])).
% 2.22/0.64  fof(f39,plain,(
% 2.22/0.64    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 2.22/0.64    inference(ennf_transformation,[],[f9])).
% 2.22/0.64  fof(f9,axiom,(
% 2.22/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 2.22/0.64  fof(f1940,plain,(
% 2.22/0.64    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X3),k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X4)) )),
% 2.22/0.64    inference(forward_demodulation,[],[f1868,f1407])).
% 2.22/0.64  fof(f1407,plain,(
% 2.22/0.64    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 2.22/0.64    inference(superposition,[],[f1349,f254])).
% 2.22/0.64  fof(f254,plain,(
% 2.22/0.64    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.22/0.64    inference(subsumption_resolution,[],[f249,f145])).
% 2.22/0.64  fof(f249,plain,(
% 2.22/0.64    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.22/0.64    inference(resolution,[],[f238,f58])).
% 2.22/0.64  fof(f238,plain,(
% 2.22/0.64    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 2.22/0.64    inference(forward_demodulation,[],[f237,f44])).
% 2.22/0.64  fof(f237,plain,(
% 2.22/0.64    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0)))) )),
% 2.22/0.64    inference(subsumption_resolution,[],[f236,f145])).
% 2.22/0.64  fof(f236,plain,(
% 2.22/0.64    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.22/0.64    inference(subsumption_resolution,[],[f232,f43])).
% 2.22/0.64  fof(f232,plain,(
% 2.22/0.64    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.22/0.64    inference(resolution,[],[f47,f143])).
% 2.22/0.64  fof(f143,plain,(
% 2.22/0.64    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X1))) )),
% 2.22/0.64    inference(backward_demodulation,[],[f106,f141])).
% 2.22/0.64  fof(f106,plain,(
% 2.22/0.64    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X1))) )),
% 2.22/0.64    inference(backward_demodulation,[],[f75,f91])).
% 2.22/0.64  fof(f75,plain,(
% 2.22/0.64    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1))) )),
% 2.22/0.64    inference(resolution,[],[f56,f43])).
% 2.22/0.64  fof(f56,plain,(
% 2.22/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)) )),
% 2.22/0.64    inference(cnf_transformation,[],[f29])).
% 2.22/0.64  fof(f1349,plain,(
% 2.22/0.64    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X3)) )),
% 2.22/0.64    inference(superposition,[],[f1033,f327])).
% 2.22/0.64  fof(f327,plain,(
% 2.22/0.64    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(X4))) )),
% 2.22/0.64    inference(subsumption_resolution,[],[f324,f145])).
% 2.22/0.64  fof(f324,plain,(
% 2.22/0.64    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(X4)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 2.22/0.64    inference(resolution,[],[f57,f307])).
% 2.22/0.64  fof(f307,plain,(
% 2.22/0.64    ( ! [X4,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),X4)) )),
% 2.22/0.64    inference(forward_demodulation,[],[f306,f45])).
% 2.22/0.64  fof(f45,plain,(
% 2.22/0.64    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.22/0.64    inference(cnf_transformation,[],[f14])).
% 2.22/0.64  fof(f306,plain,(
% 2.22/0.64    ( ! [X4,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k2_relat_1(k6_relat_1(X4)))) )),
% 2.22/0.64    inference(subsumption_resolution,[],[f305,f145])).
% 2.22/0.64  fof(f305,plain,(
% 2.22/0.64    ( ! [X4,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k2_relat_1(k6_relat_1(X4))) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 2.22/0.64    inference(subsumption_resolution,[],[f296,f43])).
% 2.22/0.64  fof(f296,plain,(
% 2.22/0.64    ( ! [X4,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k2_relat_1(k6_relat_1(X4))) | ~v1_relat_1(k6_relat_1(X4)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 2.22/0.64    inference(resolution,[],[f48,f144])).
% 2.22/0.64  fof(f48,plain,(
% 2.22/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.22/0.64    inference(cnf_transformation,[],[f25])).
% 2.22/0.64  fof(f57,plain,(
% 2.22/0.64    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 2.22/0.64    inference(cnf_transformation,[],[f31])).
% 2.22/0.64  fof(f31,plain,(
% 2.22/0.64    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.22/0.64    inference(flattening,[],[f30])).
% 2.22/0.64  fof(f30,plain,(
% 2.22/0.64    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.22/0.64    inference(ennf_transformation,[],[f16])).
% 2.22/0.64  fof(f16,axiom,(
% 2.22/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 2.22/0.64  fof(f1033,plain,(
% 2.22/0.64    ( ! [X4,X2,X3] : (k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4)) )),
% 2.22/0.64    inference(forward_demodulation,[],[f1032,f413])).
% 2.22/0.64  fof(f413,plain,(
% 2.22/0.64    ( ! [X47,X48,X46] : (k8_relat_1(X46,k7_relat_1(k6_relat_1(X47),X48)) = k7_relat_1(k7_relat_1(k6_relat_1(X46),X47),X48)) )),
% 2.22/0.64    inference(forward_demodulation,[],[f411,f141])).
% 2.22/0.64  fof(f411,plain,(
% 2.22/0.64    ( ! [X47,X48,X46] : (k7_relat_1(k8_relat_1(X46,k6_relat_1(X47)),X48) = k8_relat_1(X46,k7_relat_1(k6_relat_1(X47),X48))) )),
% 2.22/0.64    inference(resolution,[],[f63,f43])).
% 2.22/0.64  fof(f63,plain,(
% 2.22/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))) )),
% 2.22/0.64    inference(cnf_transformation,[],[f38])).
% 2.22/0.64  fof(f38,plain,(
% 2.22/0.64    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.22/0.64    inference(ennf_transformation,[],[f12])).
% 2.22/0.64  fof(f12,axiom,(
% 2.22/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 2.22/0.64  fof(f1032,plain,(
% 2.22/0.64    ( ! [X4,X2,X3] : (k8_relat_1(X2,k7_relat_1(k6_relat_1(X3),X4)) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(X2))) )),
% 2.22/0.64    inference(forward_demodulation,[],[f111,f141])).
% 2.22/0.64  fof(f111,plain,(
% 2.22/0.64    ( ! [X4,X2,X3] : (k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(X4))) = k5_relat_1(k8_relat_1(X3,k6_relat_1(X4)),k6_relat_1(X2))) )),
% 2.22/0.64    inference(resolution,[],[f108,f53])).
% 2.22/0.64  fof(f1868,plain,(
% 2.22/0.64    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3),X4)) )),
% 2.22/0.64    inference(superposition,[],[f1056,f73])).
% 2.22/0.64  fof(f148,plain,(
% 2.22/0.64    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 2.22/0.64    inference(backward_demodulation,[],[f109,f141])).
% 2.22/0.64  fof(f109,plain,(
% 2.22/0.64    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 2.22/0.64    inference(backward_demodulation,[],[f67,f91])).
% 2.22/0.64  fof(f67,plain,(
% 2.22/0.64    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 2.22/0.64    inference(definition_unfolding,[],[f42,f66])).
% 2.22/0.64  fof(f42,plain,(
% 2.22/0.64    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.22/0.64    inference(cnf_transformation,[],[f41])).
% 2.22/0.64  fof(f41,plain,(
% 2.22/0.64    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.22/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f40])).
% 2.22/0.64  fof(f40,plain,(
% 2.22/0.64    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.22/0.64    introduced(choice_axiom,[])).
% 2.22/0.64  fof(f22,plain,(
% 2.22/0.64    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 2.22/0.64    inference(ennf_transformation,[],[f21])).
% 2.22/0.64  fof(f21,negated_conjecture,(
% 2.22/0.64    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.22/0.64    inference(negated_conjecture,[],[f20])).
% 2.22/0.64  fof(f20,conjecture,(
% 2.22/0.64    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 2.22/0.64  % SZS output end Proof for theBenchmark
% 2.22/0.64  % (25109)------------------------------
% 2.22/0.64  % (25109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.64  % (25109)Termination reason: Refutation
% 2.22/0.64  
% 2.22/0.64  % (25109)Memory used [KB]: 3070
% 2.22/0.64  % (25109)Time elapsed: 0.194 s
% 2.22/0.64  % (25109)------------------------------
% 2.22/0.64  % (25109)------------------------------
% 2.22/0.65  % (25090)Success in time 0.281 s
%------------------------------------------------------------------------------
