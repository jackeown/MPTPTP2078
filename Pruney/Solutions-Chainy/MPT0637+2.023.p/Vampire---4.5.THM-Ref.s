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
% DateTime   : Thu Dec  3 12:52:25 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 195 expanded)
%              Number of leaves         :   15 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  155 ( 334 expanded)
%              Number of equality atoms :   59 ( 125 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1742,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1735])).

fof(f1735,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f75,f1489])).

fof(f1489,plain,(
    ! [X2,X3] : k8_relat_1(X3,k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X3,X2)) ),
    inference(backward_demodulation,[],[f85,f1488])).

fof(f1488,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(subsumption_resolution,[],[f1471,f240])).

fof(f240,plain,(
    ! [X14,X15] : r1_tarski(k7_relat_1(k6_relat_1(X14),X15),k6_relat_1(k3_xboole_0(X14,X15))) ),
    inference(forward_demodulation,[],[f239,f42])).

fof(f42,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f239,plain,(
    ! [X14,X15] : r1_tarski(k7_relat_1(k6_relat_1(X14),X15),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X14)),X15))) ),
    inference(subsumption_resolution,[],[f229,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f229,plain,(
    ! [X14,X15] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X14),X15),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X14)),X15)))
      | ~ v1_relat_1(k6_relat_1(X14)) ) ),
    inference(superposition,[],[f89,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f61,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f89,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2)) ),
    inference(subsumption_resolution,[],[f88,f40])).

fof(f88,plain,(
    ! [X2,X3] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(subsumption_resolution,[],[f81,f40])).

fof(f81,plain,(
    ! [X2,X3] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f55,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f1471,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k3_xboole_0(X0,X1))) ) ),
    inference(resolution,[],[f1338,f286])).

fof(f286,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X7,X6)
      | X6 = X7
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f154,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f154,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(X5,X4) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f69,f59])).

fof(f69,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f64,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f50,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1338,plain,(
    ! [X2,X3] : r1_tarski(k6_relat_1(k3_xboole_0(X2,X3)),k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f981,f63])).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f62,f40])).

fof(f62,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f44,f42])).

fof(f981,plain,(
    ! [X4,X5,X3] : r1_tarski(k7_relat_1(k6_relat_1(X4),k3_xboole_0(X3,X5)),k7_relat_1(k6_relat_1(X3),X5)) ),
    inference(backward_demodulation,[],[f396,f979])).

fof(f979,plain,(
    ! [X19,X20,X18] : k7_relat_1(k7_relat_1(k6_relat_1(X18),X19),X20) = k7_relat_1(k6_relat_1(X18),k3_xboole_0(X19,X20)) ),
    inference(forward_demodulation,[],[f978,f63])).

fof(f978,plain,(
    ! [X19,X20,X18] : k7_relat_1(k7_relat_1(k6_relat_1(X18),X18),k3_xboole_0(X19,X20)) = k7_relat_1(k7_relat_1(k6_relat_1(X18),X19),X20) ),
    inference(subsumption_resolution,[],[f977,f40])).

fof(f977,plain,(
    ! [X19,X20,X18] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(X18),X18),k3_xboole_0(X19,X20)) = k7_relat_1(k7_relat_1(k6_relat_1(X18),X19),X20)
      | ~ v1_relat_1(k6_relat_1(X18)) ) ),
    inference(subsumption_resolution,[],[f947,f163])).

fof(f163,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(subsumption_resolution,[],[f161,f40])).

fof(f161,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f113,f85])).

fof(f113,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k8_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k8_relat_1(X3,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f51,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f947,plain,(
    ! [X19,X20,X18] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(X18),X18),k3_xboole_0(X19,X20)) = k7_relat_1(k7_relat_1(k6_relat_1(X18),X19),X20)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X18),X18))
      | ~ v1_relat_1(k6_relat_1(X18)) ) ),
    inference(superposition,[],[f119,f127])).

fof(f127,plain,(
    ! [X6,X5] : k7_relat_1(k6_relat_1(X5),k3_xboole_0(X5,X6)) = k7_relat_1(k6_relat_1(X5),X6) ),
    inference(subsumption_resolution,[],[f118,f40])).

fof(f118,plain,(
    ! [X6,X5] :
      ( k7_relat_1(k6_relat_1(X5),k3_xboole_0(X5,X6)) = k7_relat_1(k6_relat_1(X5),X6)
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(superposition,[],[f61,f63])).

fof(f119,plain,(
    ! [X10,X8,X7,X9] :
      ( k7_relat_1(k7_relat_1(X7,X8),k3_xboole_0(X9,X10)) = k7_relat_1(k7_relat_1(X7,k3_xboole_0(X8,X9)),X10)
      | ~ v1_relat_1(k7_relat_1(X7,X8))
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f61,f61])).

fof(f396,plain,(
    ! [X4,X5,X3] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X5),k7_relat_1(k6_relat_1(X3),X5)) ),
    inference(subsumption_resolution,[],[f395,f40])).

fof(f395,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X5),k7_relat_1(k6_relat_1(X3),X5))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(subsumption_resolution,[],[f394,f40])).

fof(f394,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X5),k7_relat_1(k6_relat_1(X3),X5))
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(subsumption_resolution,[],[f370,f163])).

fof(f370,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X5),k7_relat_1(k6_relat_1(X3),X5))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X5))
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(superposition,[],[f146,f53])).

fof(f146,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k7_relat_1(k5_relat_1(X3,k6_relat_1(X5)),X4),k7_relat_1(X3,X4))
      | ~ v1_relat_1(k7_relat_1(X3,X4))
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f141,f40])).

fof(f141,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k7_relat_1(k5_relat_1(X3,k6_relat_1(X5)),X4),k7_relat_1(X3,X4))
      | ~ v1_relat_1(k7_relat_1(X3,X4))
      | ~ v1_relat_1(k6_relat_1(X5))
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f55,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f85,plain,(
    ! [X2,X3] : k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(subsumption_resolution,[],[f84,f40])).

fof(f84,plain,(
    ! [X2,X3] :
      ( k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f78,f40])).

fof(f78,plain,(
    ! [X2,X3] :
      ( k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f75,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f71,f40])).

fof(f71,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f39,f52])).

fof(f39,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f37])).

fof(f37,plain,
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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:38:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (384)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (374)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (379)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (383)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (376)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (371)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (381)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (367)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (370)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (372)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (368)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (375)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (378)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (378)Refutation not found, incomplete strategy% (378)------------------------------
% 0.21/0.49  % (378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (378)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (378)Memory used [KB]: 10618
% 0.21/0.49  % (378)Time elapsed: 0.075 s
% 0.21/0.49  % (378)------------------------------
% 0.21/0.49  % (378)------------------------------
% 0.21/0.49  % (369)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (373)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (380)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (377)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (382)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.36/0.53  % (370)Refutation found. Thanks to Tanya!
% 1.36/0.53  % SZS status Theorem for theBenchmark
% 1.36/0.53  % SZS output start Proof for theBenchmark
% 1.36/0.53  fof(f1742,plain,(
% 1.36/0.53    $false),
% 1.36/0.53    inference(trivial_inequality_removal,[],[f1735])).
% 1.36/0.53  fof(f1735,plain,(
% 1.36/0.53    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.36/0.53    inference(superposition,[],[f75,f1489])).
% 1.36/0.53  fof(f1489,plain,(
% 1.36/0.53    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X3,X2))) )),
% 1.36/0.53    inference(backward_demodulation,[],[f85,f1488])).
% 1.36/0.53  fof(f1488,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f1471,f240])).
% 1.36/0.53  fof(f240,plain,(
% 1.36/0.53    ( ! [X14,X15] : (r1_tarski(k7_relat_1(k6_relat_1(X14),X15),k6_relat_1(k3_xboole_0(X14,X15)))) )),
% 1.36/0.53    inference(forward_demodulation,[],[f239,f42])).
% 1.36/0.53  fof(f42,plain,(
% 1.36/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.36/0.53    inference(cnf_transformation,[],[f14])).
% 1.36/0.53  fof(f14,axiom,(
% 1.36/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.36/0.53  fof(f239,plain,(
% 1.36/0.53    ( ! [X14,X15] : (r1_tarski(k7_relat_1(k6_relat_1(X14),X15),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X14)),X15)))) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f229,f40])).
% 1.36/0.53  fof(f40,plain,(
% 1.36/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f6])).
% 1.36/0.53  fof(f6,axiom,(
% 1.36/0.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.36/0.53  fof(f229,plain,(
% 1.36/0.53    ( ! [X14,X15] : (r1_tarski(k7_relat_1(k6_relat_1(X14),X15),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X14)),X15))) | ~v1_relat_1(k6_relat_1(X14))) )),
% 1.36/0.53    inference(superposition,[],[f89,f126])).
% 1.36/0.53  fof(f126,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | ~v1_relat_1(X0)) )),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f116])).
% 1.36/0.53  fof(f116,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.53    inference(superposition,[],[f61,f44])).
% 1.36/0.53  fof(f44,plain,(
% 1.36/0.53    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f23])).
% 1.36/0.53  fof(f23,plain,(
% 1.36/0.53    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f19])).
% 1.36/0.53  fof(f19,axiom,(
% 1.36/0.53    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 1.36/0.53  fof(f61,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f36])).
% 1.36/0.53  fof(f36,plain,(
% 1.36/0.53    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.36/0.53    inference(ennf_transformation,[],[f8])).
% 1.36/0.53  fof(f8,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 1.36/0.53  fof(f89,plain,(
% 1.36/0.53    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2))) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f88,f40])).
% 1.36/0.53  fof(f88,plain,(
% 1.36/0.53    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f81,f40])).
% 1.36/0.53  fof(f81,plain,(
% 1.36/0.53    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 1.36/0.53    inference(superposition,[],[f55,f53])).
% 1.36/0.53  fof(f53,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f29])).
% 1.36/0.53  fof(f29,plain,(
% 1.36/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f17])).
% 1.36/0.53  fof(f17,axiom,(
% 1.36/0.53    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.36/0.53  fof(f55,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f31])).
% 1.36/0.53  fof(f31,plain,(
% 1.36/0.53    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f16])).
% 1.36/0.53  fof(f16,axiom,(
% 1.36/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 1.36/0.53  fof(f1471,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k3_xboole_0(X0,X1)))) )),
% 1.36/0.53    inference(resolution,[],[f1338,f286])).
% 1.36/0.53  fof(f286,plain,(
% 1.36/0.53    ( ! [X6,X7] : (~r1_tarski(X7,X6) | X6 = X7 | ~r1_tarski(X6,X7)) )),
% 1.36/0.53    inference(superposition,[],[f154,f59])).
% 1.36/0.53  fof(f59,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f35])).
% 1.36/0.53  fof(f35,plain,(
% 1.36/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f1])).
% 1.36/0.53  fof(f1,axiom,(
% 1.36/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.36/0.53  fof(f154,plain,(
% 1.36/0.53    ( ! [X4,X5] : (k3_xboole_0(X5,X4) = X4 | ~r1_tarski(X4,X5)) )),
% 1.36/0.53    inference(superposition,[],[f69,f59])).
% 1.36/0.53  fof(f69,plain,(
% 1.36/0.53    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.36/0.53    inference(superposition,[],[f64,f50])).
% 1.36/0.53  fof(f50,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f5])).
% 1.36/0.53  fof(f5,axiom,(
% 1.36/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.36/0.53  fof(f64,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.36/0.53    inference(superposition,[],[f50,f48])).
% 1.36/0.53  fof(f48,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f2])).
% 1.36/0.53  fof(f2,axiom,(
% 1.36/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.36/0.53  fof(f1338,plain,(
% 1.36/0.53    ( ! [X2,X3] : (r1_tarski(k6_relat_1(k3_xboole_0(X2,X3)),k7_relat_1(k6_relat_1(X2),X3))) )),
% 1.36/0.53    inference(superposition,[],[f981,f63])).
% 1.36/0.53  fof(f63,plain,(
% 1.36/0.53    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f62,f40])).
% 1.36/0.53  fof(f62,plain,(
% 1.36/0.53    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.36/0.53    inference(superposition,[],[f44,f42])).
% 1.36/0.53  fof(f981,plain,(
% 1.36/0.53    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X4),k3_xboole_0(X3,X5)),k7_relat_1(k6_relat_1(X3),X5))) )),
% 1.36/0.53    inference(backward_demodulation,[],[f396,f979])).
% 1.36/0.53  fof(f979,plain,(
% 1.36/0.53    ( ! [X19,X20,X18] : (k7_relat_1(k7_relat_1(k6_relat_1(X18),X19),X20) = k7_relat_1(k6_relat_1(X18),k3_xboole_0(X19,X20))) )),
% 1.36/0.53    inference(forward_demodulation,[],[f978,f63])).
% 1.36/0.53  fof(f978,plain,(
% 1.36/0.53    ( ! [X19,X20,X18] : (k7_relat_1(k7_relat_1(k6_relat_1(X18),X18),k3_xboole_0(X19,X20)) = k7_relat_1(k7_relat_1(k6_relat_1(X18),X19),X20)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f977,f40])).
% 1.36/0.53  fof(f977,plain,(
% 1.36/0.53    ( ! [X19,X20,X18] : (k7_relat_1(k7_relat_1(k6_relat_1(X18),X18),k3_xboole_0(X19,X20)) = k7_relat_1(k7_relat_1(k6_relat_1(X18),X19),X20) | ~v1_relat_1(k6_relat_1(X18))) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f947,f163])).
% 1.36/0.53  fof(f163,plain,(
% 1.36/0.53    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f161,f40])).
% 1.36/0.53  fof(f161,plain,(
% 1.36/0.53    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.36/0.53    inference(superposition,[],[f113,f85])).
% 1.36/0.53  fof(f113,plain,(
% 1.36/0.53    ( ! [X2,X3] : (v1_relat_1(k8_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f112])).
% 1.36/0.53  fof(f112,plain,(
% 1.36/0.53    ( ! [X2,X3] : (v1_relat_1(k8_relat_1(X3,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X2)) )),
% 1.36/0.53    inference(superposition,[],[f51,f54])).
% 1.36/0.53  fof(f54,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f30])).
% 1.36/0.53  fof(f30,plain,(
% 1.36/0.53    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f11])).
% 1.36/0.53  fof(f11,axiom,(
% 1.36/0.53    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).
% 1.36/0.53  fof(f51,plain,(
% 1.36/0.53    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f27])).
% 1.36/0.53  fof(f27,plain,(
% 1.36/0.53    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f7])).
% 1.36/0.53  fof(f7,axiom,(
% 1.36/0.53    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.36/0.53  fof(f947,plain,(
% 1.36/0.53    ( ! [X19,X20,X18] : (k7_relat_1(k7_relat_1(k6_relat_1(X18),X18),k3_xboole_0(X19,X20)) = k7_relat_1(k7_relat_1(k6_relat_1(X18),X19),X20) | ~v1_relat_1(k7_relat_1(k6_relat_1(X18),X18)) | ~v1_relat_1(k6_relat_1(X18))) )),
% 1.36/0.53    inference(superposition,[],[f119,f127])).
% 1.36/0.53  fof(f127,plain,(
% 1.36/0.53    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X5),k3_xboole_0(X5,X6)) = k7_relat_1(k6_relat_1(X5),X6)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f118,f40])).
% 1.36/0.53  fof(f118,plain,(
% 1.36/0.53    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X5),k3_xboole_0(X5,X6)) = k7_relat_1(k6_relat_1(X5),X6) | ~v1_relat_1(k6_relat_1(X5))) )),
% 1.36/0.53    inference(superposition,[],[f61,f63])).
% 1.36/0.53  fof(f119,plain,(
% 1.36/0.53    ( ! [X10,X8,X7,X9] : (k7_relat_1(k7_relat_1(X7,X8),k3_xboole_0(X9,X10)) = k7_relat_1(k7_relat_1(X7,k3_xboole_0(X8,X9)),X10) | ~v1_relat_1(k7_relat_1(X7,X8)) | ~v1_relat_1(X7)) )),
% 1.36/0.53    inference(superposition,[],[f61,f61])).
% 1.36/0.53  fof(f396,plain,(
% 1.36/0.53    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X5),k7_relat_1(k6_relat_1(X3),X5))) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f395,f40])).
% 1.36/0.53  fof(f395,plain,(
% 1.36/0.53    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X5),k7_relat_1(k6_relat_1(X3),X5)) | ~v1_relat_1(k6_relat_1(X4))) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f394,f40])).
% 1.36/0.53  fof(f394,plain,(
% 1.36/0.53    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X5),k7_relat_1(k6_relat_1(X3),X5)) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X4))) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f370,f163])).
% 1.36/0.53  fof(f370,plain,(
% 1.36/0.53    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X5),k7_relat_1(k6_relat_1(X3),X5)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X5)) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X4))) )),
% 1.36/0.53    inference(superposition,[],[f146,f53])).
% 1.36/0.53  fof(f146,plain,(
% 1.36/0.53    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k5_relat_1(X3,k6_relat_1(X5)),X4),k7_relat_1(X3,X4)) | ~v1_relat_1(k7_relat_1(X3,X4)) | ~v1_relat_1(X3)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f141,f40])).
% 1.36/0.53  fof(f141,plain,(
% 1.36/0.53    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k5_relat_1(X3,k6_relat_1(X5)),X4),k7_relat_1(X3,X4)) | ~v1_relat_1(k7_relat_1(X3,X4)) | ~v1_relat_1(k6_relat_1(X5)) | ~v1_relat_1(X3)) )),
% 1.36/0.53    inference(superposition,[],[f55,f58])).
% 1.36/0.53  fof(f58,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f34])).
% 1.36/0.53  fof(f34,plain,(
% 1.36/0.53    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f9])).
% 1.36/0.53  fof(f9,axiom,(
% 1.36/0.53    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 1.36/0.53  fof(f85,plain,(
% 1.36/0.53    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f84,f40])).
% 1.36/0.53  fof(f84,plain,(
% 1.36/0.53    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) | ~v1_relat_1(k6_relat_1(X2))) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f78,f40])).
% 1.36/0.53  fof(f78,plain,(
% 1.36/0.53    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 1.36/0.53    inference(superposition,[],[f53,f52])).
% 1.36/0.53  fof(f52,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f28])).
% 1.36/0.53  fof(f28,plain,(
% 1.36/0.53    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f10])).
% 1.36/0.53  fof(f10,axiom,(
% 1.36/0.53    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 1.36/0.53  fof(f75,plain,(
% 1.36/0.53    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 1.36/0.53    inference(subsumption_resolution,[],[f71,f40])).
% 1.36/0.53  fof(f71,plain,(
% 1.36/0.53    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 1.36/0.53    inference(superposition,[],[f39,f52])).
% 1.36/0.53  fof(f39,plain,(
% 1.36/0.53    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.36/0.53    inference(cnf_transformation,[],[f38])).
% 1.36/0.53  fof(f38,plain,(
% 1.36/0.53    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f37])).
% 1.36/0.53  fof(f37,plain,(
% 1.36/0.53    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f22,plain,(
% 1.36/0.53    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f21])).
% 1.36/0.53  fof(f21,negated_conjecture,(
% 1.36/0.53    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.36/0.53    inference(negated_conjecture,[],[f20])).
% 1.36/0.53  fof(f20,conjecture,(
% 1.36/0.53    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.36/0.53  % SZS output end Proof for theBenchmark
% 1.36/0.53  % (370)------------------------------
% 1.36/0.53  % (370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (370)Termination reason: Refutation
% 1.36/0.53  
% 1.36/0.53  % (370)Memory used [KB]: 2686
% 1.36/0.53  % (370)Time elapsed: 0.111 s
% 1.36/0.53  % (370)------------------------------
% 1.36/0.53  % (370)------------------------------
% 1.36/0.53  % (366)Success in time 0.171 s
%------------------------------------------------------------------------------
