%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:24 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 430 expanded)
%              Number of leaves         :   12 ( 126 expanded)
%              Depth                    :   16
%              Number of atoms          :  152 ( 734 expanded)
%              Number of equality atoms :   53 ( 345 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f730,plain,(
    $false ),
    inference(subsumption_resolution,[],[f729,f36])).

fof(f36,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f729,plain,(
    ~ r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f719,f477])).

fof(f477,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f163,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f75,f55])).

fof(f55,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f75,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f71,f74])).

fof(f74,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f73,f53])).

fof(f53,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f73,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f51,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f71,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f51,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f163,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f162,f55])).

fof(f162,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f161,f51])).

fof(f161,plain,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f45,f83])).

fof(f83,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f80,f54])).

fof(f54,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f51,f56,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f719,plain,(
    ~ r1_tarski(k3_xboole_0(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f56,f611,f544])).

fof(f544,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | r1_tarski(X3,k3_xboole_0(X4,X2))
      | ~ r1_tarski(k3_xboole_0(X2,X3),X4) ) ),
    inference(backward_demodulation,[],[f124,f540])).

fof(f540,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f534,f481])).

fof(f481,plain,(
    ! [X2,X3] : k3_xboole_0(X3,X2) = k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3)) ),
    inference(backward_demodulation,[],[f278,f477])).

fof(f278,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3)) = k3_xboole_0(X3,k3_xboole_0(X2,X2)) ),
    inference(superposition,[],[f101,f76])).

fof(f101,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f100,f54])).

fof(f100,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_relat_1(k6_relat_1(X0)))) ),
    inference(forward_demodulation,[],[f97,f76])).

fof(f97,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f52,f51,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f52,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f534,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f90,f477])).

fof(f90,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) ),
    inference(forward_demodulation,[],[f87,f74])).

fof(f87,plain,(
    ! [X2,X0,X1] : k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) ),
    inference(unit_resulting_resolution,[],[f51,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f124,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4))
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(k3_xboole_0(X2,X3),X4) ) ),
    inference(forward_demodulation,[],[f123,f76])).

fof(f123,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | ~ r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4)
      | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4)) ) ),
    inference(forward_demodulation,[],[f122,f54])).

fof(f122,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,k1_relat_1(k6_relat_1(X2)))
      | ~ r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4)
      | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4)) ) ),
    inference(subsumption_resolution,[],[f114,f51])).

fof(f114,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(k6_relat_1(X2))
      | ~ r1_tarski(X3,k1_relat_1(k6_relat_1(X2)))
      | ~ r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4)
      | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4)) ) ),
    inference(resolution,[],[f47,f52])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f611,plain,(
    ~ r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f139,f542,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f542,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(backward_demodulation,[],[f61,f540])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(forward_demodulation,[],[f59,f54])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f51,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f139,plain,(
    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f37,f86])).

fof(f86,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1)) ),
    inference(unit_resulting_resolution,[],[f38,f43])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (18200)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.50  % (18227)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (18208)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (18203)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (18208)Refutation not found, incomplete strategy% (18208)------------------------------
% 0.21/0.51  % (18208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18208)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (18208)Memory used [KB]: 10746
% 0.21/0.51  % (18208)Time elapsed: 0.078 s
% 0.21/0.51  % (18208)------------------------------
% 0.21/0.51  % (18208)------------------------------
% 0.21/0.51  % (18202)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (18201)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (18230)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (18230)Refutation not found, incomplete strategy% (18230)------------------------------
% 0.21/0.51  % (18230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18230)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (18230)Memory used [KB]: 1663
% 0.21/0.51  % (18230)Time elapsed: 0.084 s
% 0.21/0.51  % (18230)------------------------------
% 0.21/0.51  % (18230)------------------------------
% 0.21/0.52  % (18198)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (18213)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (18198)Refutation not found, incomplete strategy% (18198)------------------------------
% 0.21/0.52  % (18198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18198)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18198)Memory used [KB]: 1663
% 0.21/0.52  % (18198)Time elapsed: 0.116 s
% 0.21/0.52  % (18198)------------------------------
% 0.21/0.52  % (18198)------------------------------
% 0.21/0.52  % (18197)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (18221)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (18217)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (18223)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (18199)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (18212)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (18220)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (18227)Refutation not found, incomplete strategy% (18227)------------------------------
% 0.21/0.53  % (18227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18227)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18227)Memory used [KB]: 6268
% 0.21/0.53  % (18227)Time elapsed: 0.132 s
% 0.21/0.53  % (18227)------------------------------
% 0.21/0.53  % (18227)------------------------------
% 0.21/0.53  % (18214)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (18226)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (18216)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (18207)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (18225)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (18222)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (18204)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (18219)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (18206)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (18228)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (18229)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (18217)Refutation not found, incomplete strategy% (18217)------------------------------
% 0.21/0.54  % (18217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18217)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18217)Memory used [KB]: 1791
% 0.21/0.54  % (18217)Time elapsed: 0.138 s
% 0.21/0.54  % (18217)------------------------------
% 0.21/0.54  % (18217)------------------------------
% 0.21/0.54  % (18209)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (18229)Refutation not found, incomplete strategy% (18229)------------------------------
% 0.21/0.54  % (18229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18229)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18229)Memory used [KB]: 10746
% 0.21/0.54  % (18229)Time elapsed: 0.149 s
% 0.21/0.54  % (18229)------------------------------
% 0.21/0.54  % (18229)------------------------------
% 0.21/0.55  % (18211)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (18210)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (18210)Refutation not found, incomplete strategy% (18210)------------------------------
% 0.21/0.55  % (18210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18210)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18210)Memory used [KB]: 10618
% 0.21/0.55  % (18210)Time elapsed: 0.160 s
% 0.21/0.55  % (18210)------------------------------
% 0.21/0.55  % (18210)------------------------------
% 0.21/0.55  % (18214)Refutation not found, incomplete strategy% (18214)------------------------------
% 0.21/0.55  % (18214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18214)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18214)Memory used [KB]: 10618
% 0.21/0.55  % (18214)Time elapsed: 0.158 s
% 0.21/0.55  % (18214)------------------------------
% 0.21/0.55  % (18214)------------------------------
% 0.21/0.55  % (18226)Refutation not found, incomplete strategy% (18226)------------------------------
% 0.21/0.55  % (18226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18226)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18226)Memory used [KB]: 6268
% 0.21/0.55  % (18226)Time elapsed: 0.141 s
% 0.21/0.55  % (18226)------------------------------
% 0.21/0.55  % (18226)------------------------------
% 1.72/0.58  % (18219)Refutation found. Thanks to Tanya!
% 1.72/0.58  % SZS status Theorem for theBenchmark
% 1.72/0.58  % SZS output start Proof for theBenchmark
% 1.72/0.58  fof(f730,plain,(
% 1.72/0.58    $false),
% 1.72/0.58    inference(subsumption_resolution,[],[f729,f36])).
% 1.72/0.58  fof(f36,plain,(
% 1.72/0.58    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.72/0.58    inference(cnf_transformation,[],[f25])).
% 1.72/0.58  fof(f25,plain,(
% 1.72/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.72/0.58    inference(flattening,[],[f24])).
% 1.72/0.58  fof(f24,plain,(
% 1.72/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.72/0.58    inference(ennf_transformation,[],[f23])).
% 1.72/0.58  fof(f23,negated_conjecture,(
% 1.72/0.58    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.72/0.58    inference(negated_conjecture,[],[f22])).
% 1.72/0.58  fof(f22,conjecture,(
% 1.72/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 1.72/0.58  fof(f729,plain,(
% 1.72/0.58    ~r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.72/0.58    inference(forward_demodulation,[],[f719,f477])).
% 1.72/0.58  fof(f477,plain,(
% 1.72/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.72/0.58    inference(superposition,[],[f163,f76])).
% 1.72/0.58  fof(f76,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 1.72/0.58    inference(forward_demodulation,[],[f75,f55])).
% 1.72/0.58  fof(f55,plain,(
% 1.72/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.72/0.58    inference(cnf_transformation,[],[f14])).
% 1.72/0.58  fof(f14,axiom,(
% 1.72/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.72/0.58  fof(f75,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1)))) )),
% 1.72/0.58    inference(backward_demodulation,[],[f71,f74])).
% 1.72/0.58  fof(f74,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.72/0.58    inference(forward_demodulation,[],[f73,f53])).
% 1.72/0.58  fof(f53,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f21])).
% 1.72/0.58  fof(f21,axiom,(
% 1.72/0.58    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.72/0.58  fof(f73,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f51,f46])).
% 1.72/0.58  fof(f46,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f30])).
% 1.72/0.58  fof(f30,plain,(
% 1.72/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f15])).
% 1.72/0.58  fof(f15,axiom,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.72/0.58  fof(f51,plain,(
% 1.72/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f17])).
% 1.72/0.58  fof(f17,axiom,(
% 1.72/0.58    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.72/0.58  fof(f71,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f51,f45])).
% 1.72/0.58  fof(f45,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f29])).
% 1.72/0.58  fof(f29,plain,(
% 1.72/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f12])).
% 1.72/0.58  fof(f12,axiom,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.72/0.58  fof(f163,plain,(
% 1.72/0.58    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.72/0.58    inference(forward_demodulation,[],[f162,f55])).
% 1.72/0.58  fof(f162,plain,(
% 1.72/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) )),
% 1.72/0.58    inference(subsumption_resolution,[],[f161,f51])).
% 1.72/0.58  fof(f161,plain,(
% 1.72/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.72/0.58    inference(superposition,[],[f45,f83])).
% 1.72/0.58  fof(f83,plain,(
% 1.72/0.58    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.72/0.58    inference(forward_demodulation,[],[f80,f54])).
% 1.72/0.58  fof(f54,plain,(
% 1.72/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.72/0.58    inference(cnf_transformation,[],[f14])).
% 1.72/0.58  fof(f80,plain,(
% 1.72/0.58    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f51,f56,f44])).
% 1.72/0.58  fof(f44,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 1.72/0.58    inference(cnf_transformation,[],[f28])).
% 1.72/0.58  fof(f28,plain,(
% 1.72/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(flattening,[],[f27])).
% 1.72/0.58  fof(f27,plain,(
% 1.72/0.58    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f16])).
% 1.72/0.58  fof(f16,axiom,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.72/0.58  fof(f56,plain,(
% 1.72/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.72/0.58    inference(equality_resolution,[],[f41])).
% 1.72/0.58  fof(f41,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.72/0.58    inference(cnf_transformation,[],[f1])).
% 1.72/0.58  fof(f1,axiom,(
% 1.72/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.72/0.58  fof(f719,plain,(
% 1.72/0.58    ~r1_tarski(k3_xboole_0(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),sK1)),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f56,f611,f544])).
% 1.72/0.58  fof(f544,plain,(
% 1.72/0.58    ( ! [X4,X2,X3] : (~r1_tarski(X3,X2) | r1_tarski(X3,k3_xboole_0(X4,X2)) | ~r1_tarski(k3_xboole_0(X2,X3),X4)) )),
% 1.72/0.58    inference(backward_demodulation,[],[f124,f540])).
% 1.72/0.58  fof(f540,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 1.72/0.58    inference(forward_demodulation,[],[f534,f481])).
% 1.72/0.58  fof(f481,plain,(
% 1.72/0.58    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3))) )),
% 1.72/0.58    inference(backward_demodulation,[],[f278,f477])).
% 1.72/0.58  fof(f278,plain,(
% 1.72/0.58    ( ! [X2,X3] : (k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3)) = k3_xboole_0(X3,k3_xboole_0(X2,X2))) )),
% 1.72/0.58    inference(superposition,[],[f101,f76])).
% 1.72/0.58  fof(f101,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0))) )),
% 1.72/0.58    inference(forward_demodulation,[],[f100,f54])).
% 1.72/0.58  fof(f100,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_relat_1(k6_relat_1(X0))))) )),
% 1.72/0.58    inference(forward_demodulation,[],[f97,f76])).
% 1.72/0.58  fof(f97,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) )),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f52,f51,f50])).
% 1.72/0.58  fof(f50,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f35])).
% 1.72/0.58  fof(f35,plain,(
% 1.72/0.58    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(flattening,[],[f34])).
% 1.72/0.58  fof(f34,plain,(
% 1.72/0.58    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.72/0.58    inference(ennf_transformation,[],[f19])).
% 1.72/0.58  fof(f19,axiom,(
% 1.72/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 1.72/0.58  fof(f52,plain,(
% 1.72/0.58    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f17])).
% 1.72/0.58  fof(f534,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 1.72/0.58    inference(superposition,[],[f90,f477])).
% 1.72/0.58  fof(f90,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2)) )),
% 1.72/0.58    inference(forward_demodulation,[],[f87,f74])).
% 1.72/0.58  fof(f87,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2))) )),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f51,f43])).
% 1.72/0.58  fof(f43,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f26])).
% 1.72/0.58  fof(f26,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.72/0.58    inference(ennf_transformation,[],[f18])).
% 1.72/0.58  fof(f18,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.72/0.58  fof(f124,plain,(
% 1.72/0.58    ( ! [X4,X2,X3] : (r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4)) | ~r1_tarski(X3,X2) | ~r1_tarski(k3_xboole_0(X2,X3),X4)) )),
% 1.72/0.58    inference(forward_demodulation,[],[f123,f76])).
% 1.72/0.58  fof(f123,plain,(
% 1.72/0.58    ( ! [X4,X2,X3] : (~r1_tarski(X3,X2) | ~r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4) | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4))) )),
% 1.72/0.58    inference(forward_demodulation,[],[f122,f54])).
% 1.72/0.58  fof(f122,plain,(
% 1.72/0.58    ( ! [X4,X2,X3] : (~r1_tarski(X3,k1_relat_1(k6_relat_1(X2))) | ~r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4) | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4))) )),
% 1.72/0.58    inference(subsumption_resolution,[],[f114,f51])).
% 1.72/0.58  fof(f114,plain,(
% 1.72/0.58    ( ! [X4,X2,X3] : (~v1_relat_1(k6_relat_1(X2)) | ~r1_tarski(X3,k1_relat_1(k6_relat_1(X2))) | ~r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4) | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4))) )),
% 1.72/0.58    inference(resolution,[],[f47,f52])).
% 1.72/0.58  fof(f47,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f32])).
% 1.72/0.58  fof(f32,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.72/0.58    inference(flattening,[],[f31])).
% 1.72/0.58  fof(f31,plain,(
% 1.72/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.72/0.58    inference(ennf_transformation,[],[f20])).
% 1.72/0.58  fof(f20,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 1.72/0.58  fof(f611,plain,(
% 1.72/0.58    ~r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f139,f542,f42])).
% 1.72/0.58  fof(f42,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.72/0.58    inference(cnf_transformation,[],[f1])).
% 1.72/0.58  fof(f542,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.72/0.58    inference(backward_demodulation,[],[f61,f540])).
% 1.72/0.58  fof(f61,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.72/0.58    inference(forward_demodulation,[],[f59,f54])).
% 1.72/0.58  fof(f59,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0)))) )),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f51,f48])).
% 1.72/0.58  fof(f48,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f33])).
% 1.72/0.58  fof(f33,plain,(
% 1.72/0.58    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f13])).
% 1.72/0.58  fof(f13,axiom,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.72/0.58  fof(f139,plain,(
% 1.72/0.58    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.72/0.58    inference(superposition,[],[f37,f86])).
% 1.72/0.58  fof(f86,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1))) )),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f38,f43])).
% 1.72/0.58  fof(f38,plain,(
% 1.72/0.58    v1_relat_1(sK0)),
% 1.72/0.58    inference(cnf_transformation,[],[f25])).
% 1.72/0.58  fof(f37,plain,(
% 1.72/0.58    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.72/0.58    inference(cnf_transformation,[],[f25])).
% 1.72/0.58  % SZS output end Proof for theBenchmark
% 1.72/0.58  % (18219)------------------------------
% 1.72/0.58  % (18219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.58  % (18219)Termination reason: Refutation
% 1.72/0.58  
% 1.72/0.58  % (18219)Memory used [KB]: 2174
% 1.72/0.58  % (18219)Time elapsed: 0.186 s
% 1.72/0.58  % (18219)------------------------------
% 1.72/0.58  % (18219)------------------------------
% 1.72/0.58  % (18192)Success in time 0.222 s
%------------------------------------------------------------------------------
