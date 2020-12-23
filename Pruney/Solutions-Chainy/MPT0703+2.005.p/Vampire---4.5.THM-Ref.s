%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:19 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 146 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  160 ( 360 expanded)
%              Number of equality atoms :   47 (  61 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f650,plain,(
    $false ),
    inference(subsumption_resolution,[],[f642,f233])).

fof(f233,plain,(
    ~ r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f149,f109])).

fof(f109,plain,(
    ! [X4] :
      ( ~ r1_tarski(sK0,X4)
      | ~ r1_tarski(X4,sK1) ) ),
    inference(superposition,[],[f89,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f89,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),sK1) ),
    inference(unit_resulting_resolution,[],[f47,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f47,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f149,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f44,f43,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f642,plain,(
    r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1))) ),
    inference(backward_demodulation,[],[f167,f641])).

fof(f641,plain,(
    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f634,f68])).

fof(f68,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f634,plain,(
    k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f209,f575])).

fof(f575,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f556])).

fof(f556,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f144,f520])).

fof(f520,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f301,f105])).

fof(f105,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k2_xboole_0(X3,X2) = X3 ) ),
    inference(superposition,[],[f58,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f301,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f286,f195])).

fof(f195,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f194,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(f194,plain,(
    ! [X0,X1] : k10_relat_1(k1_xboole_0,X1) = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f193,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f86,f76])).

fof(f76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f64,f69])).

fof(f69,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f64,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f70,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f193,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(k1_xboole_0,X0),X1) = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f192,f68])).

fof(f192,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(k1_xboole_0,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f188,f63])).

fof(f188,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(k1_xboole_0,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(k1_xboole_0,X1))) ),
    inference(unit_resulting_resolution,[],[f76,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f286,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f90,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f90,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f73,f50])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0))
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f51,f60])).

fof(f46,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f209,plain,(
    ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f200,f115])).

fof(f115,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f43,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f200,plain,(
    ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f44,f43,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) ) ),
    inference(definition_unfolding,[],[f62,f66])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f167,plain,(
    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f43,f45,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f45,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (22586)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (22570)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (22572)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (22582)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (22592)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (22569)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (22583)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (22571)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (22578)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (22598)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (22598)Refutation not found, incomplete strategy% (22598)------------------------------
% 0.21/0.54  % (22598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22598)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22598)Memory used [KB]: 1663
% 0.21/0.54  % (22598)Time elapsed: 0.002 s
% 0.21/0.54  % (22598)------------------------------
% 0.21/0.54  % (22598)------------------------------
% 0.21/0.54  % (22574)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (22585)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (22587)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (22585)Refutation not found, incomplete strategy% (22585)------------------------------
% 0.21/0.54  % (22585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22585)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22585)Memory used [KB]: 10618
% 0.21/0.54  % (22585)Time elapsed: 0.140 s
% 0.21/0.54  % (22585)------------------------------
% 0.21/0.54  % (22585)------------------------------
% 0.21/0.54  % (22594)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (22580)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (22575)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (22588)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (22591)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (22576)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (22593)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (22573)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (22590)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (22579)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (22595)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (22589)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (22579)Refutation not found, incomplete strategy% (22579)------------------------------
% 0.21/0.55  % (22579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22579)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22579)Memory used [KB]: 10746
% 0.21/0.55  % (22579)Time elapsed: 0.149 s
% 0.21/0.55  % (22579)------------------------------
% 0.21/0.55  % (22579)------------------------------
% 0.21/0.55  % (22584)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (22596)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (22577)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.50/0.56  % (22597)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.50/0.56  % (22597)Refutation not found, incomplete strategy% (22597)------------------------------
% 1.50/0.56  % (22597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (22597)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (22597)Memory used [KB]: 10746
% 1.50/0.56  % (22597)Time elapsed: 0.158 s
% 1.50/0.56  % (22597)------------------------------
% 1.50/0.56  % (22597)------------------------------
% 1.50/0.57  % (22581)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.74/0.59  % (22588)Refutation found. Thanks to Tanya!
% 1.74/0.59  % SZS status Theorem for theBenchmark
% 1.74/0.59  % SZS output start Proof for theBenchmark
% 1.74/0.59  fof(f650,plain,(
% 1.74/0.59    $false),
% 1.74/0.59    inference(subsumption_resolution,[],[f642,f233])).
% 1.74/0.59  fof(f233,plain,(
% 1.74/0.59    ~r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1)))),
% 1.74/0.59    inference(unit_resulting_resolution,[],[f149,f109])).
% 1.74/0.59  fof(f109,plain,(
% 1.74/0.59    ( ! [X4] : (~r1_tarski(sK0,X4) | ~r1_tarski(X4,sK1)) )),
% 1.74/0.59    inference(superposition,[],[f89,f58])).
% 1.74/0.59  fof(f58,plain,(
% 1.74/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.74/0.59    inference(cnf_transformation,[],[f37])).
% 1.74/0.59  fof(f37,plain,(
% 1.74/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.74/0.59    inference(ennf_transformation,[],[f5])).
% 1.74/0.59  fof(f5,axiom,(
% 1.74/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.74/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.74/0.59  fof(f89,plain,(
% 1.74/0.59    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),sK1)) )),
% 1.74/0.59    inference(unit_resulting_resolution,[],[f47,f50])).
% 1.74/0.59  fof(f50,plain,(
% 1.74/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.74/0.59    inference(cnf_transformation,[],[f30])).
% 1.74/0.59  fof(f30,plain,(
% 1.74/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.74/0.59    inference(ennf_transformation,[],[f4])).
% 1.74/0.59  fof(f4,axiom,(
% 1.74/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.74/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.74/0.59  fof(f47,plain,(
% 1.74/0.59    ~r1_tarski(sK0,sK1)),
% 1.74/0.59    inference(cnf_transformation,[],[f27])).
% 1.74/0.59  fof(f27,plain,(
% 1.74/0.59    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.74/0.59    inference(flattening,[],[f26])).
% 1.74/0.59  fof(f26,plain,(
% 1.74/0.59    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.74/0.59    inference(ennf_transformation,[],[f25])).
% 1.74/0.59  fof(f25,negated_conjecture,(
% 1.74/0.59    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.74/0.59    inference(negated_conjecture,[],[f24])).
% 1.74/0.59  fof(f24,conjecture,(
% 1.74/0.59    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.74/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 1.74/0.59  fof(f149,plain,(
% 1.74/0.59    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) )),
% 1.74/0.59    inference(unit_resulting_resolution,[],[f44,f43,f56])).
% 1.74/0.59  fof(f56,plain,(
% 1.74/0.59    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 1.74/0.59    inference(cnf_transformation,[],[f35])).
% 1.74/0.59  fof(f35,plain,(
% 1.74/0.59    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.74/0.59    inference(flattening,[],[f34])).
% 1.74/0.59  fof(f34,plain,(
% 1.74/0.59    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.74/0.60    inference(ennf_transformation,[],[f22])).
% 1.74/0.60  fof(f22,axiom,(
% 1.74/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.74/0.60  fof(f43,plain,(
% 1.74/0.60    v1_relat_1(sK2)),
% 1.74/0.60    inference(cnf_transformation,[],[f27])).
% 1.74/0.60  fof(f44,plain,(
% 1.74/0.60    v1_funct_1(sK2)),
% 1.74/0.60    inference(cnf_transformation,[],[f27])).
% 1.74/0.60  fof(f642,plain,(
% 1.74/0.60    r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1)))),
% 1.74/0.60    inference(backward_demodulation,[],[f167,f641])).
% 1.74/0.60  fof(f641,plain,(
% 1.74/0.60    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 1.74/0.60    inference(forward_demodulation,[],[f634,f68])).
% 1.74/0.60  fof(f68,plain,(
% 1.74/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.74/0.60    inference(cnf_transformation,[],[f8])).
% 1.74/0.60  fof(f8,axiom,(
% 1.74/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.74/0.60  fof(f634,plain,(
% 1.74/0.60    k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.74/0.60    inference(superposition,[],[f209,f575])).
% 1.74/0.60  fof(f575,plain,(
% 1.74/0.60    k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK2))),
% 1.74/0.60    inference(unit_resulting_resolution,[],[f46,f556])).
% 1.74/0.60  fof(f556,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.74/0.60    inference(backward_demodulation,[],[f144,f520])).
% 1.74/0.60  fof(f520,plain,(
% 1.74/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.74/0.60    inference(unit_resulting_resolution,[],[f301,f105])).
% 1.74/0.60  fof(f105,plain,(
% 1.74/0.60    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k2_xboole_0(X3,X2) = X3) )),
% 1.74/0.60    inference(superposition,[],[f58,f67])).
% 1.74/0.60  fof(f67,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f1])).
% 1.74/0.60  fof(f1,axiom,(
% 1.74/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.74/0.60  fof(f301,plain,(
% 1.74/0.60    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 1.74/0.60    inference(forward_demodulation,[],[f286,f195])).
% 1.74/0.60  fof(f195,plain,(
% 1.74/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.74/0.60    inference(forward_demodulation,[],[f194,f63])).
% 1.74/0.60  fof(f63,plain,(
% 1.74/0.60    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f17])).
% 1.74/0.60  fof(f17,axiom,(
% 1.74/0.60    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 1.74/0.60  fof(f194,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k10_relat_1(k1_xboole_0,X1) = k4_xboole_0(X0,X0)) )),
% 1.74/0.60    inference(forward_demodulation,[],[f193,f87])).
% 1.74/0.60  fof(f87,plain,(
% 1.74/0.60    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.74/0.60    inference(subsumption_resolution,[],[f86,f76])).
% 1.74/0.60  fof(f76,plain,(
% 1.74/0.60    v1_relat_1(k1_xboole_0)),
% 1.74/0.60    inference(superposition,[],[f64,f69])).
% 1.74/0.60  fof(f69,plain,(
% 1.74/0.60    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.74/0.60    inference(cnf_transformation,[],[f18])).
% 1.74/0.60  fof(f18,axiom,(
% 1.74/0.60    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.74/0.60  fof(f64,plain,(
% 1.74/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f20])).
% 1.74/0.60  fof(f20,axiom,(
% 1.74/0.60    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.74/0.60  fof(f86,plain,(
% 1.74/0.60    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.74/0.60    inference(resolution,[],[f70,f60])).
% 1.74/0.60  fof(f60,plain,(
% 1.74/0.60    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.74/0.60    inference(cnf_transformation,[],[f38])).
% 1.74/0.60  fof(f38,plain,(
% 1.74/0.60    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.74/0.60    inference(ennf_transformation,[],[f9])).
% 1.74/0.60  fof(f9,axiom,(
% 1.74/0.60    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.74/0.60  fof(f70,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f42])).
% 1.74/0.60  fof(f42,plain,(
% 1.74/0.60    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.74/0.60    inference(ennf_transformation,[],[f19])).
% 1.74/0.60  fof(f19,axiom,(
% 1.74/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.74/0.60  fof(f193,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(k1_xboole_0,X0),X1) = k4_xboole_0(X0,X0)) )),
% 1.74/0.60    inference(forward_demodulation,[],[f192,f68])).
% 1.74/0.60  fof(f192,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(k1_xboole_0,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.74/0.60    inference(forward_demodulation,[],[f188,f63])).
% 1.74/0.60  fof(f188,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(k1_xboole_0,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(k1_xboole_0,X1)))) )),
% 1.74/0.60    inference(unit_resulting_resolution,[],[f76,f71])).
% 1.74/0.60  fof(f71,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1)))) )),
% 1.74/0.60    inference(definition_unfolding,[],[f61,f66])).
% 1.74/0.60  fof(f66,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f12])).
% 1.74/0.60  fof(f12,axiom,(
% 1.74/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.74/0.60  fof(f61,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f39])).
% 1.74/0.60  fof(f39,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.74/0.60    inference(ennf_transformation,[],[f21])).
% 1.74/0.60  fof(f21,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.74/0.60  fof(f286,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 1.74/0.60    inference(unit_resulting_resolution,[],[f90,f51])).
% 1.74/0.60  fof(f51,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f31])).
% 1.74/0.60  fof(f31,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.74/0.60    inference(ennf_transformation,[],[f10])).
% 1.74/0.60  fof(f10,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.74/0.60  fof(f90,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.74/0.60    inference(unit_resulting_resolution,[],[f73,f50])).
% 1.74/0.60  fof(f73,plain,(
% 1.74/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.74/0.60    inference(equality_resolution,[],[f54])).
% 1.74/0.60  fof(f54,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.74/0.60    inference(cnf_transformation,[],[f2])).
% 1.74/0.60  fof(f2,axiom,(
% 1.74/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.74/0.60  fof(f144,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.74/0.60    inference(resolution,[],[f51,f60])).
% 1.74/0.60  fof(f46,plain,(
% 1.74/0.60    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.74/0.60    inference(cnf_transformation,[],[f27])).
% 1.74/0.60  fof(f209,plain,(
% 1.74/0.60    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_relat_1(sK2)))) )),
% 1.74/0.60    inference(forward_demodulation,[],[f200,f115])).
% 1.74/0.60  fof(f115,plain,(
% 1.74/0.60    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 1.74/0.60    inference(unit_resulting_resolution,[],[f43,f48])).
% 1.74/0.60  fof(f48,plain,(
% 1.74/0.60    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f28])).
% 1.74/0.60  fof(f28,plain,(
% 1.74/0.60    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f15])).
% 1.74/0.60  fof(f15,axiom,(
% 1.74/0.60    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.74/0.60  fof(f200,plain,(
% 1.74/0.60    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))))) )),
% 1.74/0.60    inference(unit_resulting_resolution,[],[f44,f43,f72])).
% 1.74/0.60  fof(f72,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))) )),
% 1.74/0.60    inference(definition_unfolding,[],[f62,f66])).
% 1.74/0.60  fof(f62,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f41])).
% 1.74/0.60  fof(f41,plain,(
% 1.74/0.60    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.74/0.60    inference(flattening,[],[f40])).
% 1.74/0.60  fof(f40,plain,(
% 1.74/0.60    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.74/0.60    inference(ennf_transformation,[],[f23])).
% 1.74/0.60  fof(f23,axiom,(
% 1.74/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 1.74/0.60  fof(f167,plain,(
% 1.74/0.60    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))),
% 1.74/0.60    inference(unit_resulting_resolution,[],[f43,f45,f52])).
% 1.74/0.60  fof(f52,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f33])).
% 1.74/0.60  fof(f33,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.74/0.60    inference(flattening,[],[f32])).
% 1.74/0.60  fof(f32,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.74/0.60    inference(ennf_transformation,[],[f16])).
% 1.74/0.60  fof(f16,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 1.74/0.60  fof(f45,plain,(
% 1.74/0.60    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.74/0.60    inference(cnf_transformation,[],[f27])).
% 1.74/0.60  % SZS output end Proof for theBenchmark
% 1.74/0.60  % (22588)------------------------------
% 1.74/0.60  % (22588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.60  % (22588)Termination reason: Refutation
% 1.74/0.60  
% 1.74/0.60  % (22588)Memory used [KB]: 2174
% 1.74/0.60  % (22588)Time elapsed: 0.191 s
% 1.74/0.60  % (22588)------------------------------
% 1.74/0.60  % (22588)------------------------------
% 1.74/0.60  % (22560)Success in time 0.232 s
%------------------------------------------------------------------------------
