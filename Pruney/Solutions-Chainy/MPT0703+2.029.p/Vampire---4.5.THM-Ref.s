%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:22 EST 2020

% Result     : Theorem 31.94s
% Output     : Refutation 31.94s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 466 expanded)
%              Number of leaves         :   11 ( 116 expanded)
%              Depth                    :   27
%              Number of atoms          :  196 (1081 expanded)
%              Number of equality atoms :   33 ( 162 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16796,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16795,f29])).

fof(f29,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f16795,plain,(
    r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f16738,f71])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X0),X1) ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f37,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f39,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
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

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f16738,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK0),sK1)
    | r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f258,f16056])).

fof(f16056,plain,(
    k6_subset_1(sK0,sK1) = k6_subset_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f12812,f16055])).

fof(f16055,plain,(
    ! [X27] : k6_subset_1(sK0,sK0) = k9_relat_1(sK2,k6_subset_1(X27,X27)) ),
    inference(subsumption_resolution,[],[f16054,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f16054,plain,(
    ! [X27] :
      ( k6_subset_1(sK0,sK0) = k9_relat_1(sK2,k6_subset_1(X27,X27))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f16053,f3939])).

fof(f3939,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2)) ),
    inference(resolution,[],[f3011,f234])).

fof(f234,plain,(
    ! [X6,X8,X7] : r1_tarski(k6_subset_1(k6_subset_1(X6,X7),X8),X6) ),
    inference(resolution,[],[f111,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f111,plain,(
    ! [X17,X15,X16] :
      ( ~ r1_tarski(X15,k6_subset_1(X16,X17))
      | r1_tarski(X15,X16) ) ),
    inference(resolution,[],[f48,f42])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f39,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f3011,plain,(
    ! [X58] :
      ( ~ r1_tarski(k6_subset_1(X58,k2_relat_1(sK2)),sK0)
      | r1_tarski(X58,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f258,f115])).

fof(f115,plain,(
    ! [X25] :
      ( r1_tarski(X25,k2_relat_1(sK2))
      | ~ r1_tarski(X25,sK0) ) ),
    inference(resolution,[],[f48,f28])).

fof(f28,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f16053,plain,(
    ! [X27] :
      ( k6_subset_1(sK0,sK0) = k9_relat_1(sK2,k6_subset_1(X27,X27))
      | ~ r1_tarski(k6_subset_1(sK0,sK0),k2_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f15802,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15802,plain,(
    ! [X27] :
      ( k6_subset_1(sK0,sK0) = k9_relat_1(sK2,k6_subset_1(X27,X27))
      | ~ v1_funct_1(sK2)
      | ~ r1_tarski(k6_subset_1(sK0,sK0),k2_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f33,f4073])).

fof(f4073,plain,(
    ! [X71] : k10_relat_1(sK2,k6_subset_1(sK0,sK0)) = k6_subset_1(X71,X71) ),
    inference(resolution,[],[f94,f3257])).

fof(f3257,plain,(
    ! [X34] : r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK0)),X34) ),
    inference(superposition,[],[f1840,f126])).

fof(f126,plain,(
    ! [X4,X3] : k6_subset_1(X3,X3) = k6_subset_1(k6_subset_1(X3,X3),X4) ),
    inference(resolution,[],[f50,f71])).

fof(f50,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k6_subset_1(X1,X2))
      | k6_subset_1(X1,X2) = X1 ) ),
    inference(resolution,[],[f36,f42])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1840,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,X0),sK1)),X1) ),
    inference(subsumption_resolution,[],[f1839,f25])).

fof(f1839,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,X0),sK1)),X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f1836,f26])).

fof(f1836,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,X0),sK1)),X1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f1272,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f1272,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(k10_relat_1(sK2,k6_subset_1(sK0,X0)),k10_relat_1(sK2,sK1)),X1) ),
    inference(subsumption_resolution,[],[f1271,f25])).

fof(f1271,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k10_relat_1(sK2,k6_subset_1(sK0,X0)),k10_relat_1(sK2,sK1)),X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f1267,f26])).

fof(f1267,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k10_relat_1(sK2,k6_subset_1(sK0,X0)),k10_relat_1(sK2,sK1)),X1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f972,f40])).

fof(f972,plain,(
    ! [X8,X7] : r1_tarski(k6_subset_1(k6_subset_1(k10_relat_1(sK2,sK0),X7),k10_relat_1(sK2,sK1)),X8) ),
    inference(resolution,[],[f780,f43])).

fof(f780,plain,(
    ! [X6,X5] : r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),X5),k2_xboole_0(k10_relat_1(sK2,sK1),X6)) ),
    inference(resolution,[],[f268,f43])).

fof(f268,plain,(
    ! [X8,X9] : r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(X8,k2_xboole_0(k10_relat_1(sK2,sK1),X9))) ),
    inference(resolution,[],[f259,f80])).

fof(f80,plain,(
    ! [X6,X4,X5] : r1_tarski(X4,k2_xboole_0(X5,k2_xboole_0(X4,X6))) ),
    inference(resolution,[],[f65,f39])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f44,f42])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f38,f31])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f259,plain,(
    ! [X46] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK1),X46)
      | r1_tarski(k10_relat_1(sK2,sK0),X46) ) ),
    inference(superposition,[],[f163,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f150,f45])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X0)
      | ~ r1_tarski(X1,X0)
      | k2_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f68,f47])).

fof(f68,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X4,k2_xboole_0(X5,X3))
      | ~ r1_tarski(X5,X4)
      | ~ r1_tarski(X3,X4)
      | k2_xboole_0(X5,X3) = X4 ) ),
    inference(resolution,[],[f41,f36])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f163,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(X0,k10_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f142,f44])).

fof(f142,plain,(
    ! [X2] : r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),X2),k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f114,f42])).

fof(f114,plain,(
    ! [X24] :
      ( ~ r1_tarski(X24,k10_relat_1(sK2,sK0))
      | r1_tarski(X24,k10_relat_1(sK2,sK1)) ) ),
    inference(resolution,[],[f48,f27])).

fof(f27,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f94,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k6_subset_1(X3,X3))
      | k6_subset_1(X3,X3) = X2 ) ),
    inference(resolution,[],[f71,f36])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f12812,plain,(
    ! [X22] : k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k6_subset_1(X22,X22)) ),
    inference(subsumption_resolution,[],[f12811,f25])).

fof(f12811,plain,(
    ! [X22] :
      ( k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k6_subset_1(X22,X22))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f12810,f3939])).

fof(f12810,plain,(
    ! [X22] :
      ( k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k6_subset_1(X22,X22))
      | ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f12592,f26])).

fof(f12592,plain,(
    ! [X22] :
      ( k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k6_subset_1(X22,X22))
      | ~ v1_funct_1(sK2)
      | ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f33,f4072])).

fof(f4072,plain,(
    ! [X70] : k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k6_subset_1(X70,X70) ),
    inference(resolution,[],[f94,f330])).

fof(f330,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X0) ),
    inference(subsumption_resolution,[],[f329,f25])).

fof(f329,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f327,f26])).

fof(f327,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f289,f40])).

fof(f289,plain,(
    ! [X1] : r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),X1) ),
    inference(resolution,[],[f264,f43])).

fof(f264,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X2)) ),
    inference(resolution,[],[f259,f47])).

fof(f258,plain,(
    ! [X45,X44] :
      ( ~ r1_tarski(k6_subset_1(X45,X44),X44)
      | r1_tarski(X45,X44) ) ),
    inference(superposition,[],[f66,f161])).

fof(f66,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,k6_subset_1(X2,X3))) ),
    inference(resolution,[],[f44,f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:08:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (18436)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (18452)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.48  % (18444)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.49  % (18454)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.50  % (18433)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (18434)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (18439)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (18458)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (18440)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (18443)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (18445)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (18458)Refutation not found, incomplete strategy% (18458)------------------------------
% 0.20/0.53  % (18458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18430)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (18458)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (18458)Memory used [KB]: 10746
% 0.20/0.53  % (18458)Time elapsed: 0.083 s
% 0.20/0.53  % (18458)------------------------------
% 0.20/0.53  % (18458)------------------------------
% 0.20/0.53  % (18450)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (18438)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (18451)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (18435)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (18442)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (18459)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (18442)Refutation not found, incomplete strategy% (18442)------------------------------
% 0.20/0.54  % (18442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18459)Refutation not found, incomplete strategy% (18459)------------------------------
% 0.20/0.54  % (18459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18459)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (18459)Memory used [KB]: 1663
% 0.20/0.54  % (18459)Time elapsed: 0.002 s
% 0.20/0.54  % (18459)------------------------------
% 0.20/0.54  % (18459)------------------------------
% 0.20/0.54  % (18442)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (18442)Memory used [KB]: 10618
% 0.20/0.54  % (18442)Time elapsed: 0.091 s
% 0.20/0.54  % (18442)------------------------------
% 0.20/0.54  % (18442)------------------------------
% 0.20/0.54  % (18449)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (18432)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.55  % (18437)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (18440)Refutation not found, incomplete strategy% (18440)------------------------------
% 0.20/0.55  % (18440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (18440)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (18440)Memory used [KB]: 10746
% 0.20/0.55  % (18440)Time elapsed: 0.123 s
% 0.20/0.55  % (18440)------------------------------
% 0.20/0.55  % (18440)------------------------------
% 0.20/0.55  % (18441)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (18455)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (18448)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.56  % (18453)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.56  % (18431)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.56  % (18431)Refutation not found, incomplete strategy% (18431)------------------------------
% 0.20/0.56  % (18431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18431)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (18431)Memory used [KB]: 1663
% 0.20/0.56  % (18431)Time elapsed: 0.162 s
% 0.20/0.56  % (18431)------------------------------
% 0.20/0.56  % (18431)------------------------------
% 0.20/0.57  % (18457)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.57  % (18446)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.57  % (18446)Refutation not found, incomplete strategy% (18446)------------------------------
% 0.20/0.57  % (18446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (18446)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (18446)Memory used [KB]: 10618
% 0.20/0.57  % (18446)Time elapsed: 0.160 s
% 0.20/0.57  % (18446)------------------------------
% 0.20/0.57  % (18446)------------------------------
% 1.69/0.58  % (18456)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.69/0.59  % (18447)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.88/0.65  % (18445)Refutation not found, incomplete strategy% (18445)------------------------------
% 1.88/0.65  % (18445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.65  % (18445)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.65  
% 1.88/0.65  % (18445)Memory used [KB]: 6140
% 1.88/0.65  % (18445)Time elapsed: 0.209 s
% 1.88/0.65  % (18445)------------------------------
% 1.88/0.65  % (18445)------------------------------
% 2.26/0.67  % (18499)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.26/0.67  % (18499)Refutation not found, incomplete strategy% (18499)------------------------------
% 2.26/0.67  % (18499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.67  % (18499)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.67  
% 2.26/0.67  % (18499)Memory used [KB]: 6140
% 2.26/0.67  % (18499)Time elapsed: 0.004 s
% 2.26/0.67  % (18499)------------------------------
% 2.26/0.67  % (18499)------------------------------
% 2.26/0.70  % (18498)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.26/0.71  % (18433)Refutation not found, incomplete strategy% (18433)------------------------------
% 2.26/0.71  % (18433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.71  % (18433)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.71  
% 2.26/0.71  % (18433)Memory used [KB]: 6140
% 2.26/0.71  % (18433)Time elapsed: 0.315 s
% 2.26/0.71  % (18433)------------------------------
% 2.26/0.71  % (18433)------------------------------
% 2.26/0.72  % (18500)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.26/0.72  % (18503)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.26/0.74  % (18501)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.26/0.75  % (18430)Refutation not found, incomplete strategy% (18430)------------------------------
% 2.26/0.75  % (18430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.75  % (18430)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.75  
% 2.26/0.75  % (18430)Memory used [KB]: 1663
% 2.26/0.75  % (18430)Time elapsed: 0.344 s
% 2.26/0.75  % (18430)------------------------------
% 2.26/0.75  % (18430)------------------------------
% 2.26/0.75  % (18505)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.96/0.76  % (18502)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.96/0.76  % (18497)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.96/0.79  % (18454)Time limit reached!
% 2.96/0.79  % (18454)------------------------------
% 2.96/0.79  % (18454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.96/0.79  % (18454)Termination reason: Time limit
% 2.96/0.79  
% 2.96/0.79  % (18454)Memory used [KB]: 13304
% 2.96/0.79  % (18454)Time elapsed: 0.404 s
% 2.96/0.79  % (18454)------------------------------
% 2.96/0.79  % (18454)------------------------------
% 3.19/0.83  % (18519)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.39/0.84  % (18432)Time limit reached!
% 3.39/0.84  % (18432)------------------------------
% 3.39/0.84  % (18432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.39/0.84  % (18432)Termination reason: Time limit
% 3.39/0.84  
% 3.39/0.84  % (18432)Memory used [KB]: 6524
% 3.39/0.84  % (18432)Time elapsed: 0.431 s
% 3.39/0.84  % (18432)------------------------------
% 3.39/0.84  % (18432)------------------------------
% 3.39/0.88  % (18436)Time limit reached!
% 3.39/0.88  % (18436)------------------------------
% 3.39/0.88  % (18436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.39/0.88  % (18436)Termination reason: Time limit
% 3.39/0.88  % (18436)Termination phase: Saturation
% 3.39/0.88  
% 3.39/0.88  % (18436)Memory used [KB]: 15735
% 3.39/0.88  % (18436)Time elapsed: 0.500 s
% 3.39/0.88  % (18436)------------------------------
% 3.39/0.88  % (18436)------------------------------
% 3.39/0.89  % (18444)Time limit reached!
% 3.39/0.89  % (18444)------------------------------
% 3.39/0.89  % (18444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.39/0.89  % (18444)Termination reason: Time limit
% 3.39/0.89  
% 3.39/0.89  % (18444)Memory used [KB]: 5117
% 3.39/0.89  % (18444)Time elapsed: 0.503 s
% 3.39/0.89  % (18444)------------------------------
% 3.39/0.89  % (18444)------------------------------
% 3.39/0.89  % (18535)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.39/0.91  % (18552)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.92/0.98  % (18578)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 4.18/1.00  % (18437)Time limit reached!
% 4.18/1.00  % (18437)------------------------------
% 4.18/1.00  % (18437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/1.00  % (18437)Termination reason: Time limit
% 4.18/1.00  % (18437)Termination phase: Saturation
% 4.18/1.00  
% 4.18/1.00  % (18437)Memory used [KB]: 6396
% 4.18/1.00  % (18437)Time elapsed: 0.600 s
% 4.18/1.00  % (18437)------------------------------
% 4.18/1.00  % (18437)------------------------------
% 4.18/1.02  % (18614)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 4.18/1.02  % (18626)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 4.65/1.14  % (18666)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 7.04/1.27  % (18666)Refutation not found, incomplete strategy% (18666)------------------------------
% 7.04/1.27  % (18666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.04/1.27  % (18666)Termination reason: Refutation not found, incomplete strategy
% 7.04/1.27  
% 7.04/1.27  % (18666)Memory used [KB]: 6140
% 7.04/1.27  % (18666)Time elapsed: 0.244 s
% 7.04/1.27  % (18666)------------------------------
% 7.04/1.27  % (18666)------------------------------
% 7.50/1.34  % (18626)Time limit reached!
% 7.50/1.34  % (18626)------------------------------
% 7.50/1.34  % (18626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.50/1.34  % (18626)Termination reason: Time limit
% 7.50/1.34  
% 7.50/1.34  % (18626)Memory used [KB]: 14456
% 7.50/1.34  % (18626)Time elapsed: 0.410 s
% 7.50/1.34  % (18626)------------------------------
% 7.50/1.34  % (18626)------------------------------
% 7.50/1.34  % (18503)Time limit reached!
% 7.50/1.34  % (18503)------------------------------
% 7.50/1.34  % (18503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.50/1.34  % (18503)Termination reason: Time limit
% 7.50/1.34  
% 7.50/1.34  % (18503)Memory used [KB]: 22003
% 7.50/1.34  % (18503)Time elapsed: 0.625 s
% 7.50/1.34  % (18503)------------------------------
% 7.50/1.34  % (18503)------------------------------
% 7.91/1.41  % (18740)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 7.91/1.42  % (18457)Time limit reached!
% 7.91/1.42  % (18457)------------------------------
% 7.91/1.42  % (18457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.42  % (18457)Termination reason: Time limit
% 7.91/1.42  % (18457)Termination phase: Saturation
% 7.91/1.42  
% 7.91/1.42  % (18457)Memory used [KB]: 12153
% 7.91/1.42  % (18457)Time elapsed: 1.0000 s
% 7.91/1.42  % (18457)------------------------------
% 7.91/1.42  % (18457)------------------------------
% 8.60/1.46  % (18742)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 8.60/1.46  % (18741)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 9.22/1.54  % (18740)Refutation not found, incomplete strategy% (18740)------------------------------
% 9.22/1.54  % (18740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.30/1.55  % (18740)Termination reason: Refutation not found, incomplete strategy
% 9.30/1.55  
% 9.30/1.55  % (18740)Memory used [KB]: 6140
% 9.30/1.55  % (18740)Time elapsed: 0.237 s
% 9.30/1.55  % (18740)------------------------------
% 9.30/1.55  % (18740)------------------------------
% 9.30/1.56  % (18743)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 9.30/1.59  % (18535)Time limit reached!
% 9.30/1.59  % (18535)------------------------------
% 9.30/1.59  % (18535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.30/1.59  % (18535)Termination reason: Time limit
% 9.30/1.59  % (18535)Termination phase: Saturation
% 9.30/1.59  
% 9.30/1.59  % (18535)Memory used [KB]: 17142
% 9.30/1.59  % (18535)Time elapsed: 0.800 s
% 9.30/1.59  % (18535)------------------------------
% 9.30/1.59  % (18535)------------------------------
% 10.08/1.68  % (18744)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 10.08/1.70  % (18743)Refutation not found, incomplete strategy% (18743)------------------------------
% 10.08/1.70  % (18743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.08/1.70  % (18743)Termination reason: Refutation not found, incomplete strategy
% 10.08/1.70  
% 10.08/1.70  % (18743)Memory used [KB]: 6140
% 10.08/1.70  % (18743)Time elapsed: 0.253 s
% 10.08/1.70  % (18743)------------------------------
% 10.08/1.70  % (18743)------------------------------
% 10.08/1.71  % (18435)Time limit reached!
% 10.08/1.71  % (18435)------------------------------
% 10.08/1.71  % (18435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.08/1.71  % (18435)Termination reason: Time limit
% 10.08/1.71  
% 10.08/1.71  % (18435)Memory used [KB]: 9722
% 10.08/1.71  % (18435)Time elapsed: 1.305 s
% 10.08/1.71  % (18435)------------------------------
% 10.08/1.71  % (18435)------------------------------
% 10.08/1.73  % (18745)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.44/1.82  % (18742)Time limit reached!
% 11.44/1.82  % (18742)------------------------------
% 11.44/1.82  % (18742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.44/1.82  % (18742)Termination reason: Time limit
% 11.44/1.82  % (18742)Termination phase: Saturation
% 11.44/1.82  
% 11.44/1.82  % (18742)Memory used [KB]: 8955
% 11.44/1.82  % (18742)Time elapsed: 0.400 s
% 11.44/1.82  % (18742)------------------------------
% 11.44/1.82  % (18742)------------------------------
% 11.92/1.86  % (18741)Time limit reached!
% 11.92/1.86  % (18741)------------------------------
% 11.92/1.86  % (18741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.92/1.87  % (18741)Termination reason: Time limit
% 11.92/1.87  % (18741)Termination phase: Saturation
% 11.92/1.87  
% 11.92/1.87  % (18741)Memory used [KB]: 12409
% 11.92/1.87  % (18741)Time elapsed: 0.500 s
% 11.92/1.87  % (18741)------------------------------
% 11.92/1.87  % (18741)------------------------------
% 12.62/2.01  % (18744)Time limit reached!
% 12.62/2.01  % (18744)------------------------------
% 12.62/2.01  % (18744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.62/2.01  % (18744)Termination reason: Time limit
% 12.62/2.01  % (18744)Termination phase: Saturation
% 12.62/2.01  
% 12.62/2.01  % (18744)Memory used [KB]: 4605
% 12.62/2.01  % (18744)Time elapsed: 0.400 s
% 12.62/2.01  % (18744)------------------------------
% 12.62/2.01  % (18744)------------------------------
% 12.62/2.03  % (18745)Time limit reached!
% 12.62/2.03  % (18745)------------------------------
% 12.62/2.03  % (18745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.39/2.04  % (18456)Time limit reached!
% 13.39/2.04  % (18456)------------------------------
% 13.39/2.04  % (18456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.39/2.04  % (18745)Termination reason: Time limit
% 13.39/2.04  % (18745)Termination phase: Saturation
% 13.39/2.04  
% 13.39/2.04  % (18745)Memory used [KB]: 9850
% 13.39/2.04  % (18745)Time elapsed: 0.400 s
% 13.39/2.04  % (18745)------------------------------
% 13.39/2.04  % (18745)------------------------------
% 13.39/2.06  % (18456)Termination reason: Time limit
% 13.39/2.06  
% 13.39/2.06  % (18456)Memory used [KB]: 22387
% 13.39/2.06  % (18456)Time elapsed: 1.632 s
% 13.39/2.06  % (18456)------------------------------
% 13.39/2.06  % (18456)------------------------------
% 14.74/2.22  % (18450)Time limit reached!
% 14.74/2.22  % (18450)------------------------------
% 14.74/2.22  % (18450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.74/2.23  % (18450)Termination reason: Time limit
% 14.74/2.23  
% 14.74/2.23  % (18450)Memory used [KB]: 25969
% 14.74/2.23  % (18450)Time elapsed: 1.812 s
% 14.74/2.23  % (18450)------------------------------
% 14.74/2.23  % (18450)------------------------------
% 25.13/3.53  % (18441)Time limit reached!
% 25.13/3.53  % (18441)------------------------------
% 25.13/3.53  % (18441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.13/3.53  % (18441)Termination reason: Time limit
% 25.13/3.53  % (18441)Termination phase: Saturation
% 25.13/3.53  
% 25.13/3.53  % (18441)Memory used [KB]: 49892
% 25.13/3.53  % (18441)Time elapsed: 3.100 s
% 25.13/3.53  % (18441)------------------------------
% 25.13/3.53  % (18441)------------------------------
% 25.13/3.53  % (18438)Time limit reached!
% 25.13/3.53  % (18438)------------------------------
% 25.13/3.53  % (18438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.13/3.53  % (18438)Termination reason: Time limit
% 25.13/3.53  % (18438)Termination phase: Saturation
% 25.13/3.53  
% 25.13/3.53  % (18438)Memory used [KB]: 20724
% 25.13/3.53  % (18438)Time elapsed: 3.100 s
% 25.13/3.53  % (18438)------------------------------
% 25.13/3.53  % (18438)------------------------------
% 26.66/3.71  % (18449)Time limit reached!
% 26.66/3.71  % (18449)------------------------------
% 26.66/3.71  % (18449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.66/3.71  % (18449)Termination reason: Time limit
% 26.66/3.71  % (18449)Termination phase: Saturation
% 26.66/3.71  
% 26.66/3.71  % (18449)Memory used [KB]: 26737
% 26.66/3.71  % (18449)Time elapsed: 3.300 s
% 26.66/3.71  % (18449)------------------------------
% 26.66/3.71  % (18449)------------------------------
% 27.16/3.78  % (18519)Time limit reached!
% 27.16/3.78  % (18519)------------------------------
% 27.16/3.78  % (18519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 27.16/3.78  % (18519)Termination reason: Time limit
% 27.16/3.78  % (18519)Termination phase: Saturation
% 27.16/3.78  
% 27.16/3.78  % (18519)Memory used [KB]: 31086
% 27.16/3.78  % (18519)Time elapsed: 3.0000 s
% 27.16/3.78  % (18519)------------------------------
% 27.16/3.78  % (18519)------------------------------
% 28.96/3.99  % (18500)Time limit reached!
% 28.96/3.99  % (18500)------------------------------
% 28.96/3.99  % (18500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 28.96/4.00  % (18500)Termination reason: Time limit
% 28.96/4.00  % (18500)Termination phase: Saturation
% 28.96/4.00  
% 28.96/4.00  % (18500)Memory used [KB]: 55393
% 28.96/4.00  % (18500)Time elapsed: 3.400 s
% 28.96/4.00  % (18500)------------------------------
% 28.96/4.00  % (18500)------------------------------
% 28.96/4.04  % (18505)Time limit reached!
% 28.96/4.04  % (18505)------------------------------
% 28.96/4.04  % (18505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 28.96/4.04  % (18505)Termination reason: Time limit
% 28.96/4.04  % (18505)Termination phase: Saturation
% 28.96/4.04  
% 28.96/4.04  % (18505)Memory used [KB]: 21748
% 28.96/4.04  % (18505)Time elapsed: 3.300 s
% 28.96/4.04  % (18505)------------------------------
% 28.96/4.04  % (18505)------------------------------
% 31.94/4.36  % (18552)Refutation found. Thanks to Tanya!
% 31.94/4.36  % SZS status Theorem for theBenchmark
% 31.94/4.36  % SZS output start Proof for theBenchmark
% 31.94/4.36  fof(f16796,plain,(
% 31.94/4.36    $false),
% 31.94/4.36    inference(subsumption_resolution,[],[f16795,f29])).
% 31.94/4.36  fof(f29,plain,(
% 31.94/4.36    ~r1_tarski(sK0,sK1)),
% 31.94/4.36    inference(cnf_transformation,[],[f14])).
% 31.94/4.36  fof(f14,plain,(
% 31.94/4.36    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 31.94/4.36    inference(flattening,[],[f13])).
% 31.94/4.36  fof(f13,plain,(
% 31.94/4.36    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 31.94/4.36    inference(ennf_transformation,[],[f12])).
% 31.94/4.36  fof(f12,negated_conjecture,(
% 31.94/4.36    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 31.94/4.36    inference(negated_conjecture,[],[f11])).
% 31.94/4.36  fof(f11,conjecture,(
% 31.94/4.36    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 31.94/4.36    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 31.94/4.36  fof(f16795,plain,(
% 31.94/4.36    r1_tarski(sK0,sK1)),
% 31.94/4.36    inference(subsumption_resolution,[],[f16738,f71])).
% 31.94/4.36  fof(f71,plain,(
% 31.94/4.36    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X0),X1)) )),
% 31.94/4.36    inference(resolution,[],[f47,f43])).
% 31.94/4.36  fof(f43,plain,(
% 31.94/4.36    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 31.94/4.36    inference(definition_unfolding,[],[f37,f31])).
% 31.94/4.36  fof(f31,plain,(
% 31.94/4.36    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 31.94/4.36    inference(cnf_transformation,[],[f8])).
% 31.94/4.36  fof(f8,axiom,(
% 31.94/4.36    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 31.94/4.36    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 31.94/4.36  fof(f37,plain,(
% 31.94/4.36    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 31.94/4.36    inference(cnf_transformation,[],[f18])).
% 31.94/4.36  fof(f18,plain,(
% 31.94/4.36    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 31.94/4.36    inference(ennf_transformation,[],[f5])).
% 31.94/4.36  fof(f5,axiom,(
% 31.94/4.36    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 31.94/4.36    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 31.94/4.36  fof(f47,plain,(
% 31.94/4.36    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 31.94/4.36    inference(resolution,[],[f39,f45])).
% 31.94/4.36  fof(f45,plain,(
% 31.94/4.36    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.94/4.36    inference(equality_resolution,[],[f35])).
% 31.94/4.36  fof(f35,plain,(
% 31.94/4.36    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 31.94/4.36    inference(cnf_transformation,[],[f1])).
% 31.94/4.36  fof(f1,axiom,(
% 31.94/4.36    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.94/4.36    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 31.94/4.36  fof(f39,plain,(
% 31.94/4.36    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 31.94/4.36    inference(cnf_transformation,[],[f20])).
% 31.94/4.36  fof(f20,plain,(
% 31.94/4.36    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 31.94/4.36    inference(ennf_transformation,[],[f2])).
% 31.94/4.36  fof(f2,axiom,(
% 31.94/4.36    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 31.94/4.36    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 31.94/4.36  fof(f16738,plain,(
% 31.94/4.36    ~r1_tarski(k6_subset_1(sK0,sK0),sK1) | r1_tarski(sK0,sK1)),
% 31.94/4.36    inference(superposition,[],[f258,f16056])).
% 31.94/4.36  fof(f16056,plain,(
% 31.94/4.36    k6_subset_1(sK0,sK1) = k6_subset_1(sK0,sK0)),
% 31.94/4.36    inference(backward_demodulation,[],[f12812,f16055])).
% 31.94/4.36  fof(f16055,plain,(
% 31.94/4.36    ( ! [X27] : (k6_subset_1(sK0,sK0) = k9_relat_1(sK2,k6_subset_1(X27,X27))) )),
% 31.94/4.36    inference(subsumption_resolution,[],[f16054,f25])).
% 31.94/4.36  fof(f25,plain,(
% 31.94/4.36    v1_relat_1(sK2)),
% 31.94/4.36    inference(cnf_transformation,[],[f14])).
% 31.94/4.36  fof(f16054,plain,(
% 31.94/4.36    ( ! [X27] : (k6_subset_1(sK0,sK0) = k9_relat_1(sK2,k6_subset_1(X27,X27)) | ~v1_relat_1(sK2)) )),
% 31.94/4.36    inference(subsumption_resolution,[],[f16053,f3939])).
% 31.94/4.36  fof(f3939,plain,(
% 31.94/4.36    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))) )),
% 31.94/4.36    inference(resolution,[],[f3011,f234])).
% 31.94/4.36  fof(f234,plain,(
% 31.94/4.36    ( ! [X6,X8,X7] : (r1_tarski(k6_subset_1(k6_subset_1(X6,X7),X8),X6)) )),
% 31.94/4.36    inference(resolution,[],[f111,f42])).
% 31.94/4.36  fof(f42,plain,(
% 31.94/4.36    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 31.94/4.36    inference(definition_unfolding,[],[f30,f31])).
% 31.94/4.36  fof(f30,plain,(
% 31.94/4.36    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 31.94/4.36    inference(cnf_transformation,[],[f4])).
% 31.94/4.36  fof(f4,axiom,(
% 31.94/4.36    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 31.94/4.36    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 31.94/4.36  fof(f111,plain,(
% 31.94/4.36    ( ! [X17,X15,X16] : (~r1_tarski(X15,k6_subset_1(X16,X17)) | r1_tarski(X15,X16)) )),
% 31.94/4.36    inference(resolution,[],[f48,f42])).
% 31.94/4.36  fof(f48,plain,(
% 31.94/4.36    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 31.94/4.36    inference(superposition,[],[f39,f32])).
% 31.94/4.37  fof(f32,plain,(
% 31.94/4.37    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 31.94/4.37    inference(cnf_transformation,[],[f15])).
% 31.94/4.37  fof(f15,plain,(
% 31.94/4.37    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 31.94/4.37    inference(ennf_transformation,[],[f3])).
% 31.94/4.37  fof(f3,axiom,(
% 31.94/4.37    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 31.94/4.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 31.94/4.37  fof(f3011,plain,(
% 31.94/4.37    ( ! [X58] : (~r1_tarski(k6_subset_1(X58,k2_relat_1(sK2)),sK0) | r1_tarski(X58,k2_relat_1(sK2))) )),
% 31.94/4.37    inference(resolution,[],[f258,f115])).
% 31.94/4.37  fof(f115,plain,(
% 31.94/4.37    ( ! [X25] : (r1_tarski(X25,k2_relat_1(sK2)) | ~r1_tarski(X25,sK0)) )),
% 31.94/4.37    inference(resolution,[],[f48,f28])).
% 31.94/4.37  fof(f28,plain,(
% 31.94/4.37    r1_tarski(sK0,k2_relat_1(sK2))),
% 31.94/4.37    inference(cnf_transformation,[],[f14])).
% 31.94/4.37  fof(f16053,plain,(
% 31.94/4.37    ( ! [X27] : (k6_subset_1(sK0,sK0) = k9_relat_1(sK2,k6_subset_1(X27,X27)) | ~r1_tarski(k6_subset_1(sK0,sK0),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 31.94/4.37    inference(subsumption_resolution,[],[f15802,f26])).
% 31.94/4.37  fof(f26,plain,(
% 31.94/4.37    v1_funct_1(sK2)),
% 31.94/4.37    inference(cnf_transformation,[],[f14])).
% 31.94/4.37  fof(f15802,plain,(
% 31.94/4.37    ( ! [X27] : (k6_subset_1(sK0,sK0) = k9_relat_1(sK2,k6_subset_1(X27,X27)) | ~v1_funct_1(sK2) | ~r1_tarski(k6_subset_1(sK0,sK0),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 31.94/4.37    inference(superposition,[],[f33,f4073])).
% 31.94/4.37  fof(f4073,plain,(
% 31.94/4.37    ( ! [X71] : (k10_relat_1(sK2,k6_subset_1(sK0,sK0)) = k6_subset_1(X71,X71)) )),
% 31.94/4.37    inference(resolution,[],[f94,f3257])).
% 31.94/4.37  fof(f3257,plain,(
% 31.94/4.37    ( ! [X34] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK0)),X34)) )),
% 31.94/4.37    inference(superposition,[],[f1840,f126])).
% 31.94/4.37  fof(f126,plain,(
% 31.94/4.37    ( ! [X4,X3] : (k6_subset_1(X3,X3) = k6_subset_1(k6_subset_1(X3,X3),X4)) )),
% 31.94/4.37    inference(resolution,[],[f50,f71])).
% 31.94/4.37  fof(f50,plain,(
% 31.94/4.37    ( ! [X2,X1] : (~r1_tarski(X1,k6_subset_1(X1,X2)) | k6_subset_1(X1,X2) = X1) )),
% 31.94/4.37    inference(resolution,[],[f36,f42])).
% 31.94/4.37  fof(f36,plain,(
% 31.94/4.37    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 31.94/4.37    inference(cnf_transformation,[],[f1])).
% 31.94/4.37  fof(f1840,plain,(
% 31.94/4.37    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,X0),sK1)),X1)) )),
% 31.94/4.37    inference(subsumption_resolution,[],[f1839,f25])).
% 31.94/4.37  fof(f1839,plain,(
% 31.94/4.37    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,X0),sK1)),X1) | ~v1_relat_1(sK2)) )),
% 31.94/4.37    inference(subsumption_resolution,[],[f1836,f26])).
% 31.94/4.37  fof(f1836,plain,(
% 31.94/4.37    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,X0),sK1)),X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 31.94/4.37    inference(superposition,[],[f1272,f40])).
% 31.94/4.37  fof(f40,plain,(
% 31.94/4.37    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 31.94/4.37    inference(cnf_transformation,[],[f22])).
% 31.94/4.37  fof(f22,plain,(
% 31.94/4.37    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 31.94/4.37    inference(flattening,[],[f21])).
% 31.94/4.37  fof(f21,plain,(
% 31.94/4.37    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 31.94/4.37    inference(ennf_transformation,[],[f9])).
% 31.94/4.37  fof(f9,axiom,(
% 31.94/4.37    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 31.94/4.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 31.94/4.37  fof(f1272,plain,(
% 31.94/4.37    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k10_relat_1(sK2,k6_subset_1(sK0,X0)),k10_relat_1(sK2,sK1)),X1)) )),
% 31.94/4.37    inference(subsumption_resolution,[],[f1271,f25])).
% 31.94/4.37  fof(f1271,plain,(
% 31.94/4.37    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k10_relat_1(sK2,k6_subset_1(sK0,X0)),k10_relat_1(sK2,sK1)),X1) | ~v1_relat_1(sK2)) )),
% 31.94/4.37    inference(subsumption_resolution,[],[f1267,f26])).
% 31.94/4.37  fof(f1267,plain,(
% 31.94/4.37    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k10_relat_1(sK2,k6_subset_1(sK0,X0)),k10_relat_1(sK2,sK1)),X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 31.94/4.37    inference(superposition,[],[f972,f40])).
% 31.94/4.37  fof(f972,plain,(
% 31.94/4.37    ( ! [X8,X7] : (r1_tarski(k6_subset_1(k6_subset_1(k10_relat_1(sK2,sK0),X7),k10_relat_1(sK2,sK1)),X8)) )),
% 31.94/4.37    inference(resolution,[],[f780,f43])).
% 31.94/4.37  fof(f780,plain,(
% 31.94/4.37    ( ! [X6,X5] : (r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),X5),k2_xboole_0(k10_relat_1(sK2,sK1),X6))) )),
% 31.94/4.37    inference(resolution,[],[f268,f43])).
% 31.94/4.37  fof(f268,plain,(
% 31.94/4.37    ( ! [X8,X9] : (r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(X8,k2_xboole_0(k10_relat_1(sK2,sK1),X9)))) )),
% 31.94/4.37    inference(resolution,[],[f259,f80])).
% 31.94/4.37  fof(f80,plain,(
% 31.94/4.37    ( ! [X6,X4,X5] : (r1_tarski(X4,k2_xboole_0(X5,k2_xboole_0(X4,X6)))) )),
% 31.94/4.37    inference(resolution,[],[f65,f39])).
% 31.94/4.37  fof(f65,plain,(
% 31.94/4.37    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 31.94/4.37    inference(resolution,[],[f44,f42])).
% 31.94/4.37  fof(f44,plain,(
% 31.94/4.37    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 31.94/4.37    inference(definition_unfolding,[],[f38,f31])).
% 31.94/4.37  fof(f38,plain,(
% 31.94/4.37    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 31.94/4.37    inference(cnf_transformation,[],[f19])).
% 31.94/4.37  fof(f19,plain,(
% 31.94/4.37    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 31.94/4.37    inference(ennf_transformation,[],[f6])).
% 31.94/4.37  fof(f6,axiom,(
% 31.94/4.37    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 31.94/4.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 31.94/4.37  fof(f259,plain,(
% 31.94/4.37    ( ! [X46] : (~r1_tarski(k10_relat_1(sK2,sK1),X46) | r1_tarski(k10_relat_1(sK2,sK0),X46)) )),
% 31.94/4.37    inference(superposition,[],[f163,f161])).
% 31.94/4.37  fof(f161,plain,(
% 31.94/4.37    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0)) )),
% 31.94/4.37    inference(subsumption_resolution,[],[f150,f45])).
% 31.94/4.37  fof(f150,plain,(
% 31.94/4.37    ( ! [X0,X1] : (~r1_tarski(X0,X0) | ~r1_tarski(X1,X0) | k2_xboole_0(X0,X1) = X0) )),
% 31.94/4.37    inference(resolution,[],[f68,f47])).
% 31.94/4.37  fof(f68,plain,(
% 31.94/4.37    ( ! [X4,X5,X3] : (~r1_tarski(X4,k2_xboole_0(X5,X3)) | ~r1_tarski(X5,X4) | ~r1_tarski(X3,X4) | k2_xboole_0(X5,X3) = X4) )),
% 31.94/4.37    inference(resolution,[],[f41,f36])).
% 31.94/4.37  fof(f41,plain,(
% 31.94/4.37    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 31.94/4.37    inference(cnf_transformation,[],[f24])).
% 31.94/4.37  fof(f24,plain,(
% 31.94/4.37    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 31.94/4.37    inference(flattening,[],[f23])).
% 31.94/4.37  fof(f23,plain,(
% 31.94/4.37    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 31.94/4.37    inference(ennf_transformation,[],[f7])).
% 31.94/4.37  fof(f7,axiom,(
% 31.94/4.37    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 31.94/4.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 31.94/4.37  fof(f163,plain,(
% 31.94/4.37    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(X0,k10_relat_1(sK2,sK1)))) )),
% 31.94/4.37    inference(resolution,[],[f142,f44])).
% 31.94/4.37  fof(f142,plain,(
% 31.94/4.37    ( ! [X2] : (r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),X2),k10_relat_1(sK2,sK1))) )),
% 31.94/4.37    inference(resolution,[],[f114,f42])).
% 31.94/4.37  fof(f114,plain,(
% 31.94/4.37    ( ! [X24] : (~r1_tarski(X24,k10_relat_1(sK2,sK0)) | r1_tarski(X24,k10_relat_1(sK2,sK1))) )),
% 31.94/4.37    inference(resolution,[],[f48,f27])).
% 31.94/4.37  fof(f27,plain,(
% 31.94/4.37    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 31.94/4.37    inference(cnf_transformation,[],[f14])).
% 31.94/4.37  fof(f94,plain,(
% 31.94/4.37    ( ! [X2,X3] : (~r1_tarski(X2,k6_subset_1(X3,X3)) | k6_subset_1(X3,X3) = X2) )),
% 31.94/4.37    inference(resolution,[],[f71,f36])).
% 31.94/4.37  fof(f33,plain,(
% 31.94/4.37    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 31.94/4.37    inference(cnf_transformation,[],[f17])).
% 31.94/4.37  fof(f17,plain,(
% 31.94/4.37    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 31.94/4.37    inference(flattening,[],[f16])).
% 31.94/4.37  fof(f16,plain,(
% 31.94/4.37    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 31.94/4.37    inference(ennf_transformation,[],[f10])).
% 31.94/4.37  fof(f10,axiom,(
% 31.94/4.37    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 31.94/4.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 31.94/4.37  fof(f12812,plain,(
% 31.94/4.37    ( ! [X22] : (k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k6_subset_1(X22,X22))) )),
% 31.94/4.37    inference(subsumption_resolution,[],[f12811,f25])).
% 31.94/4.37  fof(f12811,plain,(
% 31.94/4.37    ( ! [X22] : (k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k6_subset_1(X22,X22)) | ~v1_relat_1(sK2)) )),
% 31.94/4.37    inference(subsumption_resolution,[],[f12810,f3939])).
% 31.94/4.37  fof(f12810,plain,(
% 31.94/4.37    ( ! [X22] : (k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k6_subset_1(X22,X22)) | ~r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 31.94/4.37    inference(subsumption_resolution,[],[f12592,f26])).
% 31.94/4.37  fof(f12592,plain,(
% 31.94/4.37    ( ! [X22] : (k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k6_subset_1(X22,X22)) | ~v1_funct_1(sK2) | ~r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 31.94/4.37    inference(superposition,[],[f33,f4072])).
% 31.94/4.37  fof(f4072,plain,(
% 31.94/4.37    ( ! [X70] : (k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k6_subset_1(X70,X70)) )),
% 31.94/4.37    inference(resolution,[],[f94,f330])).
% 31.94/4.37  fof(f330,plain,(
% 31.94/4.37    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X0)) )),
% 31.94/4.37    inference(subsumption_resolution,[],[f329,f25])).
% 31.94/4.37  fof(f329,plain,(
% 31.94/4.37    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X0) | ~v1_relat_1(sK2)) )),
% 31.94/4.37    inference(subsumption_resolution,[],[f327,f26])).
% 31.94/4.37  fof(f327,plain,(
% 31.94/4.37    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 31.94/4.37    inference(superposition,[],[f289,f40])).
% 31.94/4.37  fof(f289,plain,(
% 31.94/4.37    ( ! [X1] : (r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),X1)) )),
% 31.94/4.37    inference(resolution,[],[f264,f43])).
% 31.94/4.37  fof(f264,plain,(
% 31.94/4.37    ( ! [X2] : (r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X2))) )),
% 31.94/4.37    inference(resolution,[],[f259,f47])).
% 31.94/4.37  fof(f258,plain,(
% 31.94/4.37    ( ! [X45,X44] : (~r1_tarski(k6_subset_1(X45,X44),X44) | r1_tarski(X45,X44)) )),
% 31.94/4.37    inference(superposition,[],[f66,f161])).
% 31.94/4.37  fof(f66,plain,(
% 31.94/4.37    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,k6_subset_1(X2,X3)))) )),
% 31.94/4.37    inference(resolution,[],[f44,f45])).
% 31.94/4.37  % SZS output end Proof for theBenchmark
% 31.94/4.37  % (18552)------------------------------
% 31.94/4.37  % (18552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.94/4.37  % (18552)Termination reason: Refutation
% 31.94/4.37  
% 31.94/4.37  % (18552)Memory used [KB]: 17782
% 31.94/4.37  % (18552)Time elapsed: 3.532 s
% 31.94/4.37  % (18552)------------------------------
% 31.94/4.37  % (18552)------------------------------
% 31.94/4.37  % (18429)Success in time 4.008 s
%------------------------------------------------------------------------------
