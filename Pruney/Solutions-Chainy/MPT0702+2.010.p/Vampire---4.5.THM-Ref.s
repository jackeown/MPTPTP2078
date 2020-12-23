%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:13 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 342 expanded)
%              Number of leaves         :   12 (  83 expanded)
%              Depth                    :   17
%              Number of atoms          :  216 (1731 expanded)
%              Number of equality atoms :   51 (  84 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1558,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1536,f50])).

fof(f50,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(f1536,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f78,f1518])).

fof(f1518,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1516,f399])).

fof(f399,plain,(
    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f127,f48])).

fof(f48,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f127,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK2))
      | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1 ) ),
    inference(forward_demodulation,[],[f126,f119])).

fof(f119,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) ),
    inference(subsumption_resolution,[],[f118,f45])).

fof(f45,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f117,f46])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f117,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f63,f49])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f126,plain,(
    ! [X1] :
      ( k10_relat_1(sK2,k10_relat_1(k2_funct_1(sK2),X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f125,f115])).

fof(f115,plain,(
    ! [X0] : k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f114,plain,(
    ! [X0] :
      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f113,f46])).

fof(f113,plain,(
    ! [X0] :
      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f62,f49])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f125,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK2))
      | k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),X1)) = X1 ) ),
    inference(forward_demodulation,[],[f124,f108])).

fof(f108,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f107,f45])).

fof(f107,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f106,f46])).

fof(f106,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f55,f49])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f124,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k2_relat_1(k2_funct_1(sK2)))
      | k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f122,f75])).

fof(f75,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f74,f45])).

fof(f74,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f52,f46])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f122,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k2_relat_1(k2_funct_1(sK2)))
      | k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),X1)) = X1
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f64,f77])).

fof(f77,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f76,f45])).

fof(f76,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f53,f46])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1516,plain,(
    k3_xboole_0(sK0,sK1) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f393,f168])).

fof(f168,plain,(
    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f130,f82])).

fof(f82,plain,(
    k9_relat_1(sK2,sK0) = k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f130,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f129,f45])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f128,f46])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f70,f49])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

fof(f393,plain,(
    ! [X0] : k3_xboole_0(sK0,X0) = k10_relat_1(sK2,k9_relat_1(sK2,k3_xboole_0(sK0,X0))) ),
    inference(resolution,[],[f127,f87])).

fof(f87,plain,(
    ! [X6] : r1_tarski(k3_xboole_0(sK0,X6),k1_relat_1(sK2)) ),
    inference(resolution,[],[f69,f48])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f56,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.08/0.27  % Computer   : n011.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 14:54:27 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.13/0.40  % (10701)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.13/0.40  % (10707)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.13/0.40  % (10699)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.13/0.42  % (10693)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.13/0.43  % (10704)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.13/0.43  % (10700)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.13/0.44  % (10703)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.13/0.44  % (10697)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.13/0.45  % (10696)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.13/0.46  % (10695)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.13/0.46  % (10692)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.13/0.46  % (10717)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.13/0.46  % (10702)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.13/0.47  % (10712)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.13/0.47  % (10710)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.13/0.47  % (10711)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.13/0.47  % (10715)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.13/0.48  % (10709)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.13/0.48  % (10718)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.13/0.48  % (10720)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.13/0.48  % (10705)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.13/0.48  % (10714)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.13/0.48  % (10694)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.13/0.49  % (10699)Refutation found. Thanks to Tanya!
% 0.13/0.49  % SZS status Theorem for theBenchmark
% 0.13/0.49  % SZS output start Proof for theBenchmark
% 0.13/0.49  fof(f1558,plain,(
% 0.13/0.49    $false),
% 0.13/0.49    inference(subsumption_resolution,[],[f1536,f50])).
% 0.13/0.49  fof(f50,plain,(
% 0.13/0.49    ~r1_tarski(sK0,sK1)),
% 0.13/0.49    inference(cnf_transformation,[],[f42])).
% 0.13/0.49  fof(f42,plain,(
% 0.13/0.49    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.13/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f41])).
% 0.13/0.49  fof(f41,plain,(
% 0.13/0.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.13/0.49    introduced(choice_axiom,[])).
% 0.13/0.49  fof(f21,plain,(
% 0.13/0.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.13/0.49    inference(flattening,[],[f20])).
% 0.13/0.49  fof(f20,plain,(
% 0.13/0.49    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.13/0.49    inference(ennf_transformation,[],[f19])).
% 0.13/0.49  fof(f19,negated_conjecture,(
% 0.13/0.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.13/0.49    inference(negated_conjecture,[],[f18])).
% 0.13/0.49  fof(f18,conjecture,(
% 0.13/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.13/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 0.13/0.49  fof(f1536,plain,(
% 0.13/0.49    r1_tarski(sK0,sK1)),
% 0.13/0.49    inference(superposition,[],[f78,f1518])).
% 0.13/0.49  fof(f1518,plain,(
% 0.13/0.49    sK0 = k3_xboole_0(sK0,sK1)),
% 0.13/0.49    inference(forward_demodulation,[],[f1516,f399])).
% 0.13/0.49  fof(f399,plain,(
% 0.13/0.49    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 0.13/0.49    inference(resolution,[],[f127,f48])).
% 0.13/0.49  fof(f48,plain,(
% 0.13/0.49    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.13/0.49    inference(cnf_transformation,[],[f42])).
% 0.13/0.49  fof(f127,plain,(
% 0.13/0.49    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK2)) | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1) )),
% 0.13/0.49    inference(forward_demodulation,[],[f126,f119])).
% 0.13/0.49  fof(f119,plain,(
% 0.13/0.49    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)) )),
% 0.13/0.49    inference(subsumption_resolution,[],[f118,f45])).
% 0.13/0.49  fof(f45,plain,(
% 0.13/0.49    v1_relat_1(sK2)),
% 0.13/0.49    inference(cnf_transformation,[],[f42])).
% 0.13/0.49  fof(f118,plain,(
% 0.13/0.49    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.13/0.49    inference(subsumption_resolution,[],[f117,f46])).
% 0.13/0.49  fof(f46,plain,(
% 0.13/0.49    v1_funct_1(sK2)),
% 0.13/0.49    inference(cnf_transformation,[],[f42])).
% 0.13/0.49  fof(f117,plain,(
% 0.13/0.49    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.13/0.49    inference(resolution,[],[f63,f49])).
% 0.13/0.49  fof(f49,plain,(
% 0.13/0.49    v2_funct_1(sK2)),
% 0.13/0.49    inference(cnf_transformation,[],[f42])).
% 0.13/0.49  fof(f63,plain,(
% 0.13/0.49    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.13/0.49    inference(cnf_transformation,[],[f33])).
% 0.13/0.49  fof(f33,plain,(
% 0.13/0.49    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.13/0.49    inference(flattening,[],[f32])).
% 0.13/0.49  fof(f32,plain,(
% 0.13/0.49    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.13/0.49    inference(ennf_transformation,[],[f15])).
% 0.13/0.49  fof(f15,axiom,(
% 0.13/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.13/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 0.13/0.49  fof(f126,plain,(
% 0.13/0.49    ( ! [X1] : (k10_relat_1(sK2,k10_relat_1(k2_funct_1(sK2),X1)) = X1 | ~r1_tarski(X1,k1_relat_1(sK2))) )),
% 0.13/0.49    inference(forward_demodulation,[],[f125,f115])).
% 0.13/0.49  fof(f115,plain,(
% 0.13/0.49    ( ! [X0] : (k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)) )),
% 0.13/0.49    inference(subsumption_resolution,[],[f114,f45])).
% 0.13/0.49  fof(f114,plain,(
% 0.13/0.49    ( ! [X0] : (k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) | ~v1_relat_1(sK2)) )),
% 0.13/0.49    inference(subsumption_resolution,[],[f113,f46])).
% 0.13/0.49  fof(f113,plain,(
% 0.13/0.49    ( ! [X0] : (k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.13/0.49    inference(resolution,[],[f62,f49])).
% 0.13/0.49  fof(f62,plain,(
% 0.13/0.49    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.13/0.49    inference(cnf_transformation,[],[f31])).
% 0.13/0.49  fof(f31,plain,(
% 0.13/0.49    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.13/0.49    inference(flattening,[],[f30])).
% 0.13/0.49  fof(f30,plain,(
% 0.13/0.49    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.13/0.49    inference(ennf_transformation,[],[f16])).
% 0.13/0.49  fof(f16,axiom,(
% 0.13/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.13/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).
% 0.13/0.49  fof(f125,plain,(
% 0.13/0.49    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK2)) | k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),X1)) = X1) )),
% 0.13/0.49    inference(forward_demodulation,[],[f124,f108])).
% 0.13/0.49  fof(f108,plain,(
% 0.13/0.49    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.13/0.49    inference(subsumption_resolution,[],[f107,f45])).
% 0.13/0.49  fof(f107,plain,(
% 0.13/0.49    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.13/0.49    inference(subsumption_resolution,[],[f106,f46])).
% 0.13/0.49  fof(f106,plain,(
% 0.13/0.49    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.13/0.49    inference(resolution,[],[f55,f49])).
% 0.13/0.49  fof(f55,plain,(
% 0.13/0.49    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.13/0.49    inference(cnf_transformation,[],[f26])).
% 0.13/0.49  fof(f26,plain,(
% 0.13/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.13/0.49    inference(flattening,[],[f25])).
% 0.13/0.49  fof(f25,plain,(
% 0.13/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.13/0.49    inference(ennf_transformation,[],[f17])).
% 0.13/0.49  fof(f17,axiom,(
% 0.13/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.13/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.13/0.49  fof(f124,plain,(
% 0.13/0.49    ( ! [X1] : (~r1_tarski(X1,k2_relat_1(k2_funct_1(sK2))) | k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),X1)) = X1) )),
% 0.13/0.49    inference(subsumption_resolution,[],[f122,f75])).
% 0.13/0.49  fof(f75,plain,(
% 0.13/0.49    v1_relat_1(k2_funct_1(sK2))),
% 0.13/0.49    inference(subsumption_resolution,[],[f74,f45])).
% 0.13/0.49  fof(f74,plain,(
% 0.13/0.49    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.13/0.49    inference(resolution,[],[f52,f46])).
% 0.13/0.49  fof(f52,plain,(
% 0.13/0.49    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.13/0.49    inference(cnf_transformation,[],[f24])).
% 0.13/0.49  fof(f24,plain,(
% 0.13/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.13/0.49    inference(flattening,[],[f23])).
% 0.13/0.49  fof(f23,plain,(
% 0.13/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.13/0.49    inference(ennf_transformation,[],[f11])).
% 0.13/0.49  fof(f11,axiom,(
% 0.13/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.13/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.13/0.49  fof(f122,plain,(
% 0.13/0.49    ( ! [X1] : (~r1_tarski(X1,k2_relat_1(k2_funct_1(sK2))) | k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),X1)) = X1 | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.13/0.49    inference(resolution,[],[f64,f77])).
% 0.13/0.49  fof(f77,plain,(
% 0.13/0.49    v1_funct_1(k2_funct_1(sK2))),
% 0.13/0.49    inference(subsumption_resolution,[],[f76,f45])).
% 0.13/0.49  fof(f76,plain,(
% 0.13/0.49    v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.13/0.49    inference(resolution,[],[f53,f46])).
% 0.13/0.49  fof(f53,plain,(
% 0.13/0.49    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.13/0.49    inference(cnf_transformation,[],[f24])).
% 0.13/0.49  fof(f64,plain,(
% 0.13/0.49    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.13/0.49    inference(cnf_transformation,[],[f35])).
% 0.13/0.49  fof(f35,plain,(
% 0.13/0.49    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.13/0.49    inference(flattening,[],[f34])).
% 0.13/0.49  fof(f34,plain,(
% 0.13/0.49    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.13/0.49    inference(ennf_transformation,[],[f14])).
% 0.13/0.49  fof(f14,axiom,(
% 0.13/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.13/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.13/0.49  fof(f1516,plain,(
% 0.13/0.49    k3_xboole_0(sK0,sK1) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 0.13/0.49    inference(superposition,[],[f393,f168])).
% 0.13/0.49  fof(f168,plain,(
% 0.13/0.49    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 0.13/0.49    inference(superposition,[],[f130,f82])).
% 0.13/0.49  fof(f82,plain,(
% 0.13/0.49    k9_relat_1(sK2,sK0) = k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.13/0.49    inference(resolution,[],[f61,f47])).
% 0.13/0.49  fof(f47,plain,(
% 0.13/0.49    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.13/0.49    inference(cnf_transformation,[],[f42])).
% 0.13/0.49  fof(f61,plain,(
% 0.13/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.13/0.49    inference(cnf_transformation,[],[f29])).
% 0.13/0.49  fof(f29,plain,(
% 0.13/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.13/0.49    inference(ennf_transformation,[],[f6])).
% 0.13/0.49  fof(f6,axiom,(
% 0.13/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.13/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.13/0.49  fof(f130,plain,(
% 0.13/0.49    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.13/0.49    inference(subsumption_resolution,[],[f129,f45])).
% 0.13/0.49  fof(f129,plain,(
% 0.13/0.49    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 0.13/0.49    inference(subsumption_resolution,[],[f128,f46])).
% 0.13/0.49  fof(f128,plain,(
% 0.13/0.49    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.13/0.49    inference(resolution,[],[f70,f49])).
% 0.13/0.49  fof(f70,plain,(
% 0.13/0.49    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.13/0.49    inference(cnf_transformation,[],[f38])).
% 0.13/0.49  fof(f38,plain,(
% 0.13/0.49    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.13/0.49    inference(flattening,[],[f37])).
% 0.13/0.49  fof(f37,plain,(
% 0.13/0.49    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.13/0.49    inference(ennf_transformation,[],[f12])).
% 0.13/0.49  fof(f12,axiom,(
% 0.13/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.13/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).
% 0.13/0.49  fof(f393,plain,(
% 0.13/0.49    ( ! [X0] : (k3_xboole_0(sK0,X0) = k10_relat_1(sK2,k9_relat_1(sK2,k3_xboole_0(sK0,X0)))) )),
% 0.13/0.49    inference(resolution,[],[f127,f87])).
% 0.13/0.49  fof(f87,plain,(
% 0.13/0.49    ( ! [X6] : (r1_tarski(k3_xboole_0(sK0,X6),k1_relat_1(sK2))) )),
% 0.13/0.49    inference(resolution,[],[f69,f48])).
% 0.13/0.49  fof(f69,plain,(
% 0.13/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1)) )),
% 0.13/0.49    inference(cnf_transformation,[],[f36])).
% 0.13/0.49  fof(f36,plain,(
% 0.13/0.49    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.13/0.49    inference(ennf_transformation,[],[f3])).
% 0.13/0.49  fof(f3,axiom,(
% 0.13/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.13/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.13/0.49  fof(f78,plain,(
% 0.13/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.13/0.49    inference(superposition,[],[f56,f57])).
% 0.13/0.49  fof(f57,plain,(
% 0.13/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.13/0.49    inference(cnf_transformation,[],[f1])).
% 0.13/0.49  fof(f1,axiom,(
% 0.13/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.13/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.13/0.49  fof(f56,plain,(
% 0.13/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.13/0.49    inference(cnf_transformation,[],[f4])).
% 0.13/0.49  fof(f4,axiom,(
% 0.13/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.13/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.13/0.49  % SZS output end Proof for theBenchmark
% 0.13/0.49  % (10699)------------------------------
% 0.13/0.49  % (10699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.49  % (10699)Termination reason: Refutation
% 0.13/0.49  
% 0.13/0.49  % (10699)Memory used [KB]: 2942
% 0.13/0.49  % (10699)Time elapsed: 0.152 s
% 0.13/0.49  % (10699)------------------------------
% 0.13/0.49  % (10699)------------------------------
% 0.13/0.49  % (10691)Success in time 0.212 s
%------------------------------------------------------------------------------
