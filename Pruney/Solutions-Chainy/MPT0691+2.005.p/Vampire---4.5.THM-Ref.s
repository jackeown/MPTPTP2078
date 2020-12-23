%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:45 EST 2020

% Result     : Theorem 37.67s
% Output     : Refutation 37.67s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 441 expanded)
%              Number of leaves         :   18 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          :  163 (1062 expanded)
%              Number of equality atoms :   48 ( 155 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69232,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f61,f69050])).

fof(f69050,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f69049,f11909])).

fof(f11909,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f11907,f8613])).

fof(f8613,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f70,f8552,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f8552,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f3035,f316])).

fof(f316,plain,(
    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f315,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f315,plain,(
    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f58,f262])).

fof(f262,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f39,f163,f54])).

fof(f163,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,k1_relat_1(sK1)),X0) ),
    inference(unit_resulting_resolution,[],[f72,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f72,plain,(
    ! [X0] : r1_tarski(sK0,k2_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f44,f37,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f37,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f3035,plain,(
    ! [X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X1))) ),
    inference(superposition,[],[f87,f213])).

fof(f213,plain,(
    ! [X0] : k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) ),
    inference(global_subsumption,[],[f36,f211])).

fof(f211,plain,(
    ! [X0] :
      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f59,f62])).

fof(f62,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f36,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f55,f47])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f68,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f68,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f36,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f70,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f36,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f11907,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f79,f8656])).

fof(f8656,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f8638,f67])).

fof(f67,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0) ),
    inference(unit_resulting_resolution,[],[f60,f36,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8638,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(superposition,[],[f80,f8613])).

fof(f80,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f68,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f79,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f68,f41])).

fof(f69049,plain,(
    ~ r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f68658,f472])).

fof(f472,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(k10_relat_1(sK1,X1),X0)) ),
    inference(superposition,[],[f71,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f71,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) ),
    inference(unit_resulting_resolution,[],[f36,f59])).

fof(f68658,plain,(
    ~ r1_tarski(sK0,k1_setfam_1(k2_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0))) ),
    inference(unit_resulting_resolution,[],[f38,f68268,f57])).

fof(f68268,plain,(
    ! [X6] : r1_tarski(k1_setfam_1(k2_tarski(X6,sK0)),X6) ),
    inference(superposition,[],[f67727,f8613])).

fof(f67727,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k2_tarski(X3,k1_relat_1(k7_relat_1(sK1,X2)))),X3) ),
    inference(superposition,[],[f24799,f4076])).

fof(f4076,plain,(
    ! [X4,X3] : k10_relat_1(k7_relat_1(k7_relat_1(sK1,X3),X4),k2_relat_1(k7_relat_1(sK1,X3))) = k1_setfam_1(k2_tarski(X4,k1_relat_1(k7_relat_1(sK1,X3)))) ),
    inference(global_subsumption,[],[f68,f4073])).

fof(f4073,plain,(
    ! [X4,X3] :
      ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X3),X4),k2_relat_1(k7_relat_1(sK1,X3))) = k1_setfam_1(k2_tarski(X4,k1_relat_1(k7_relat_1(sK1,X3))))
      | ~ v1_relat_1(k7_relat_1(sK1,X3)) ) ),
    inference(superposition,[],[f59,f79])).

fof(f24799,plain,(
    ! [X2,X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2),X1) ),
    inference(unit_resulting_resolution,[],[f88,f188,f57])).

fof(f188,plain,(
    ! [X2,X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2),k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1))) ),
    inference(unit_resulting_resolution,[],[f86,f50])).

fof(f86,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)) ),
    inference(unit_resulting_resolution,[],[f68,f49])).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)),X1) ),
    inference(unit_resulting_resolution,[],[f68,f51])).

fof(f38,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (23626)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (23649)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (23629)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (23631)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (23630)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (23628)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (23627)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (23633)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (23644)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (23648)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (23647)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (23639)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (23638)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (23640)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (23636)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (23637)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (23645)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (23651)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (23646)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (23652)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (23632)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (23650)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (23654)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (23641)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (23655)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (23643)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (23653)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (23642)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (23635)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (23634)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 2.04/0.68  % (23629)Refutation not found, incomplete strategy% (23629)------------------------------
% 2.04/0.68  % (23629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.68  % (23629)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.68  
% 2.04/0.68  % (23629)Memory used [KB]: 6140
% 2.04/0.68  % (23629)Time elapsed: 0.252 s
% 2.04/0.68  % (23629)------------------------------
% 2.04/0.68  % (23629)------------------------------
% 2.77/0.78  % (23656)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.33/0.81  % (23628)Time limit reached!
% 3.33/0.81  % (23628)------------------------------
% 3.33/0.81  % (23628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.81  % (23628)Termination reason: Time limit
% 3.33/0.81  
% 3.33/0.81  % (23628)Memory used [KB]: 7419
% 3.33/0.81  % (23628)Time elapsed: 0.410 s
% 3.33/0.81  % (23628)------------------------------
% 3.33/0.81  % (23628)------------------------------
% 3.33/0.83  % (23650)Time limit reached!
% 3.33/0.83  % (23650)------------------------------
% 3.33/0.83  % (23650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.83  % (23650)Termination reason: Time limit
% 3.33/0.83  
% 3.33/0.83  % (23650)Memory used [KB]: 13304
% 3.33/0.83  % (23650)Time elapsed: 0.430 s
% 3.33/0.83  % (23650)------------------------------
% 3.33/0.83  % (23650)------------------------------
% 4.31/0.93  % (23632)Time limit reached!
% 4.31/0.93  % (23632)------------------------------
% 4.31/0.93  % (23632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.93  % (23632)Termination reason: Time limit
% 4.31/0.93  % (23632)Termination phase: Saturation
% 4.31/0.93  
% 4.31/0.93  % (23632)Memory used [KB]: 15351
% 4.31/0.93  % (23632)Time elapsed: 0.500 s
% 4.31/0.93  % (23632)------------------------------
% 4.31/0.93  % (23632)------------------------------
% 4.31/0.94  % (23655)Time limit reached!
% 4.31/0.94  % (23655)------------------------------
% 4.31/0.94  % (23655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.94  % (23655)Termination reason: Time limit
% 4.31/0.94  % (23655)Termination phase: Saturation
% 4.31/0.94  
% 4.31/0.94  % (23655)Memory used [KB]: 2174
% 4.31/0.94  % (23655)Time elapsed: 0.500 s
% 4.31/0.94  % (23655)------------------------------
% 4.31/0.94  % (23655)------------------------------
% 4.31/0.95  % (23640)Time limit reached!
% 4.31/0.95  % (23640)------------------------------
% 4.31/0.95  % (23640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.95  % (23640)Termination reason: Time limit
% 4.31/0.95  % (23640)Termination phase: Saturation
% 4.31/0.95  
% 4.31/0.95  % (23640)Memory used [KB]: 5884
% 4.31/0.95  % (23640)Time elapsed: 0.500 s
% 4.31/0.95  % (23640)------------------------------
% 4.31/0.95  % (23640)------------------------------
% 4.31/0.97  % (23657)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.31/0.98  % (23658)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.31/0.98  % (23658)Refutation not found, incomplete strategy% (23658)------------------------------
% 4.31/0.98  % (23658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.98  % (23658)Termination reason: Refutation not found, incomplete strategy
% 4.31/0.98  
% 4.31/0.98  % (23658)Memory used [KB]: 6268
% 4.31/0.98  % (23658)Time elapsed: 0.107 s
% 4.31/0.98  % (23658)------------------------------
% 4.31/0.98  % (23658)------------------------------
% 5.01/1.05  % (23659)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.01/1.05  % (23633)Time limit reached!
% 5.01/1.05  % (23633)------------------------------
% 5.01/1.05  % (23633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.05  % (23633)Termination reason: Time limit
% 5.01/1.05  
% 5.01/1.05  % (23633)Memory used [KB]: 8827
% 5.01/1.05  % (23633)Time elapsed: 0.630 s
% 5.01/1.05  % (23633)------------------------------
% 5.01/1.05  % (23633)------------------------------
% 5.01/1.05  % (23660)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.01/1.07  % (23661)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.43/1.10  % (23662)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.43/1.18  % (23663)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.71/1.22  % (23627)Time limit reached!
% 6.71/1.22  % (23627)------------------------------
% 6.71/1.22  % (23627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.71/1.22  % (23627)Termination reason: Time limit
% 6.71/1.22  % (23627)Termination phase: Saturation
% 6.71/1.22  
% 6.71/1.22  % (23627)Memory used [KB]: 7547
% 6.71/1.22  % (23627)Time elapsed: 0.800 s
% 6.71/1.22  % (23627)------------------------------
% 6.71/1.22  % (23627)------------------------------
% 7.48/1.31  % (23664)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 8.01/1.41  % (23638)Time limit reached!
% 8.01/1.41  % (23638)------------------------------
% 8.01/1.41  % (23638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.01/1.41  % (23638)Termination reason: Time limit
% 8.01/1.41  
% 8.01/1.41  % (23638)Memory used [KB]: 14583
% 8.01/1.41  % (23638)Time elapsed: 1.015 s
% 8.01/1.41  % (23638)------------------------------
% 8.01/1.41  % (23638)------------------------------
% 8.01/1.44  % (23653)Time limit reached!
% 8.01/1.44  % (23653)------------------------------
% 8.01/1.44  % (23653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.01/1.45  % (23653)Termination reason: Time limit
% 8.01/1.45  
% 8.01/1.45  % (23653)Memory used [KB]: 9594
% 8.01/1.45  % (23653)Time elapsed: 1.044 s
% 8.01/1.45  % (23653)------------------------------
% 8.01/1.45  % (23653)------------------------------
% 9.09/1.55  % (23665)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 9.09/1.58  % (23666)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.68/1.61  % (23626)Time limit reached!
% 9.68/1.61  % (23626)------------------------------
% 9.68/1.61  % (23626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.68/1.63  % (23626)Termination reason: Time limit
% 9.68/1.63  
% 9.68/1.63  % (23626)Memory used [KB]: 13048
% 9.68/1.63  % (23626)Time elapsed: 1.206 s
% 9.68/1.63  % (23626)------------------------------
% 9.68/1.63  % (23626)------------------------------
% 9.68/1.65  % (23662)Time limit reached!
% 9.68/1.65  % (23662)------------------------------
% 9.68/1.65  % (23662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.68/1.65  % (23662)Termination reason: Time limit
% 9.68/1.65  
% 9.68/1.65  % (23662)Memory used [KB]: 17782
% 9.68/1.65  % (23662)Time elapsed: 0.625 s
% 9.68/1.65  % (23662)------------------------------
% 9.68/1.65  % (23662)------------------------------
% 10.51/1.72  % (23631)Time limit reached!
% 10.51/1.72  % (23631)------------------------------
% 10.51/1.72  % (23631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.51/1.72  % (23631)Termination reason: Time limit
% 10.51/1.72  % (23631)Termination phase: Saturation
% 10.51/1.72  
% 10.51/1.72  % (23631)Memory used [KB]: 8827
% 10.51/1.72  % (23631)Time elapsed: 1.300 s
% 10.51/1.72  % (23631)------------------------------
% 10.51/1.72  % (23631)------------------------------
% 10.51/1.74  % (23642)Time limit reached!
% 10.51/1.74  % (23642)------------------------------
% 10.51/1.74  % (23642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.51/1.74  % (23642)Termination reason: Time limit
% 10.51/1.74  % (23642)Termination phase: Saturation
% 10.51/1.74  
% 10.51/1.74  % (23642)Memory used [KB]: 11769
% 10.51/1.74  % (23642)Time elapsed: 1.300 s
% 10.51/1.74  % (23642)------------------------------
% 10.51/1.74  % (23642)------------------------------
% 10.51/1.77  % (23667)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 11.24/1.78  % (23668)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 11.49/1.82  % (23669)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 11.49/1.89  % (23670)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 12.67/2.02  % (23652)Time limit reached!
% 12.67/2.02  % (23652)------------------------------
% 12.67/2.02  % (23652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.67/2.02  % (23652)Termination reason: Time limit
% 12.67/2.02  
% 12.67/2.02  % (23652)Memory used [KB]: 20724
% 12.67/2.02  % (23652)Time elapsed: 1.615 s
% 12.67/2.02  % (23652)------------------------------
% 12.67/2.02  % (23652)------------------------------
% 13.60/2.14  % (23671)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 14.59/2.21  % (23669)Time limit reached!
% 14.59/2.21  % (23669)------------------------------
% 14.59/2.21  % (23669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.59/2.21  % (23669)Termination reason: Time limit
% 14.59/2.21  % (23669)Termination phase: Saturation
% 14.59/2.21  
% 14.59/2.21  % (23669)Memory used [KB]: 21108
% 14.59/2.21  % (23669)Time elapsed: 0.400 s
% 14.59/2.21  % (23669)------------------------------
% 14.59/2.21  % (23669)------------------------------
% 14.59/2.23  % (23665)Time limit reached!
% 14.59/2.23  % (23665)------------------------------
% 14.59/2.23  % (23665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.59/2.23  % (23665)Termination reason: Time limit
% 14.59/2.23  
% 14.59/2.23  % (23665)Memory used [KB]: 14839
% 14.59/2.23  % (23665)Time elapsed: 0.803 s
% 14.59/2.23  % (23665)------------------------------
% 14.59/2.23  % (23665)------------------------------
% 14.59/2.28  % (23646)Time limit reached!
% 14.59/2.28  % (23646)------------------------------
% 14.59/2.28  % (23646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.59/2.28  % (23646)Termination reason: Time limit
% 14.59/2.28  
% 14.59/2.28  % (23646)Memory used [KB]: 23922
% 14.59/2.28  % (23646)Time elapsed: 1.849 s
% 14.59/2.28  % (23646)------------------------------
% 14.59/2.28  % (23646)------------------------------
% 15.27/2.33  % (23672)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 15.27/2.36  % (23673)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 16.09/2.42  % (23674)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 16.09/2.49  % (23671)Time limit reached!
% 16.09/2.49  % (23671)------------------------------
% 16.09/2.49  % (23671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.09/2.49  % (23671)Termination reason: Time limit
% 16.09/2.49  
% 16.09/2.49  % (23671)Memory used [KB]: 9338
% 16.09/2.49  % (23671)Time elapsed: 0.423 s
% 16.09/2.49  % (23671)------------------------------
% 16.09/2.49  % (23671)------------------------------
% 17.37/2.66  % (23675)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 17.37/2.67  % (23673)Time limit reached!
% 17.37/2.67  % (23673)------------------------------
% 17.37/2.67  % (23673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.37/2.67  % (23673)Termination reason: Time limit
% 17.37/2.67  
% 17.37/2.67  % (23673)Memory used [KB]: 8827
% 17.37/2.67  % (23673)Time elapsed: 0.408 s
% 17.37/2.67  % (23673)------------------------------
% 17.37/2.67  % (23673)------------------------------
% 18.63/2.77  % (23672)Time limit reached!
% 18.63/2.77  % (23672)------------------------------
% 18.63/2.77  % (23672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.63/2.77  % (23672)Termination reason: Time limit
% 18.63/2.77  
% 18.63/2.77  % (23672)Memory used [KB]: 12281
% 18.63/2.77  % (23672)Time elapsed: 0.503 s
% 18.63/2.77  % (23672)------------------------------
% 18.63/2.77  % (23672)------------------------------
% 18.63/2.81  % (23676)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 19.42/2.85  % (23641)Time limit reached!
% 19.42/2.85  % (23641)------------------------------
% 19.42/2.85  % (23641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.42/2.85  % (23641)Termination reason: Time limit
% 19.42/2.85  % (23641)Termination phase: Saturation
% 19.42/2.85  
% 19.42/2.85  % (23641)Memory used [KB]: 16247
% 19.42/2.85  % (23641)Time elapsed: 2.400 s
% 19.42/2.85  % (23641)------------------------------
% 19.42/2.85  % (23641)------------------------------
% 20.19/2.94  % (23675)Time limit reached!
% 20.19/2.94  % (23675)------------------------------
% 20.19/2.94  % (23675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.19/2.94  % (23675)Termination reason: Time limit
% 20.19/2.94  % (23675)Termination phase: Saturation
% 20.19/2.94  
% 20.19/2.94  % (23675)Memory used [KB]: 4349
% 20.19/2.94  % (23675)Time elapsed: 0.400 s
% 20.19/2.94  % (23675)------------------------------
% 20.19/2.94  % (23675)------------------------------
% 21.86/3.12  % (23676)Time limit reached!
% 21.86/3.12  % (23676)------------------------------
% 21.86/3.12  % (23676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.86/3.12  % (23676)Termination reason: Time limit
% 21.86/3.12  
% 21.86/3.12  % (23676)Memory used [KB]: 8827
% 21.86/3.12  % (23676)Time elapsed: 0.422 s
% 21.86/3.12  % (23676)------------------------------
% 21.86/3.12  % (23676)------------------------------
% 24.98/3.53  % (23637)Time limit reached!
% 24.98/3.53  % (23637)------------------------------
% 24.98/3.53  % (23637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.98/3.53  % (23637)Termination reason: Time limit
% 24.98/3.53  
% 24.98/3.53  % (23637)Memory used [KB]: 35820
% 24.98/3.53  % (23637)Time elapsed: 3.115 s
% 24.98/3.53  % (23637)------------------------------
% 24.98/3.53  % (23637)------------------------------
% 24.98/3.53  % (23634)Time limit reached!
% 24.98/3.53  % (23634)------------------------------
% 24.98/3.53  % (23634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.98/3.53  % (23634)Termination reason: Time limit
% 24.98/3.53  
% 24.98/3.53  % (23634)Memory used [KB]: 28656
% 24.98/3.53  % (23634)Time elapsed: 3.111 s
% 24.98/3.53  % (23634)------------------------------
% 24.98/3.53  % (23634)------------------------------
% 31.55/4.37  % (23663)Time limit reached!
% 31.55/4.37  % (23663)------------------------------
% 31.55/4.37  % (23663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.55/4.37  % (23663)Termination reason: Time limit
% 31.55/4.37  % (23663)Termination phase: Saturation
% 31.55/4.37  
% 31.55/4.37  % (23663)Memory used [KB]: 26481
% 31.55/4.37  % (23663)Time elapsed: 3.300 s
% 31.55/4.37  % (23663)------------------------------
% 31.55/4.37  % (23663)------------------------------
% 31.55/4.39  % (23659)Time limit reached!
% 31.55/4.39  % (23659)------------------------------
% 31.55/4.39  % (23659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.55/4.39  % (23659)Termination reason: Time limit
% 31.55/4.39  
% 31.55/4.39  % (23659)Memory used [KB]: 32622
% 31.55/4.39  % (23659)Time elapsed: 3.443 s
% 31.55/4.39  % (23659)------------------------------
% 31.55/4.39  % (23659)------------------------------
% 31.55/4.39  % (23664)Time limit reached!
% 31.55/4.39  % (23664)------------------------------
% 31.55/4.39  % (23664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.55/4.39  % (23664)Termination reason: Time limit
% 31.55/4.39  % (23664)Termination phase: Saturation
% 31.55/4.39  
% 31.55/4.39  % (23664)Memory used [KB]: 32622
% 31.55/4.39  % (23664)Time elapsed: 3.0000 s
% 31.55/4.39  % (23664)------------------------------
% 31.55/4.39  % (23664)------------------------------
% 37.67/5.15  % (23667)Refutation found. Thanks to Tanya!
% 37.67/5.15  % SZS status Theorem for theBenchmark
% 37.67/5.15  % SZS output start Proof for theBenchmark
% 37.67/5.15  fof(f69232,plain,(
% 37.67/5.15    $false),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f61,f69050])).
% 37.67/5.15  fof(f69050,plain,(
% 37.67/5.15    ~r1_tarski(sK0,sK0)),
% 37.67/5.15    inference(forward_demodulation,[],[f69049,f11909])).
% 37.67/5.15  fof(f11909,plain,(
% 37.67/5.15    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 37.67/5.15    inference(forward_demodulation,[],[f11907,f8613])).
% 37.67/5.15  fof(f8613,plain,(
% 37.67/5.15    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f70,f8552,f54])).
% 37.67/5.15  fof(f54,plain,(
% 37.67/5.15    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 37.67/5.15    inference(cnf_transformation,[],[f35])).
% 37.67/5.15  fof(f35,plain,(
% 37.67/5.15    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 37.67/5.15    inference(flattening,[],[f34])).
% 37.67/5.15  fof(f34,plain,(
% 37.67/5.15    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 37.67/5.15    inference(nnf_transformation,[],[f2])).
% 37.67/5.15  fof(f2,axiom,(
% 37.67/5.15    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 37.67/5.15  fof(f8552,plain,(
% 37.67/5.15    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 37.67/5.15    inference(superposition,[],[f3035,f316])).
% 37.67/5.15  fof(f316,plain,(
% 37.67/5.15    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))),
% 37.67/5.15    inference(forward_demodulation,[],[f315,f40])).
% 37.67/5.15  fof(f40,plain,(
% 37.67/5.15    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 37.67/5.15    inference(cnf_transformation,[],[f5])).
% 37.67/5.15  fof(f5,axiom,(
% 37.67/5.15    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 37.67/5.15  fof(f315,plain,(
% 37.67/5.15    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0)),
% 37.67/5.15    inference(superposition,[],[f58,f262])).
% 37.67/5.15  fof(f262,plain,(
% 37.67/5.15    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f39,f163,f54])).
% 37.67/5.15  fof(f163,plain,(
% 37.67/5.15    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k1_relat_1(sK1)),X0)) )),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f72,f56])).
% 37.67/5.15  fof(f56,plain,(
% 37.67/5.15    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 37.67/5.15    inference(cnf_transformation,[],[f29])).
% 37.67/5.15  fof(f29,plain,(
% 37.67/5.15    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 37.67/5.15    inference(ennf_transformation,[],[f6])).
% 37.67/5.15  fof(f6,axiom,(
% 37.67/5.15    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 37.67/5.15  fof(f72,plain,(
% 37.67/5.15    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(k1_relat_1(sK1),X0))) )),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f44,f37,f57])).
% 37.67/5.15  fof(f57,plain,(
% 37.67/5.15    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 37.67/5.15    inference(cnf_transformation,[],[f31])).
% 37.67/5.15  fof(f31,plain,(
% 37.67/5.15    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 37.67/5.15    inference(flattening,[],[f30])).
% 37.67/5.15  fof(f30,plain,(
% 37.67/5.15    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 37.67/5.15    inference(ennf_transformation,[],[f3])).
% 37.67/5.15  fof(f3,axiom,(
% 37.67/5.15    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 37.67/5.15  fof(f37,plain,(
% 37.67/5.15    r1_tarski(sK0,k1_relat_1(sK1))),
% 37.67/5.15    inference(cnf_transformation,[],[f33])).
% 37.67/5.15  fof(f33,plain,(
% 37.67/5.15    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 37.67/5.15    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f32])).
% 37.67/5.15  fof(f32,plain,(
% 37.67/5.15    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 37.67/5.15    introduced(choice_axiom,[])).
% 37.67/5.15  fof(f21,plain,(
% 37.67/5.15    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 37.67/5.15    inference(flattening,[],[f20])).
% 37.67/5.15  fof(f20,plain,(
% 37.67/5.15    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 37.67/5.15    inference(ennf_transformation,[],[f19])).
% 37.67/5.15  fof(f19,negated_conjecture,(
% 37.67/5.15    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 37.67/5.15    inference(negated_conjecture,[],[f18])).
% 37.67/5.15  fof(f18,conjecture,(
% 37.67/5.15    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 37.67/5.15  fof(f44,plain,(
% 37.67/5.15    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 37.67/5.15    inference(cnf_transformation,[],[f8])).
% 37.67/5.15  fof(f8,axiom,(
% 37.67/5.15    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 37.67/5.15  fof(f39,plain,(
% 37.67/5.15    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 37.67/5.15    inference(cnf_transformation,[],[f4])).
% 37.67/5.15  fof(f4,axiom,(
% 37.67/5.15    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 37.67/5.15  fof(f58,plain,(
% 37.67/5.15    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 37.67/5.15    inference(definition_unfolding,[],[f48,f47])).
% 37.67/5.15  fof(f47,plain,(
% 37.67/5.15    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 37.67/5.15    inference(cnf_transformation,[],[f10])).
% 37.67/5.15  fof(f10,axiom,(
% 37.67/5.15    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 37.67/5.15  fof(f48,plain,(
% 37.67/5.15    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 37.67/5.15    inference(cnf_transformation,[],[f7])).
% 37.67/5.15  fof(f7,axiom,(
% 37.67/5.15    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 37.67/5.15  fof(f3035,plain,(
% 37.67/5.15    ( ! [X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X1)))) )),
% 37.67/5.15    inference(superposition,[],[f87,f213])).
% 37.67/5.15  fof(f213,plain,(
% 37.67/5.15    ( ! [X0] : (k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) )),
% 37.67/5.15    inference(global_subsumption,[],[f36,f211])).
% 37.67/5.15  fof(f211,plain,(
% 37.67/5.15    ( ! [X0] : (k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) | ~v1_relat_1(sK1)) )),
% 37.67/5.15    inference(superposition,[],[f59,f62])).
% 37.67/5.15  fof(f62,plain,(
% 37.67/5.15    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f36,f41])).
% 37.67/5.15  fof(f41,plain,(
% 37.67/5.15    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 37.67/5.15    inference(cnf_transformation,[],[f22])).
% 37.67/5.15  fof(f22,plain,(
% 37.67/5.15    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 37.67/5.15    inference(ennf_transformation,[],[f15])).
% 37.67/5.15  fof(f15,axiom,(
% 37.67/5.15    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 37.67/5.15  fof(f59,plain,(
% 37.67/5.15    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 37.67/5.15    inference(definition_unfolding,[],[f55,f47])).
% 37.67/5.15  fof(f55,plain,(
% 37.67/5.15    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 37.67/5.15    inference(cnf_transformation,[],[f28])).
% 37.67/5.15  fof(f28,plain,(
% 37.67/5.15    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 37.67/5.15    inference(ennf_transformation,[],[f17])).
% 37.67/5.15  fof(f17,axiom,(
% 37.67/5.15    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 37.67/5.15  fof(f36,plain,(
% 37.67/5.15    v1_relat_1(sK1)),
% 37.67/5.15    inference(cnf_transformation,[],[f33])).
% 37.67/5.15  fof(f87,plain,(
% 37.67/5.15    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f68,f50])).
% 37.67/5.15  fof(f50,plain,(
% 37.67/5.15    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 37.67/5.15    inference(cnf_transformation,[],[f26])).
% 37.67/5.15  fof(f26,plain,(
% 37.67/5.15    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 37.67/5.15    inference(ennf_transformation,[],[f14])).
% 37.67/5.15  fof(f14,axiom,(
% 37.67/5.15    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 37.67/5.15  fof(f68,plain,(
% 37.67/5.15    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f36,f49])).
% 37.67/5.15  fof(f49,plain,(
% 37.67/5.15    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 37.67/5.15    inference(cnf_transformation,[],[f25])).
% 37.67/5.15  fof(f25,plain,(
% 37.67/5.15    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 37.67/5.15    inference(ennf_transformation,[],[f11])).
% 37.67/5.15  fof(f11,axiom,(
% 37.67/5.15    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 37.67/5.15  fof(f70,plain,(
% 37.67/5.15    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) )),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f36,f51])).
% 37.67/5.15  fof(f51,plain,(
% 37.67/5.15    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 37.67/5.15    inference(cnf_transformation,[],[f27])).
% 37.67/5.15  fof(f27,plain,(
% 37.67/5.15    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 37.67/5.15    inference(ennf_transformation,[],[f16])).
% 37.67/5.15  fof(f16,axiom,(
% 37.67/5.15    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 37.67/5.15  fof(f11907,plain,(
% 37.67/5.15    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 37.67/5.15    inference(superposition,[],[f79,f8656])).
% 37.67/5.15  fof(f8656,plain,(
% 37.67/5.15    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 37.67/5.15    inference(forward_demodulation,[],[f8638,f67])).
% 37.67/5.15  fof(f67,plain,(
% 37.67/5.15    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0)) )),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f60,f36,f43])).
% 37.67/5.15  fof(f43,plain,(
% 37.67/5.15    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 37.67/5.15    inference(cnf_transformation,[],[f24])).
% 37.67/5.15  fof(f24,plain,(
% 37.67/5.15    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 37.67/5.15    inference(ennf_transformation,[],[f13])).
% 37.67/5.15  fof(f13,axiom,(
% 37.67/5.15    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 37.67/5.15  fof(f60,plain,(
% 37.67/5.15    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 37.67/5.15    inference(equality_resolution,[],[f53])).
% 37.67/5.15  fof(f53,plain,(
% 37.67/5.15    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 37.67/5.15    inference(cnf_transformation,[],[f35])).
% 37.67/5.15  fof(f8638,plain,(
% 37.67/5.15    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 37.67/5.15    inference(superposition,[],[f80,f8613])).
% 37.67/5.15  fof(f80,plain,(
% 37.67/5.15    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f68,f42])).
% 37.67/5.15  fof(f42,plain,(
% 37.67/5.15    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 37.67/5.15    inference(cnf_transformation,[],[f23])).
% 37.67/5.15  fof(f23,plain,(
% 37.67/5.15    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 37.67/5.15    inference(ennf_transformation,[],[f12])).
% 37.67/5.15  fof(f12,axiom,(
% 37.67/5.15    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 37.67/5.15  fof(f79,plain,(
% 37.67/5.15    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) )),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f68,f41])).
% 37.67/5.15  fof(f69049,plain,(
% 37.67/5.15    ~r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)))),
% 37.67/5.15    inference(forward_demodulation,[],[f68658,f472])).
% 37.67/5.15  fof(f472,plain,(
% 37.67/5.15    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(k10_relat_1(sK1,X1),X0))) )),
% 37.67/5.15    inference(superposition,[],[f71,f45])).
% 37.67/5.15  fof(f45,plain,(
% 37.67/5.15    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 37.67/5.15    inference(cnf_transformation,[],[f9])).
% 37.67/5.15  fof(f9,axiom,(
% 37.67/5.15    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 37.67/5.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 37.67/5.15  fof(f71,plain,(
% 37.67/5.15    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1)))) )),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f36,f59])).
% 37.67/5.15  fof(f68658,plain,(
% 37.67/5.15    ~r1_tarski(sK0,k1_setfam_1(k2_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)))),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f38,f68268,f57])).
% 37.67/5.15  fof(f68268,plain,(
% 37.67/5.15    ( ! [X6] : (r1_tarski(k1_setfam_1(k2_tarski(X6,sK0)),X6)) )),
% 37.67/5.15    inference(superposition,[],[f67727,f8613])).
% 37.67/5.15  fof(f67727,plain,(
% 37.67/5.15    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k2_tarski(X3,k1_relat_1(k7_relat_1(sK1,X2)))),X3)) )),
% 37.67/5.15    inference(superposition,[],[f24799,f4076])).
% 37.67/5.15  fof(f4076,plain,(
% 37.67/5.15    ( ! [X4,X3] : (k10_relat_1(k7_relat_1(k7_relat_1(sK1,X3),X4),k2_relat_1(k7_relat_1(sK1,X3))) = k1_setfam_1(k2_tarski(X4,k1_relat_1(k7_relat_1(sK1,X3))))) )),
% 37.67/5.15    inference(global_subsumption,[],[f68,f4073])).
% 37.67/5.15  fof(f4073,plain,(
% 37.67/5.15    ( ! [X4,X3] : (k10_relat_1(k7_relat_1(k7_relat_1(sK1,X3),X4),k2_relat_1(k7_relat_1(sK1,X3))) = k1_setfam_1(k2_tarski(X4,k1_relat_1(k7_relat_1(sK1,X3)))) | ~v1_relat_1(k7_relat_1(sK1,X3))) )),
% 37.67/5.15    inference(superposition,[],[f59,f79])).
% 37.67/5.15  fof(f24799,plain,(
% 37.67/5.15    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2),X1)) )),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f88,f188,f57])).
% 37.67/5.15  fof(f188,plain,(
% 37.67/5.15    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2),k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)))) )),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f86,f50])).
% 37.67/5.15  fof(f86,plain,(
% 37.67/5.15    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1))) )),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f68,f49])).
% 37.67/5.15  fof(f88,plain,(
% 37.67/5.15    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)),X1)) )),
% 37.67/5.15    inference(unit_resulting_resolution,[],[f68,f51])).
% 37.67/5.15  fof(f38,plain,(
% 37.67/5.15    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 37.67/5.15    inference(cnf_transformation,[],[f33])).
% 37.67/5.15  fof(f61,plain,(
% 37.67/5.15    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 37.67/5.15    inference(equality_resolution,[],[f52])).
% 37.67/5.15  fof(f52,plain,(
% 37.67/5.15    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 37.67/5.15    inference(cnf_transformation,[],[f35])).
% 37.67/5.15  % SZS output end Proof for theBenchmark
% 37.67/5.15  % (23667)------------------------------
% 37.67/5.15  % (23667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 37.67/5.15  % (23667)Termination reason: Refutation
% 37.67/5.15  
% 37.67/5.15  % (23667)Memory used [KB]: 43624
% 37.67/5.15  % (23667)Time elapsed: 3.459 s
% 37.67/5.15  % (23667)------------------------------
% 37.67/5.15  % (23667)------------------------------
% 37.67/5.16  % (23625)Success in time 4.806 s
%------------------------------------------------------------------------------
