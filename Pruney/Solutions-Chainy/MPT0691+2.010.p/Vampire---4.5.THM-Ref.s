%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:46 EST 2020

% Result     : Theorem 9.18s
% Output     : Refutation 9.18s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 930 expanded)
%              Number of leaves         :   21 ( 257 expanded)
%              Depth                    :   23
%              Number of atoms          :  203 (2041 expanded)
%              Number of equality atoms :   66 ( 351 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15416,plain,(
    $false ),
    inference(subsumption_resolution,[],[f15405,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f15405,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(superposition,[],[f2101,f15115])).

fof(f15115,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f15113,f14830])).

fof(f14830,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f14829,f414])).

fof(f414,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f290,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f290,plain,(
    ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(forward_demodulation,[],[f285,f44])).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f285,plain,(
    ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(backward_demodulation,[],[f271,f268])).

fof(f268,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f43,f221,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f221,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,k1_relat_1(sK1)),X0) ),
    inference(unit_resulting_resolution,[],[f88,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f61,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f88,plain,(
    ! [X0] : r1_tarski(sK0,k3_tarski(k2_tarski(k1_relat_1(sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f64,f41,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f41,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f36])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f271,plain,(
    ! [X0] : k3_tarski(k2_tarski(k4_xboole_0(sK0,k1_relat_1(sK1)),k4_xboole_0(X0,k4_xboole_0(sK0,k1_relat_1(sK1))))) = X0 ),
    inference(unit_resulting_resolution,[],[f221,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) = X1 ) ),
    inference(definition_unfolding,[],[f56,f51])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f14829,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k3_tarski(k2_tarski(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f14805,f824])).

fof(f824,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f743,f313])).

fof(f313,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2 ) ),
    inference(forward_demodulation,[],[f312,f268])).

fof(f312,plain,(
    ! [X2] :
      ( k1_xboole_0 = X2
      | ~ r1_tarski(X2,k4_xboole_0(sK0,k1_relat_1(sK1))) ) ),
    inference(forward_demodulation,[],[f277,f268])).

fof(f277,plain,(
    ! [X2] :
      ( k4_xboole_0(sK0,k1_relat_1(sK1)) = X2
      | ~ r1_tarski(X2,k4_xboole_0(sK0,k1_relat_1(sK1))) ) ),
    inference(resolution,[],[f221,f59])).

fof(f743,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0),X1) ),
    inference(unit_resulting_resolution,[],[f117,f68])).

fof(f117,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k3_tarski(k2_tarski(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f64,f79,f63])).

fof(f79,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f40,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f14805,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k3_tarski(k2_tarski(sK0,k4_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),sK0))) ),
    inference(unit_resulting_resolution,[],[f14736,f66])).

fof(f14736,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f4753,f413])).

fof(f413,plain,(
    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f412,f44])).

fof(f412,plain,(
    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f65,f268])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f4753,plain,(
    ! [X2] : r1_tarski(k1_setfam_1(k2_tarski(X2,k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X2))) ),
    inference(superposition,[],[f116,f651])).

fof(f651,plain,(
    ! [X0] : k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f81,f72])).

fof(f72,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f40,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f81,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) ),
    inference(unit_resulting_resolution,[],[f40,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f60,f50])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f116,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(backward_demodulation,[],[f108,f99])).

fof(f99,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f78,f45])).

fof(f78,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f40,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f108,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(unit_resulting_resolution,[],[f78,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f15113,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f99,f15033])).

fof(f15033,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f14839,f95])).

fof(f95,plain,(
    k9_relat_1(sK1,sK0) = k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f40,f41,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f14839,plain,(
    k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f478,f14830])).

fof(f478,plain,(
    k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,sK0))) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f472,f137])).

fof(f137,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f130,f100])).

fof(f100,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f78,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f130,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f40,f79,f47])).

fof(f472,plain,(
    k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,sK0))) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f40,f122,f47])).

fof(f122,plain,(
    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f79,f63])).

fof(f2101,plain,(
    ! [X0] : ~ r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f2013,f652])).

fof(f652,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(k10_relat_1(sK1,X1),X0)) ),
    inference(superposition,[],[f81,f49])).

fof(f2013,plain,(
    ! [X0] : ~ r1_tarski(sK0,k1_setfam_1(k2_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0))) ),
    inference(unit_resulting_resolution,[],[f42,f1986,f63])).

fof(f1986,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k2_tarski(X2,X3)),X2) ),
    inference(superposition,[],[f1812,f65])).

fof(f1812,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f1810,f68])).

fof(f1810,plain,(
    ! [X6,X7] : r1_tarski(X6,k3_tarski(k2_tarski(X7,X6))) ),
    inference(subsumption_resolution,[],[f1806,f43])).

fof(f1806,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | r1_tarski(X6,k3_tarski(k2_tarski(X7,X6))) ) ),
    inference(superposition,[],[f455,f1737])).

fof(f1737,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[],[f1350,f49])).

fof(f1350,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f43,f983,f59])).

fof(f983,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f64,f456])).

fof(f456,plain,(
    ! [X2,X3] :
      ( r1_tarski(k4_xboole_0(X3,X2),k1_xboole_0)
      | ~ r1_tarski(X3,X2) ) ),
    inference(superposition,[],[f68,f414])).

fof(f455,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0)
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f69,f414])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f62,f51])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f42,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:50:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (8408)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (8425)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.49  % (8416)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (8412)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (8404)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (8420)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (8407)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (8405)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (8411)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (8406)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (8426)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (8418)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.35/0.54  % (8410)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.35/0.54  % (8409)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.54  % (8413)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.35/0.54  % (8403)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.35/0.54  % (8428)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.35/0.55  % (8432)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.35/0.55  % (8429)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.35/0.55  % (8431)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.35/0.55  % (8424)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.35/0.55  % (8421)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.35/0.55  % (8415)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.35/0.55  % (8430)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.35/0.55  % (8422)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.49/0.56  % (8423)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.49/0.56  % (8417)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.49/0.56  % (8427)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.49/0.56  % (8419)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.49/0.56  % (8414)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 3.56/0.83  % (8405)Time limit reached!
% 3.56/0.83  % (8405)------------------------------
% 3.56/0.83  % (8405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.84  % (8427)Time limit reached!
% 3.56/0.84  % (8427)------------------------------
% 3.56/0.84  % (8427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.84  % (8427)Termination reason: Time limit
% 3.56/0.84  
% 3.56/0.84  % (8427)Memory used [KB]: 13048
% 3.56/0.84  % (8427)Time elapsed: 0.429 s
% 3.56/0.84  % (8427)------------------------------
% 3.56/0.84  % (8427)------------------------------
% 3.56/0.85  % (8405)Termination reason: Time limit
% 3.56/0.85  % (8405)Termination phase: Saturation
% 3.56/0.85  
% 3.56/0.85  % (8405)Memory used [KB]: 7419
% 3.56/0.85  % (8405)Time elapsed: 0.400 s
% 3.56/0.85  % (8405)------------------------------
% 3.56/0.85  % (8405)------------------------------
% 3.77/0.92  % (8417)Time limit reached!
% 3.77/0.92  % (8417)------------------------------
% 3.77/0.92  % (8417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.77/0.92  % (8417)Termination reason: Time limit
% 3.77/0.92  
% 3.77/0.92  % (8417)Memory used [KB]: 6140
% 3.77/0.92  % (8417)Time elapsed: 0.512 s
% 3.77/0.92  % (8417)------------------------------
% 3.77/0.92  % (8417)------------------------------
% 4.35/0.93  % (8409)Time limit reached!
% 4.35/0.93  % (8409)------------------------------
% 4.35/0.93  % (8409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.93  % (8409)Termination reason: Time limit
% 4.35/0.93  
% 4.35/0.93  % (8409)Memory used [KB]: 15351
% 4.35/0.93  % (8409)Time elapsed: 0.515 s
% 4.35/0.93  % (8409)------------------------------
% 4.35/0.93  % (8409)------------------------------
% 4.35/0.93  % (8432)Time limit reached!
% 4.35/0.93  % (8432)------------------------------
% 4.35/0.93  % (8432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.93  % (8432)Termination reason: Time limit
% 4.35/0.93  % (8432)Termination phase: Saturation
% 4.35/0.93  
% 4.35/0.93  % (8432)Memory used [KB]: 2174
% 4.35/0.93  % (8432)Time elapsed: 0.500 s
% 4.35/0.93  % (8432)------------------------------
% 4.35/0.93  % (8432)------------------------------
% 4.65/0.98  % (8618)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.65/0.98  % (8612)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 5.12/1.05  % (8410)Time limit reached!
% 5.12/1.05  % (8410)------------------------------
% 5.12/1.05  % (8410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.12/1.05  % (8410)Termination reason: Time limit
% 5.12/1.05  
% 5.12/1.05  % (8410)Memory used [KB]: 7164
% 5.12/1.05  % (8410)Time elapsed: 0.606 s
% 5.12/1.05  % (8410)------------------------------
% 5.12/1.05  % (8410)------------------------------
% 5.12/1.05  % (8659)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.12/1.05  % (8657)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 5.12/1.07  % (8660)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 6.01/1.16  % (8665)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.73/1.23  % (8404)Time limit reached!
% 6.73/1.23  % (8404)------------------------------
% 6.73/1.23  % (8404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.73/1.24  % (8404)Termination reason: Time limit
% 6.73/1.24  
% 6.73/1.24  % (8404)Memory used [KB]: 8443
% 6.73/1.24  % (8404)Time elapsed: 0.815 s
% 6.73/1.24  % (8404)------------------------------
% 6.73/1.24  % (8404)------------------------------
% 7.53/1.33  % (8406)Time limit reached!
% 7.53/1.33  % (8406)------------------------------
% 7.53/1.33  % (8406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.53/1.33  % (8406)Termination reason: Time limit
% 7.53/1.33  
% 7.53/1.33  % (8406)Memory used [KB]: 7291
% 7.53/1.33  % (8406)Time elapsed: 0.917 s
% 7.53/1.33  % (8406)------------------------------
% 7.53/1.33  % (8406)------------------------------
% 7.53/1.34  % (8666)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 7.81/1.43  % (8415)Time limit reached!
% 7.81/1.43  % (8415)------------------------------
% 7.81/1.43  % (8415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.81/1.43  % (8415)Termination reason: Time limit
% 7.81/1.43  
% 7.81/1.43  % (8415)Memory used [KB]: 15479
% 7.81/1.43  % (8415)Time elapsed: 1.022 s
% 7.81/1.43  % (8415)------------------------------
% 7.81/1.43  % (8415)------------------------------
% 7.81/1.43  % (8430)Time limit reached!
% 7.81/1.43  % (8430)------------------------------
% 7.81/1.43  % (8430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.33/1.44  % (8430)Termination reason: Time limit
% 8.33/1.44  % (8430)Termination phase: Saturation
% 8.33/1.44  
% 8.33/1.44  % (8430)Memory used [KB]: 9978
% 8.33/1.44  % (8430)Time elapsed: 1.0000 s
% 8.33/1.44  % (8430)------------------------------
% 8.33/1.44  % (8430)------------------------------
% 8.33/1.46  % (8667)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 8.94/1.54  % (8669)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 9.18/1.57  % (8668)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 9.18/1.59  % (8414)Refutation found. Thanks to Tanya!
% 9.18/1.59  % SZS status Theorem for theBenchmark
% 9.18/1.59  % SZS output start Proof for theBenchmark
% 9.18/1.59  fof(f15416,plain,(
% 9.18/1.59    $false),
% 9.18/1.59    inference(subsumption_resolution,[],[f15405,f71])).
% 9.18/1.59  fof(f71,plain,(
% 9.18/1.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 9.18/1.59    inference(equality_resolution,[],[f57])).
% 9.18/1.59  fof(f57,plain,(
% 9.18/1.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 9.18/1.59    inference(cnf_transformation,[],[f39])).
% 9.18/1.59  fof(f39,plain,(
% 9.18/1.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 9.18/1.59    inference(flattening,[],[f38])).
% 9.18/1.59  fof(f38,plain,(
% 9.18/1.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 9.18/1.59    inference(nnf_transformation,[],[f1])).
% 9.18/1.59  fof(f1,axiom,(
% 9.18/1.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 9.18/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 9.18/1.59  fof(f15405,plain,(
% 9.18/1.59    ~r1_tarski(sK0,sK0)),
% 9.18/1.59    inference(superposition,[],[f2101,f15115])).
% 9.18/1.59  fof(f15115,plain,(
% 9.18/1.59    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 9.18/1.59    inference(forward_demodulation,[],[f15113,f14830])).
% 9.18/1.59  fof(f14830,plain,(
% 9.18/1.59    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 9.18/1.59    inference(forward_demodulation,[],[f14829,f414])).
% 9.18/1.59  fof(f414,plain,(
% 9.18/1.59    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 9.18/1.59    inference(superposition,[],[f290,f49])).
% 9.18/1.59  fof(f49,plain,(
% 9.18/1.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 9.18/1.59    inference(cnf_transformation,[],[f10])).
% 9.18/1.59  fof(f10,axiom,(
% 9.18/1.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 9.18/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 9.18/1.59  fof(f290,plain,(
% 9.18/1.59    ( ! [X0] : (k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0) )),
% 9.18/1.59    inference(forward_demodulation,[],[f285,f44])).
% 9.18/1.59  fof(f44,plain,(
% 9.18/1.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 9.18/1.59    inference(cnf_transformation,[],[f4])).
% 9.18/1.59  fof(f4,axiom,(
% 9.18/1.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 9.18/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 9.18/1.59  fof(f285,plain,(
% 9.18/1.59    ( ! [X0] : (k3_tarski(k2_tarski(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) = X0) )),
% 9.18/1.59    inference(backward_demodulation,[],[f271,f268])).
% 9.18/1.59  fof(f268,plain,(
% 9.18/1.59    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))),
% 9.18/1.59    inference(unit_resulting_resolution,[],[f43,f221,f59])).
% 9.18/1.59  fof(f59,plain,(
% 9.18/1.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 9.18/1.59    inference(cnf_transformation,[],[f39])).
% 9.18/1.59  fof(f221,plain,(
% 9.18/1.59    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k1_relat_1(sK1)),X0)) )),
% 9.18/1.59    inference(unit_resulting_resolution,[],[f88,f68])).
% 9.18/1.59  fof(f68,plain,(
% 9.18/1.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 9.18/1.59    inference(definition_unfolding,[],[f61,f51])).
% 9.18/1.59  fof(f51,plain,(
% 9.18/1.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 9.18/1.59    inference(cnf_transformation,[],[f11])).
% 9.18/1.59  fof(f11,axiom,(
% 9.18/1.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 9.18/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 9.18/1.59  fof(f61,plain,(
% 9.18/1.59    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 9.18/1.59    inference(cnf_transformation,[],[f32])).
% 9.18/1.59  fof(f32,plain,(
% 9.18/1.59    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 9.18/1.59    inference(ennf_transformation,[],[f5])).
% 9.18/1.59  fof(f5,axiom,(
% 9.18/1.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 9.18/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 9.18/1.59  fof(f88,plain,(
% 9.18/1.59    ( ! [X0] : (r1_tarski(sK0,k3_tarski(k2_tarski(k1_relat_1(sK1),X0)))) )),
% 9.18/1.59    inference(unit_resulting_resolution,[],[f64,f41,f63])).
% 9.18/1.59  fof(f63,plain,(
% 9.18/1.59    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 9.18/1.59    inference(cnf_transformation,[],[f35])).
% 9.18/1.59  fof(f35,plain,(
% 9.18/1.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 9.18/1.59    inference(flattening,[],[f34])).
% 9.18/1.59  fof(f34,plain,(
% 9.18/1.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 9.18/1.59    inference(ennf_transformation,[],[f2])).
% 9.18/1.59  fof(f2,axiom,(
% 9.18/1.59    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 9.18/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 9.18/1.59  fof(f41,plain,(
% 9.18/1.59    r1_tarski(sK0,k1_relat_1(sK1))),
% 9.18/1.59    inference(cnf_transformation,[],[f37])).
% 9.18/1.59  fof(f37,plain,(
% 9.18/1.59    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 9.18/1.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f36])).
% 9.18/1.59  fof(f36,plain,(
% 9.18/1.59    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 9.18/1.59    introduced(choice_axiom,[])).
% 9.18/1.59  fof(f23,plain,(
% 9.18/1.59    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 9.18/1.59    inference(flattening,[],[f22])).
% 9.18/1.59  fof(f22,plain,(
% 9.18/1.59    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 9.18/1.59    inference(ennf_transformation,[],[f21])).
% 9.18/1.59  fof(f21,negated_conjecture,(
% 9.18/1.59    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 9.18/1.59    inference(negated_conjecture,[],[f20])).
% 9.18/1.59  fof(f20,conjecture,(
% 9.18/1.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 9.18/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 9.18/1.59  fof(f64,plain,(
% 9.18/1.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 9.18/1.59    inference(definition_unfolding,[],[f48,f51])).
% 9.18/1.59  fof(f48,plain,(
% 9.18/1.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 9.18/1.59    inference(cnf_transformation,[],[f9])).
% 9.18/1.59  fof(f9,axiom,(
% 9.18/1.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 9.18/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 9.18/1.59  fof(f43,plain,(
% 9.18/1.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 9.18/1.59    inference(cnf_transformation,[],[f3])).
% 9.18/1.59  fof(f3,axiom,(
% 9.18/1.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 9.18/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 9.18/1.59  fof(f271,plain,(
% 9.18/1.59    ( ! [X0] : (k3_tarski(k2_tarski(k4_xboole_0(sK0,k1_relat_1(sK1)),k4_xboole_0(X0,k4_xboole_0(sK0,k1_relat_1(sK1))))) = X0) )),
% 9.18/1.59    inference(unit_resulting_resolution,[],[f221,f66])).
% 9.18/1.59  fof(f66,plain,(
% 9.18/1.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) = X1) )),
% 9.18/1.59    inference(definition_unfolding,[],[f56,f51])).
% 9.18/1.59  fof(f56,plain,(
% 9.18/1.59    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 9.18/1.59    inference(cnf_transformation,[],[f30])).
% 9.18/1.59  fof(f30,plain,(
% 9.18/1.59    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 9.18/1.59    inference(ennf_transformation,[],[f7])).
% 9.18/1.60  fof(f7,axiom,(
% 9.18/1.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 9.18/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 9.18/1.60  fof(f14829,plain,(
% 9.18/1.60    k1_relat_1(k7_relat_1(sK1,sK0)) = k3_tarski(k2_tarski(sK0,k1_xboole_0))),
% 9.18/1.60    inference(forward_demodulation,[],[f14805,f824])).
% 9.18/1.60  fof(f824,plain,(
% 9.18/1.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0)) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f743,f313])).
% 9.18/1.60  fof(f313,plain,(
% 9.18/1.60    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X2) )),
% 9.18/1.60    inference(forward_demodulation,[],[f312,f268])).
% 9.18/1.60  fof(f312,plain,(
% 9.18/1.60    ( ! [X2] : (k1_xboole_0 = X2 | ~r1_tarski(X2,k4_xboole_0(sK0,k1_relat_1(sK1)))) )),
% 9.18/1.60    inference(forward_demodulation,[],[f277,f268])).
% 9.18/1.60  fof(f277,plain,(
% 9.18/1.60    ( ! [X2] : (k4_xboole_0(sK0,k1_relat_1(sK1)) = X2 | ~r1_tarski(X2,k4_xboole_0(sK0,k1_relat_1(sK1)))) )),
% 9.18/1.60    inference(resolution,[],[f221,f59])).
% 9.18/1.60  fof(f743,plain,(
% 9.18/1.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0),X1)) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f117,f68])).
% 9.18/1.60  fof(f117,plain,(
% 9.18/1.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k3_tarski(k2_tarski(X0,X1)))) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f64,f79,f63])).
% 9.18/1.60  fof(f79,plain,(
% 9.18/1.60    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f40,f54])).
% 9.18/1.60  fof(f54,plain,(
% 9.18/1.60    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 9.18/1.60    inference(cnf_transformation,[],[f28])).
% 9.18/1.60  fof(f28,plain,(
% 9.18/1.60    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 9.18/1.60    inference(ennf_transformation,[],[f18])).
% 9.18/1.60  fof(f18,axiom,(
% 9.18/1.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 9.18/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 9.18/1.60  fof(f40,plain,(
% 9.18/1.60    v1_relat_1(sK1)),
% 9.18/1.60    inference(cnf_transformation,[],[f37])).
% 9.18/1.60  fof(f14805,plain,(
% 9.18/1.60    k1_relat_1(k7_relat_1(sK1,sK0)) = k3_tarski(k2_tarski(sK0,k4_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),sK0)))),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f14736,f66])).
% 9.18/1.60  fof(f14736,plain,(
% 9.18/1.60    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 9.18/1.60    inference(superposition,[],[f4753,f413])).
% 9.18/1.60  fof(f413,plain,(
% 9.18/1.60    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))),
% 9.18/1.60    inference(forward_demodulation,[],[f412,f44])).
% 9.18/1.60  fof(f412,plain,(
% 9.18/1.60    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0)),
% 9.18/1.60    inference(superposition,[],[f65,f268])).
% 9.18/1.60  fof(f65,plain,(
% 9.18/1.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 9.18/1.60    inference(definition_unfolding,[],[f52,f50])).
% 9.18/1.60  fof(f50,plain,(
% 9.18/1.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 9.18/1.60    inference(cnf_transformation,[],[f12])).
% 9.18/1.60  fof(f12,axiom,(
% 9.18/1.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 9.18/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 9.18/1.60  fof(f52,plain,(
% 9.18/1.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 9.18/1.60    inference(cnf_transformation,[],[f8])).
% 9.18/1.60  fof(f8,axiom,(
% 9.18/1.60    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 9.18/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 9.18/1.60  fof(f4753,plain,(
% 9.18/1.60    ( ! [X2] : (r1_tarski(k1_setfam_1(k2_tarski(X2,k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X2)))) )),
% 9.18/1.60    inference(superposition,[],[f116,f651])).
% 9.18/1.60  fof(f651,plain,(
% 9.18/1.60    ( ! [X0] : (k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) )),
% 9.18/1.60    inference(superposition,[],[f81,f72])).
% 9.18/1.60  fof(f72,plain,(
% 9.18/1.60    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f40,f45])).
% 9.18/1.60  fof(f45,plain,(
% 9.18/1.60    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 9.18/1.60    inference(cnf_transformation,[],[f24])).
% 9.18/1.60  fof(f24,plain,(
% 9.18/1.60    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 9.18/1.60    inference(ennf_transformation,[],[f16])).
% 9.18/1.60  fof(f16,axiom,(
% 9.18/1.60    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 9.18/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 9.18/1.60  fof(f81,plain,(
% 9.18/1.60    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1)))) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f40,f67])).
% 9.18/1.60  fof(f67,plain,(
% 9.18/1.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) )),
% 9.18/1.60    inference(definition_unfolding,[],[f60,f50])).
% 9.18/1.60  fof(f60,plain,(
% 9.18/1.60    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 9.18/1.60    inference(cnf_transformation,[],[f31])).
% 9.18/1.60  fof(f31,plain,(
% 9.18/1.60    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 9.18/1.60    inference(ennf_transformation,[],[f19])).
% 9.18/1.60  fof(f19,axiom,(
% 9.18/1.60    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 9.18/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 9.18/1.60  fof(f116,plain,(
% 9.18/1.60    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 9.18/1.60    inference(backward_demodulation,[],[f108,f99])).
% 9.18/1.60  fof(f99,plain,(
% 9.18/1.60    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f78,f45])).
% 9.18/1.60  fof(f78,plain,(
% 9.18/1.60    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f40,f53])).
% 9.18/1.60  fof(f53,plain,(
% 9.18/1.60    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 9.18/1.60    inference(cnf_transformation,[],[f27])).
% 9.18/1.60  fof(f27,plain,(
% 9.18/1.60    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 9.18/1.60    inference(ennf_transformation,[],[f13])).
% 9.18/1.60  fof(f13,axiom,(
% 9.18/1.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 9.18/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 9.18/1.60  fof(f108,plain,(
% 9.18/1.60    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))))) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f78,f55])).
% 9.18/1.60  fof(f55,plain,(
% 9.18/1.60    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 9.18/1.60    inference(cnf_transformation,[],[f29])).
% 9.18/1.60  fof(f29,plain,(
% 9.18/1.60    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 9.18/1.60    inference(ennf_transformation,[],[f17])).
% 9.18/1.60  fof(f17,axiom,(
% 9.18/1.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 9.18/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 9.18/1.60  fof(f15113,plain,(
% 9.18/1.60    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 9.18/1.60    inference(superposition,[],[f99,f15033])).
% 9.18/1.60  fof(f15033,plain,(
% 9.18/1.60    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 9.18/1.60    inference(forward_demodulation,[],[f14839,f95])).
% 9.18/1.60  fof(f95,plain,(
% 9.18/1.60    k9_relat_1(sK1,sK0) = k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0)),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f40,f41,f47])).
% 9.18/1.60  fof(f47,plain,(
% 9.18/1.60    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 9.18/1.60    inference(cnf_transformation,[],[f26])).
% 9.18/1.60  fof(f26,plain,(
% 9.18/1.60    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 9.18/1.60    inference(ennf_transformation,[],[f15])).
% 9.18/1.60  fof(f15,axiom,(
% 9.18/1.60    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 9.18/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 9.18/1.60  fof(f14839,plain,(
% 9.18/1.60    k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 9.18/1.60    inference(backward_demodulation,[],[f478,f14830])).
% 9.18/1.60  fof(f478,plain,(
% 9.18/1.60    k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,sK0))) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 9.18/1.60    inference(forward_demodulation,[],[f472,f137])).
% 9.18/1.60  fof(f137,plain,(
% 9.18/1.60    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 9.18/1.60    inference(forward_demodulation,[],[f130,f100])).
% 9.18/1.60  fof(f100,plain,(
% 9.18/1.60    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f78,f46])).
% 9.18/1.60  fof(f46,plain,(
% 9.18/1.60    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 9.18/1.60    inference(cnf_transformation,[],[f25])).
% 9.18/1.60  fof(f25,plain,(
% 9.18/1.60    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 9.18/1.60    inference(ennf_transformation,[],[f14])).
% 9.18/1.60  fof(f14,axiom,(
% 9.18/1.60    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 9.18/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 9.18/1.60  fof(f130,plain,(
% 9.18/1.60    ( ! [X0] : (k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f40,f79,f47])).
% 9.18/1.60  fof(f472,plain,(
% 9.18/1.60    k9_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,sK0))) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f40,f122,f47])).
% 9.18/1.60  fof(f122,plain,(
% 9.18/1.60    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f41,f79,f63])).
% 9.18/1.60  fof(f2101,plain,(
% 9.18/1.60    ( ! [X0] : (~r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,sK0)))) )),
% 9.18/1.60    inference(forward_demodulation,[],[f2013,f652])).
% 9.18/1.60  fof(f652,plain,(
% 9.18/1.60    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(k10_relat_1(sK1,X1),X0))) )),
% 9.18/1.60    inference(superposition,[],[f81,f49])).
% 9.18/1.60  fof(f2013,plain,(
% 9.18/1.60    ( ! [X0] : (~r1_tarski(sK0,k1_setfam_1(k2_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0)))) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f42,f1986,f63])).
% 9.18/1.60  fof(f1986,plain,(
% 9.18/1.60    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k2_tarski(X2,X3)),X2)) )),
% 9.18/1.60    inference(superposition,[],[f1812,f65])).
% 9.18/1.60  fof(f1812,plain,(
% 9.18/1.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f1810,f68])).
% 9.18/1.60  fof(f1810,plain,(
% 9.18/1.60    ( ! [X6,X7] : (r1_tarski(X6,k3_tarski(k2_tarski(X7,X6)))) )),
% 9.18/1.60    inference(subsumption_resolution,[],[f1806,f43])).
% 9.18/1.60  fof(f1806,plain,(
% 9.18/1.60    ( ! [X6,X7] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | r1_tarski(X6,k3_tarski(k2_tarski(X7,X6)))) )),
% 9.18/1.60    inference(superposition,[],[f455,f1737])).
% 9.18/1.60  fof(f1737,plain,(
% 9.18/1.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 9.18/1.60    inference(superposition,[],[f1350,f49])).
% 9.18/1.60  fof(f1350,plain,(
% 9.18/1.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f43,f983,f59])).
% 9.18/1.60  fof(f983,plain,(
% 9.18/1.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))),k1_xboole_0)) )),
% 9.18/1.60    inference(unit_resulting_resolution,[],[f64,f456])).
% 9.18/1.60  fof(f456,plain,(
% 9.18/1.60    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X3,X2),k1_xboole_0) | ~r1_tarski(X3,X2)) )),
% 9.18/1.60    inference(superposition,[],[f68,f414])).
% 9.18/1.60  fof(f455,plain,(
% 9.18/1.60    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0) | r1_tarski(X1,X0)) )),
% 9.18/1.60    inference(superposition,[],[f69,f414])).
% 9.18/1.60  fof(f69,plain,(
% 9.18/1.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 9.18/1.60    inference(definition_unfolding,[],[f62,f51])).
% 9.18/1.60  fof(f62,plain,(
% 9.18/1.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 9.18/1.60    inference(cnf_transformation,[],[f33])).
% 9.18/1.60  fof(f33,plain,(
% 9.18/1.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 9.18/1.60    inference(ennf_transformation,[],[f6])).
% 9.18/1.60  fof(f6,axiom,(
% 9.18/1.60    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 9.18/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 9.18/1.60  fof(f42,plain,(
% 9.18/1.60    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 9.18/1.60    inference(cnf_transformation,[],[f37])).
% 9.18/1.60  % SZS output end Proof for theBenchmark
% 9.18/1.60  % (8414)------------------------------
% 9.18/1.60  % (8414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.18/1.60  % (8414)Termination reason: Refutation
% 9.18/1.60  
% 9.18/1.60  % (8414)Memory used [KB]: 16630
% 9.18/1.60  % (8414)Time elapsed: 1.176 s
% 9.18/1.60  % (8414)------------------------------
% 9.18/1.60  % (8414)------------------------------
% 9.18/1.60  % (8402)Success in time 1.23 s
%------------------------------------------------------------------------------
