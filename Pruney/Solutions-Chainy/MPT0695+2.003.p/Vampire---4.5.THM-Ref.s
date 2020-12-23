%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:04 EST 2020

% Result     : Theorem 4.98s
% Output     : Refutation 4.98s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 509 expanded)
%              Number of leaves         :   15 ( 138 expanded)
%              Depth                    :   18
%              Number of atoms          :  167 (1100 expanded)
%              Number of equality atoms :   81 ( 443 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5999,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f5960])).

fof(f5960,plain,(
    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f267,f5702])).

fof(f5702,plain,(
    ! [X37,X38] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X37),X38)) = k1_setfam_1(k1_enumset1(X38,X38,k9_relat_1(sK2,X37))) ),
    inference(forward_demodulation,[],[f5701,f171])).

fof(f171,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(forward_demodulation,[],[f158,f105])).

fof(f105,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0) ),
    inference(backward_demodulation,[],[f90,f97])).

fof(f97,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_funct_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f90,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f35,f57])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f40,f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f158,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(resolution,[],[f147,f32])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(sK2,X1))) = k9_relat_1(X0,k1_relat_1(k7_relat_1(sK2,X1))) ) ),
    inference(resolution,[],[f36,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0) ),
    inference(resolution,[],[f41,f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f5701,plain,(
    ! [X37,X38] : k1_setfam_1(k1_enumset1(X38,X38,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X37))))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X37),X38)) ),
    inference(forward_demodulation,[],[f5662,f627])).

fof(f627,plain,(
    ! [X2,X1] : k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X1))),X2)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1),X2)) ),
    inference(backward_demodulation,[],[f271,f621])).

fof(f621,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(superposition,[],[f370,f253])).

fof(f253,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f54,f32])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f370,plain,(
    ! [X132,X133] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X132,X132,X133))) = k9_relat_1(k7_relat_1(sK2,X132),X133) ),
    inference(forward_demodulation,[],[f322,f98])).

fof(f98,plain,(
    ! [X2,X1] : k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)) = k9_relat_1(k7_relat_1(sK2,X1),X2) ),
    inference(resolution,[],[f42,f57])).

fof(f322,plain,(
    ! [X132,X133] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X132,X132,X133))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X132),X133)) ),
    inference(superposition,[],[f97,f280])).

fof(f280,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(resolution,[],[f55,f32])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f271,plain,(
    ! [X2,X1] : k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(sK2,X2)) = k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X1))),X2)) ),
    inference(superposition,[],[f186,f253])).

fof(f186,plain,(
    ! [X2,X1] : k9_relat_1(k7_relat_1(sK2,X1),X2) = k9_relat_1(k7_relat_1(sK2,X1),k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(sK2,X1)),k1_relat_1(k7_relat_1(sK2,X1)),X2))) ),
    inference(resolution,[],[f52,f57])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(f5662,plain,(
    ! [X37,X38] : k1_setfam_1(k1_enumset1(X38,X38,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X37))))) = k9_relat_1(k7_relat_1(sK2,X37),k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X37))),X38)) ),
    inference(superposition,[],[f5554,f999])).

fof(f999,plain,(
    ! [X2,X1] : k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(sK2,X1))) ),
    inference(forward_demodulation,[],[f998,f105])).

fof(f998,plain,(
    ! [X2,X1] : k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1))))) ),
    inference(subsumption_resolution,[],[f983,f57])).

fof(f983,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1)))))
      | ~ v1_relat_1(k7_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f53,f72])).

fof(f72,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK2,X0)) ),
    inference(subsumption_resolution,[],[f71,f32])).

fof(f71,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK2,X0))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f5554,plain,(
    ! [X12,X13] : k9_relat_1(k7_relat_1(sK2,X13),X12) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X13))),X12) ),
    inference(superposition,[],[f5480,f611])).

fof(f611,plain,(
    ! [X2,X3] : k9_relat_1(k7_relat_1(sK2,X2),X3) = k9_relat_1(k7_relat_1(sK2,X3),X2) ),
    inference(superposition,[],[f507,f98])).

fof(f507,plain,(
    ! [X105,X106] : k9_relat_1(k7_relat_1(sK2,X105),X106) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X106),X105)) ),
    inference(superposition,[],[f98,f401])).

fof(f401,plain,(
    ! [X2,X3] : k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2) ),
    inference(superposition,[],[f294,f280])).

fof(f294,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f280,f51])).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f37,f38,f38])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f5480,plain,(
    ! [X282,X283] : k9_relat_1(k7_relat_1(sK2,X282),k1_relat_1(k7_relat_1(sK2,X283))) = k9_relat_1(k7_relat_1(sK2,X283),X282) ),
    inference(backward_demodulation,[],[f528,f5451])).

fof(f5451,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(superposition,[],[f2697,f186])).

fof(f2697,plain,(
    ! [X142,X140,X141] : k9_relat_1(k7_relat_1(sK2,X140),k1_setfam_1(k1_enumset1(X141,X141,X142))) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X140),X142),X141) ),
    inference(forward_demodulation,[],[f2590,f99])).

fof(f99,plain,(
    ! [X4,X5,X3] : k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4),X5)) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4),X5) ),
    inference(resolution,[],[f42,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(resolution,[],[f57,f40])).

fof(f2590,plain,(
    ! [X142,X140,X141] : k9_relat_1(k7_relat_1(sK2,X140),k1_setfam_1(k1_enumset1(X141,X141,X142))) = k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X140),X142),X141)) ),
    inference(superposition,[],[f98,f1551])).

fof(f1551,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X0),X1) = k7_relat_1(k7_relat_1(sK2,X2),k1_setfam_1(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f281,f51])).

fof(f281,plain,(
    ! [X4,X2,X3] : k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3),X4) = k7_relat_1(k7_relat_1(sK2,X2),k1_setfam_1(k1_enumset1(X3,X3,X4))) ),
    inference(resolution,[],[f55,f57])).

fof(f528,plain,(
    ! [X282,X283] : k9_relat_1(k7_relat_1(sK2,X282),k1_relat_1(k7_relat_1(sK2,X283))) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X283),X282),k1_relat_1(k7_relat_1(sK2,X283))) ),
    inference(superposition,[],[f159,f401])).

fof(f159,plain,(
    ! [X2,X1] : k9_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2),k1_relat_1(k7_relat_1(sK2,X2))) = k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X2))) ),
    inference(resolution,[],[f147,f57])).

fof(f267,plain,(
    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(backward_demodulation,[],[f56,f253])).

fof(f56,plain,(
    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(backward_demodulation,[],[f50,f51])).

fof(f50,plain,(
    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) ),
    inference(definition_unfolding,[],[f34,f49,f49])).

fof(f34,plain,(
    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n004.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 19:41:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (17459)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.44  % (17467)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.44  % (17461)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.45  % (17456)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (17465)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (17457)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (17458)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (17460)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (17466)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (17464)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (17470)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (17462)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (17469)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (17455)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (17468)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (17472)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (17463)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (17471)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 4.98/0.99  % (17468)Refutation found. Thanks to Tanya!
% 4.98/0.99  % SZS status Theorem for theBenchmark
% 4.98/0.99  % SZS output start Proof for theBenchmark
% 4.98/0.99  fof(f5999,plain,(
% 4.98/0.99    $false),
% 4.98/0.99    inference(trivial_inequality_removal,[],[f5960])).
% 4.98/0.99  fof(f5960,plain,(
% 4.98/0.99    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))),
% 4.98/0.99    inference(superposition,[],[f267,f5702])).
% 4.98/0.99  fof(f5702,plain,(
% 4.98/0.99    ( ! [X37,X38] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X37),X38)) = k1_setfam_1(k1_enumset1(X38,X38,k9_relat_1(sK2,X37)))) )),
% 4.98/0.99    inference(forward_demodulation,[],[f5701,f171])).
% 4.98/0.99  fof(f171,plain,(
% 4.98/0.99    ( ! [X0] : (k9_relat_1(sK2,X0) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) )),
% 4.98/0.99    inference(forward_demodulation,[],[f158,f105])).
% 4.98/0.99  fof(f105,plain,(
% 4.98/0.99    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0)) )),
% 4.98/0.99    inference(backward_demodulation,[],[f90,f97])).
% 4.98/0.99  fof(f97,plain,(
% 4.98/0.99    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 4.98/0.99    inference(resolution,[],[f42,f32])).
% 4.98/0.99  fof(f32,plain,(
% 4.98/0.99    v1_relat_1(sK2)),
% 4.98/0.99    inference(cnf_transformation,[],[f31])).
% 4.98/0.99  fof(f31,plain,(
% 4.98/0.99    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 4.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f30])).
% 4.98/0.99  fof(f30,plain,(
% 4.98/0.99    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 4.98/0.99    introduced(choice_axiom,[])).
% 4.98/0.99  fof(f17,plain,(
% 4.98/0.99    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 4.98/0.99    inference(flattening,[],[f16])).
% 4.98/0.99  fof(f16,plain,(
% 4.98/0.99    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 4.98/0.99    inference(ennf_transformation,[],[f15])).
% 4.98/0.99  fof(f15,negated_conjecture,(
% 4.98/0.99    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 4.98/0.99    inference(negated_conjecture,[],[f14])).
% 4.98/0.99  fof(f14,conjecture,(
% 4.98/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_funct_1)).
% 4.98/0.99  fof(f42,plain,(
% 4.98/0.99    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 4.98/0.99    inference(cnf_transformation,[],[f22])).
% 4.98/0.99  fof(f22,plain,(
% 4.98/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 4.98/0.99    inference(ennf_transformation,[],[f8])).
% 4.98/0.99  fof(f8,axiom,(
% 4.98/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 4.98/0.99  fof(f90,plain,(
% 4.98/0.99    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0))) )),
% 4.98/0.99    inference(resolution,[],[f35,f57])).
% 4.98/0.99  fof(f57,plain,(
% 4.98/0.99    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 4.98/0.99    inference(resolution,[],[f40,f32])).
% 4.98/0.99  fof(f40,plain,(
% 4.98/0.99    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 4.98/0.99    inference(cnf_transformation,[],[f20])).
% 4.98/0.99  fof(f20,plain,(
% 4.98/0.99    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 4.98/0.99    inference(ennf_transformation,[],[f4])).
% 4.98/0.99  fof(f4,axiom,(
% 4.98/0.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 4.98/0.99  fof(f35,plain,(
% 4.98/0.99    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 4.98/0.99    inference(cnf_transformation,[],[f18])).
% 4.98/0.99  fof(f18,plain,(
% 4.98/0.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 4.98/0.99    inference(ennf_transformation,[],[f7])).
% 4.98/0.99  fof(f7,axiom,(
% 4.98/0.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 4.98/0.99  fof(f158,plain,(
% 4.98/0.99    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) )),
% 4.98/0.99    inference(resolution,[],[f147,f32])).
% 4.98/0.99  fof(f147,plain,(
% 4.98/0.99    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(sK2,X1))) = k9_relat_1(X0,k1_relat_1(k7_relat_1(sK2,X1)))) )),
% 4.98/0.99    inference(resolution,[],[f36,f64])).
% 4.98/0.99  fof(f64,plain,(
% 4.98/0.99    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)) )),
% 4.98/0.99    inference(resolution,[],[f41,f32])).
% 4.98/0.99  fof(f41,plain,(
% 4.98/0.99    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 4.98/0.99    inference(cnf_transformation,[],[f21])).
% 4.98/0.99  fof(f21,plain,(
% 4.98/0.99    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 4.98/0.99    inference(ennf_transformation,[],[f10])).
% 4.98/0.99  fof(f10,axiom,(
% 4.98/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 4.98/0.99  fof(f36,plain,(
% 4.98/0.99    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 4.98/0.99    inference(cnf_transformation,[],[f19])).
% 4.98/0.99  fof(f19,plain,(
% 4.98/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 4.98/0.99    inference(ennf_transformation,[],[f9])).
% 4.98/0.99  fof(f9,axiom,(
% 4.98/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 4.98/0.99  fof(f5701,plain,(
% 4.98/0.99    ( ! [X37,X38] : (k1_setfam_1(k1_enumset1(X38,X38,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X37))))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X37),X38))) )),
% 4.98/0.99    inference(forward_demodulation,[],[f5662,f627])).
% 4.98/0.99  fof(f627,plain,(
% 4.98/0.99    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X1))),X2)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1),X2))) )),
% 4.98/0.99    inference(backward_demodulation,[],[f271,f621])).
% 4.98/0.99  fof(f621,plain,(
% 4.98/0.99    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1))) )),
% 4.98/0.99    inference(superposition,[],[f370,f253])).
% 4.98/0.99  fof(f253,plain,(
% 4.98/0.99    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))) )),
% 4.98/0.99    inference(resolution,[],[f54,f32])).
% 4.98/0.99  fof(f54,plain,(
% 4.98/0.99    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1)))) )),
% 4.98/0.99    inference(definition_unfolding,[],[f47,f49])).
% 4.98/0.99  fof(f49,plain,(
% 4.98/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 4.98/0.99    inference(definition_unfolding,[],[f39,f38])).
% 4.98/0.99  fof(f38,plain,(
% 4.98/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.98/0.99    inference(cnf_transformation,[],[f2])).
% 4.98/0.99  fof(f2,axiom,(
% 4.98/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 4.98/0.99  fof(f39,plain,(
% 4.98/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 4.98/0.99    inference(cnf_transformation,[],[f3])).
% 4.98/0.99  fof(f3,axiom,(
% 4.98/0.99    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 4.98/0.99  fof(f47,plain,(
% 4.98/0.99    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.98/0.99    inference(cnf_transformation,[],[f28])).
% 4.98/0.99  fof(f28,plain,(
% 4.98/0.99    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 4.98/0.99    inference(ennf_transformation,[],[f12])).
% 4.98/0.99  fof(f12,axiom,(
% 4.98/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 4.98/0.99  fof(f370,plain,(
% 4.98/0.99    ( ! [X132,X133] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X132,X132,X133))) = k9_relat_1(k7_relat_1(sK2,X132),X133)) )),
% 4.98/0.99    inference(forward_demodulation,[],[f322,f98])).
% 4.98/0.99  fof(f98,plain,(
% 4.98/0.99    ( ! [X2,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)) = k9_relat_1(k7_relat_1(sK2,X1),X2)) )),
% 4.98/0.99    inference(resolution,[],[f42,f57])).
% 4.98/0.99  fof(f322,plain,(
% 4.98/0.99    ( ! [X132,X133] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X132,X132,X133))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X132),X133))) )),
% 4.98/0.99    inference(superposition,[],[f97,f280])).
% 4.98/0.99  fof(f280,plain,(
% 4.98/0.99    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 4.98/0.99    inference(resolution,[],[f55,f32])).
% 4.98/0.99  fof(f55,plain,(
% 4.98/0.99    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 4.98/0.99    inference(definition_unfolding,[],[f48,f49])).
% 4.98/0.99  fof(f48,plain,(
% 4.98/0.99    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 4.98/0.99    inference(cnf_transformation,[],[f29])).
% 4.98/0.99  fof(f29,plain,(
% 4.98/0.99    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 4.98/0.99    inference(ennf_transformation,[],[f5])).
% 4.98/0.99  fof(f5,axiom,(
% 4.98/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 4.98/0.99  fof(f271,plain,(
% 4.98/0.99    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(sK2,X2)) = k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X1))),X2))) )),
% 4.98/0.99    inference(superposition,[],[f186,f253])).
% 4.98/0.99  fof(f186,plain,(
% 4.98/0.99    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),X2) = k9_relat_1(k7_relat_1(sK2,X1),k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(sK2,X1)),k1_relat_1(k7_relat_1(sK2,X1)),X2)))) )),
% 4.98/0.99    inference(resolution,[],[f52,f57])).
% 4.98/0.99  fof(f52,plain,(
% 4.98/0.99    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)))) )),
% 4.98/0.99    inference(definition_unfolding,[],[f43,f49])).
% 4.98/0.99  fof(f43,plain,(
% 4.98/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 4.98/0.99    inference(cnf_transformation,[],[f23])).
% 4.98/0.99  fof(f23,plain,(
% 4.98/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.98/0.99    inference(ennf_transformation,[],[f6])).
% 4.98/0.99  fof(f6,axiom,(
% 4.98/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).
% 4.98/0.99  fof(f5662,plain,(
% 4.98/0.99    ( ! [X37,X38] : (k1_setfam_1(k1_enumset1(X38,X38,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X37))))) = k9_relat_1(k7_relat_1(sK2,X37),k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X37))),X38))) )),
% 4.98/0.99    inference(superposition,[],[f5554,f999])).
% 4.98/0.99  fof(f999,plain,(
% 4.98/0.99    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(sK2,X1)))) )),
% 4.98/0.99    inference(forward_demodulation,[],[f998,f105])).
% 4.98/0.99  fof(f998,plain,(
% 4.98/0.99    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1)))))) )),
% 4.98/0.99    inference(subsumption_resolution,[],[f983,f57])).
% 4.98/0.99  fof(f983,plain,(
% 4.98/0.99    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1))))) | ~v1_relat_1(k7_relat_1(sK2,X1))) )),
% 4.98/0.99    inference(resolution,[],[f53,f72])).
% 4.98/0.99  fof(f72,plain,(
% 4.98/0.99    ( ! [X0] : (v1_funct_1(k7_relat_1(sK2,X0))) )),
% 4.98/0.99    inference(subsumption_resolution,[],[f71,f32])).
% 4.98/0.99  fof(f71,plain,(
% 4.98/0.99    ( ! [X0] : (v1_funct_1(k7_relat_1(sK2,X0)) | ~v1_relat_1(sK2)) )),
% 4.98/0.99    inference(resolution,[],[f46,f33])).
% 4.98/0.99  fof(f33,plain,(
% 4.98/0.99    v1_funct_1(sK2)),
% 4.98/0.99    inference(cnf_transformation,[],[f31])).
% 4.98/0.99  fof(f46,plain,(
% 4.98/0.99    ( ! [X0,X1] : (~v1_funct_1(X0) | v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.98/0.99    inference(cnf_transformation,[],[f27])).
% 4.98/0.99  fof(f27,plain,(
% 4.98/0.99    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.98/0.99    inference(flattening,[],[f26])).
% 4.98/0.99  fof(f26,plain,(
% 4.98/0.99    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.98/0.99    inference(ennf_transformation,[],[f11])).
% 4.98/0.99  fof(f11,axiom,(
% 4.98/0.99    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 4.98/0.99  fof(f53,plain,(
% 4.98/0.99    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 4.98/0.99    inference(definition_unfolding,[],[f44,f49])).
% 4.98/0.99  fof(f44,plain,(
% 4.98/0.99    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.98/0.99    inference(cnf_transformation,[],[f25])).
% 4.98/0.99  fof(f25,plain,(
% 4.98/0.99    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.98/0.99    inference(flattening,[],[f24])).
% 4.98/0.99  fof(f24,plain,(
% 4.98/0.99    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.98/0.99    inference(ennf_transformation,[],[f13])).
% 4.98/0.99  fof(f13,axiom,(
% 4.98/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 4.98/0.99  fof(f5554,plain,(
% 4.98/0.99    ( ! [X12,X13] : (k9_relat_1(k7_relat_1(sK2,X13),X12) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X13))),X12)) )),
% 4.98/0.99    inference(superposition,[],[f5480,f611])).
% 4.98/0.99  fof(f611,plain,(
% 4.98/0.99    ( ! [X2,X3] : (k9_relat_1(k7_relat_1(sK2,X2),X3) = k9_relat_1(k7_relat_1(sK2,X3),X2)) )),
% 4.98/0.99    inference(superposition,[],[f507,f98])).
% 4.98/0.99  fof(f507,plain,(
% 4.98/0.99    ( ! [X105,X106] : (k9_relat_1(k7_relat_1(sK2,X105),X106) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X106),X105))) )),
% 4.98/0.99    inference(superposition,[],[f98,f401])).
% 4.98/0.99  fof(f401,plain,(
% 4.98/0.99    ( ! [X2,X3] : (k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2)) )),
% 4.98/0.99    inference(superposition,[],[f294,f280])).
% 4.98/0.99  fof(f294,plain,(
% 4.98/0.99    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X1,X1,X0)))) )),
% 4.98/0.99    inference(superposition,[],[f280,f51])).
% 4.98/0.99  fof(f51,plain,(
% 4.98/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 4.98/0.99    inference(definition_unfolding,[],[f37,f38,f38])).
% 4.98/0.99  fof(f37,plain,(
% 4.98/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.98/0.99    inference(cnf_transformation,[],[f1])).
% 4.98/0.99  fof(f1,axiom,(
% 4.98/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 4.98/0.99  fof(f5480,plain,(
% 4.98/0.99    ( ! [X282,X283] : (k9_relat_1(k7_relat_1(sK2,X282),k1_relat_1(k7_relat_1(sK2,X283))) = k9_relat_1(k7_relat_1(sK2,X283),X282)) )),
% 4.98/0.99    inference(backward_demodulation,[],[f528,f5451])).
% 4.98/0.99  fof(f5451,plain,(
% 4.98/0.99    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),k1_relat_1(k7_relat_1(sK2,X0)))) )),
% 4.98/0.99    inference(superposition,[],[f2697,f186])).
% 4.98/0.99  fof(f2697,plain,(
% 4.98/0.99    ( ! [X142,X140,X141] : (k9_relat_1(k7_relat_1(sK2,X140),k1_setfam_1(k1_enumset1(X141,X141,X142))) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X140),X142),X141)) )),
% 4.98/0.99    inference(forward_demodulation,[],[f2590,f99])).
% 4.98/0.99  fof(f99,plain,(
% 4.98/0.99    ( ! [X4,X5,X3] : (k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4),X5)) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4),X5)) )),
% 4.98/0.99    inference(resolution,[],[f42,f58])).
% 4.98/0.99  fof(f58,plain,(
% 4.98/0.99    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) )),
% 4.98/0.99    inference(resolution,[],[f57,f40])).
% 4.98/0.99  fof(f2590,plain,(
% 4.98/0.99    ( ! [X142,X140,X141] : (k9_relat_1(k7_relat_1(sK2,X140),k1_setfam_1(k1_enumset1(X141,X141,X142))) = k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X140),X142),X141))) )),
% 4.98/0.99    inference(superposition,[],[f98,f1551])).
% 4.98/0.99  fof(f1551,plain,(
% 4.98/0.99    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X0),X1) = k7_relat_1(k7_relat_1(sK2,X2),k1_setfam_1(k1_enumset1(X1,X1,X0)))) )),
% 4.98/0.99    inference(superposition,[],[f281,f51])).
% 4.98/0.99  fof(f281,plain,(
% 4.98/0.99    ( ! [X4,X2,X3] : (k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3),X4) = k7_relat_1(k7_relat_1(sK2,X2),k1_setfam_1(k1_enumset1(X3,X3,X4)))) )),
% 4.98/0.99    inference(resolution,[],[f55,f57])).
% 4.98/0.99  fof(f528,plain,(
% 4.98/0.99    ( ! [X282,X283] : (k9_relat_1(k7_relat_1(sK2,X282),k1_relat_1(k7_relat_1(sK2,X283))) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X283),X282),k1_relat_1(k7_relat_1(sK2,X283)))) )),
% 4.98/0.99    inference(superposition,[],[f159,f401])).
% 4.98/0.99  fof(f159,plain,(
% 4.98/0.99    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2),k1_relat_1(k7_relat_1(sK2,X2))) = k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X2)))) )),
% 4.98/0.99    inference(resolution,[],[f147,f57])).
% 4.98/0.99  fof(f267,plain,(
% 4.98/0.99    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))),
% 4.98/0.99    inference(backward_demodulation,[],[f56,f253])).
% 4.98/0.99  fof(f56,plain,(
% 4.98/0.99    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))),
% 4.98/0.99    inference(backward_demodulation,[],[f50,f51])).
% 4.98/0.99  fof(f50,plain,(
% 4.98/0.99    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))),
% 4.98/0.99    inference(definition_unfolding,[],[f34,f49,f49])).
% 4.98/0.99  fof(f34,plain,(
% 4.98/0.99    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)),
% 4.98/0.99    inference(cnf_transformation,[],[f31])).
% 4.98/0.99  % SZS output end Proof for theBenchmark
% 4.98/0.99  % (17468)------------------------------
% 4.98/0.99  % (17468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.98/0.99  % (17468)Termination reason: Refutation
% 4.98/0.99  
% 4.98/0.99  % (17468)Memory used [KB]: 7803
% 4.98/0.99  % (17468)Time elapsed: 0.570 s
% 4.98/0.99  % (17468)------------------------------
% 4.98/0.99  % (17468)------------------------------
% 4.98/0.99  % (17454)Success in time 0.643 s
%------------------------------------------------------------------------------
