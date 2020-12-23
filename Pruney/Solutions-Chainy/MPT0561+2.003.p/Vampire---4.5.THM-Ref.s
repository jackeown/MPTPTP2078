%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:02 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 242 expanded)
%              Number of leaves         :   17 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  150 ( 454 expanded)
%              Number of equality atoms :   47 (  81 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4456,plain,(
    $false ),
    inference(resolution,[],[f4447,f1734])).

fof(f1734,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f696,f1730])).

fof(f1730,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(X1,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X1)) ),
    inference(superposition,[],[f1724,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f45,f46,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1724,plain,(
    ! [X676] : k1_relat_1(k7_relat_1(sK1,X676)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X676)) ),
    inference(resolution,[],[f54,f33])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f696,plain,(
    ~ r1_tarski(k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f52,f53])).

fof(f52,plain,(
    ~ r1_tarski(k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f34,f46])).

fof(f34,plain,(
    ~ r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f4447,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1))) ),
    inference(forward_demodulation,[],[f4446,f3337])).

fof(f3337,plain,(
    ! [X40] : k9_relat_1(k4_relat_1(sK1),X40) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X40))) ),
    inference(backward_demodulation,[],[f1146,f3308])).

fof(f3308,plain,(
    ! [X299] : k5_relat_1(sK1,k6_relat_1(X299)) = k4_relat_1(k7_relat_1(k4_relat_1(sK1),X299)) ),
    inference(forward_demodulation,[],[f3307,f816])).

fof(f816,plain,(
    ! [X0] : k7_relat_1(k4_relat_1(sK1),X0) = k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) ),
    inference(resolution,[],[f48,f55])).

fof(f55,plain,(
    v1_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f37,f33])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f3307,plain,(
    ! [X299] : k4_relat_1(k5_relat_1(k6_relat_1(X299),k4_relat_1(sK1))) = k5_relat_1(sK1,k6_relat_1(X299)) ),
    inference(forward_demodulation,[],[f3219,f36])).

fof(f36,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f3219,plain,(
    ! [X299] : k4_relat_1(k5_relat_1(k6_relat_1(X299),k4_relat_1(sK1))) = k5_relat_1(sK1,k4_relat_1(k6_relat_1(X299))) ),
    inference(resolution,[],[f2695,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f2695,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,k4_relat_1(sK1))) = k5_relat_1(sK1,k4_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f2516,f122])).

fof(f122,plain,(
    sK1 = k4_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f38,f33])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f2516,plain,(
    ! [X0] :
      ( k4_relat_1(k5_relat_1(X0,k4_relat_1(sK1))) = k5_relat_1(k4_relat_1(k4_relat_1(sK1)),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f42,f55])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f1146,plain,(
    ! [X40] : k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X40))) = k9_relat_1(k4_relat_1(sK1),X40) ),
    inference(backward_demodulation,[],[f277,f1038])).

fof(f1038,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) = k9_relat_1(k4_relat_1(sK1),X0) ),
    inference(resolution,[],[f49,f55])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f277,plain,(
    ! [X40] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X40)) = k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X40))) ),
    inference(resolution,[],[f40,f70])).

fof(f70,plain,(
    ! [X3] : v1_relat_1(k7_relat_1(k4_relat_1(sK1),X3)) ),
    inference(resolution,[],[f47,f55])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f4446,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1))))) ),
    inference(subsumption_resolution,[],[f4445,f68])).

fof(f68,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f47,f33])).

fof(f4445,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1)))))
      | ~ v1_relat_1(k7_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f4438,f3309])).

fof(f3309,plain,(
    ! [X2] : v1_relat_1(k5_relat_1(sK1,k6_relat_1(X2))) ),
    inference(backward_demodulation,[],[f79,f3308])).

fof(f79,plain,(
    ! [X2] : v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2))) ),
    inference(resolution,[],[f70,f37])).

fof(f4438,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1)))))
      | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1))))
      | ~ v1_relat_1(k7_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f4397,f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f4397,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0)))) ),
    inference(superposition,[],[f4391,f1144])).

fof(f1144,plain,(
    ! [X85] : k7_relat_1(sK1,X85) = k5_relat_1(k7_relat_1(sK1,X85),k6_relat_1(k9_relat_1(sK1,X85))) ),
    inference(backward_demodulation,[],[f550,f1143])).

fof(f1143,plain,(
    ! [X429] : k2_relat_1(k7_relat_1(sK1,X429)) = k9_relat_1(sK1,X429) ),
    inference(resolution,[],[f49,f33])).

fof(f550,plain,(
    ! [X85] : k7_relat_1(sK1,X85) = k5_relat_1(k7_relat_1(sK1,X85),k6_relat_1(k2_relat_1(k7_relat_1(sK1,X85)))) ),
    inference(resolution,[],[f39,f68])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f4391,plain,(
    ! [X1000,X1001] : r1_tarski(k5_relat_1(k7_relat_1(sK1,X1000),k6_relat_1(X1001)),k5_relat_1(sK1,k6_relat_1(X1001))) ),
    inference(resolution,[],[f1917,f33])).

fof(f1917,plain,(
    ! [X445,X443,X444] :
      ( ~ v1_relat_1(X443)
      | r1_tarski(k5_relat_1(k7_relat_1(X443,X444),k6_relat_1(X445)),k5_relat_1(X443,k6_relat_1(X445))) ) ),
    inference(resolution,[],[f51,f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:19:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (4894)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (4904)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (4905)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (4893)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (4892)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (4897)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (4907)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (4896)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (4908)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (4899)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (4898)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (4895)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (4901)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (4903)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (4909)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (4906)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (4902)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (4900)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.59/0.60  % (4904)Refutation found. Thanks to Tanya!
% 1.59/0.60  % SZS status Theorem for theBenchmark
% 1.59/0.60  % SZS output start Proof for theBenchmark
% 1.59/0.60  fof(f4456,plain,(
% 1.59/0.60    $false),
% 1.59/0.60    inference(resolution,[],[f4447,f1734])).
% 1.59/0.60  fof(f1734,plain,(
% 1.59/0.60    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 1.59/0.60    inference(backward_demodulation,[],[f696,f1730])).
% 1.59/0.60  fof(f1730,plain,(
% 1.59/0.60    ( ! [X1] : (k1_setfam_1(k2_tarski(X1,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X1))) )),
% 1.59/0.60    inference(superposition,[],[f1724,f53])).
% 1.59/0.60  fof(f53,plain,(
% 1.59/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.59/0.60    inference(definition_unfolding,[],[f45,f46,f46])).
% 1.59/0.60  fof(f46,plain,(
% 1.59/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.59/0.60    inference(cnf_transformation,[],[f2])).
% 1.59/0.60  fof(f2,axiom,(
% 1.59/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.59/0.60  fof(f45,plain,(
% 1.59/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f1])).
% 1.59/0.60  fof(f1,axiom,(
% 1.59/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.59/0.60  fof(f1724,plain,(
% 1.59/0.60    ( ! [X676] : (k1_relat_1(k7_relat_1(sK1,X676)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X676))) )),
% 1.59/0.60    inference(resolution,[],[f54,f33])).
% 1.59/0.60  fof(f33,plain,(
% 1.59/0.60    v1_relat_1(sK1)),
% 1.59/0.60    inference(cnf_transformation,[],[f32])).
% 1.59/0.60  fof(f32,plain,(
% 1.59/0.60    ~r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 1.59/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f31])).
% 1.59/0.60  fof(f31,plain,(
% 1.59/0.60    ? [X0,X1] : (~r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) & v1_relat_1(X1)) => (~r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 1.59/0.60    introduced(choice_axiom,[])).
% 1.59/0.60  fof(f18,plain,(
% 1.59/0.60    ? [X0,X1] : (~r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.59/0.60    inference(ennf_transformation,[],[f17])).
% 1.59/0.60  fof(f17,negated_conjecture,(
% 1.59/0.60    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))))),
% 1.59/0.60    inference(negated_conjecture,[],[f16])).
% 1.59/0.60  fof(f16,conjecture,(
% 1.59/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).
% 1.59/0.60  fof(f54,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 1.59/0.60    inference(definition_unfolding,[],[f50,f46])).
% 1.59/0.60  fof(f50,plain,(
% 1.59/0.60    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f29])).
% 1.59/0.60  fof(f29,plain,(
% 1.59/0.60    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.59/0.60    inference(ennf_transformation,[],[f13])).
% 1.59/0.60  fof(f13,axiom,(
% 1.59/0.60    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.59/0.60  fof(f696,plain,(
% 1.59/0.60    ~r1_tarski(k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 1.59/0.60    inference(backward_demodulation,[],[f52,f53])).
% 1.59/0.60  fof(f52,plain,(
% 1.59/0.60    ~r1_tarski(k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 1.59/0.60    inference(definition_unfolding,[],[f34,f46])).
% 1.59/0.60  fof(f34,plain,(
% 1.59/0.60    ~r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 1.59/0.60    inference(cnf_transformation,[],[f32])).
% 1.59/0.60  fof(f4447,plain,(
% 1.59/0.60    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X1)))) )),
% 1.59/0.60    inference(forward_demodulation,[],[f4446,f3337])).
% 1.59/0.60  fof(f3337,plain,(
% 1.59/0.60    ( ! [X40] : (k9_relat_1(k4_relat_1(sK1),X40) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X40)))) )),
% 1.59/0.60    inference(backward_demodulation,[],[f1146,f3308])).
% 1.59/0.60  fof(f3308,plain,(
% 1.59/0.60    ( ! [X299] : (k5_relat_1(sK1,k6_relat_1(X299)) = k4_relat_1(k7_relat_1(k4_relat_1(sK1),X299))) )),
% 1.59/0.60    inference(forward_demodulation,[],[f3307,f816])).
% 1.59/0.60  fof(f816,plain,(
% 1.59/0.60    ( ! [X0] : (k7_relat_1(k4_relat_1(sK1),X0) = k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1))) )),
% 1.59/0.60    inference(resolution,[],[f48,f55])).
% 1.59/0.60  fof(f55,plain,(
% 1.59/0.60    v1_relat_1(k4_relat_1(sK1))),
% 1.59/0.60    inference(resolution,[],[f37,f33])).
% 1.59/0.60  fof(f37,plain,(
% 1.59/0.60    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 1.59/0.60    inference(cnf_transformation,[],[f19])).
% 1.59/0.60  fof(f19,plain,(
% 1.59/0.60    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.59/0.60    inference(ennf_transformation,[],[f3])).
% 1.59/0.60  fof(f3,axiom,(
% 1.59/0.60    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.59/0.60  fof(f48,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f27])).
% 1.59/0.60  fof(f27,plain,(
% 1.59/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.59/0.60    inference(ennf_transformation,[],[f15])).
% 1.59/0.60  fof(f15,axiom,(
% 1.59/0.60    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.59/0.60  fof(f3307,plain,(
% 1.59/0.60    ( ! [X299] : (k4_relat_1(k5_relat_1(k6_relat_1(X299),k4_relat_1(sK1))) = k5_relat_1(sK1,k6_relat_1(X299))) )),
% 1.59/0.60    inference(forward_demodulation,[],[f3219,f36])).
% 1.59/0.60  fof(f36,plain,(
% 1.59/0.60    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.59/0.60    inference(cnf_transformation,[],[f11])).
% 1.59/0.60  fof(f11,axiom,(
% 1.59/0.60    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 1.59/0.60  fof(f3219,plain,(
% 1.59/0.60    ( ! [X299] : (k4_relat_1(k5_relat_1(k6_relat_1(X299),k4_relat_1(sK1))) = k5_relat_1(sK1,k4_relat_1(k6_relat_1(X299)))) )),
% 1.59/0.60    inference(resolution,[],[f2695,f35])).
% 1.59/0.60  fof(f35,plain,(
% 1.59/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.59/0.60    inference(cnf_transformation,[],[f4])).
% 1.59/0.60  fof(f4,axiom,(
% 1.59/0.60    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.59/0.60  fof(f2695,plain,(
% 1.59/0.60    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,k4_relat_1(sK1))) = k5_relat_1(sK1,k4_relat_1(X0))) )),
% 1.59/0.60    inference(forward_demodulation,[],[f2516,f122])).
% 1.59/0.60  fof(f122,plain,(
% 1.59/0.60    sK1 = k4_relat_1(k4_relat_1(sK1))),
% 1.59/0.60    inference(resolution,[],[f38,f33])).
% 1.59/0.60  fof(f38,plain,(
% 1.59/0.60    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 1.59/0.60    inference(cnf_transformation,[],[f20])).
% 1.59/0.60  fof(f20,plain,(
% 1.59/0.60    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.59/0.60    inference(ennf_transformation,[],[f6])).
% 1.59/0.60  fof(f6,axiom,(
% 1.59/0.60    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.59/0.60  fof(f2516,plain,(
% 1.59/0.60    ( ! [X0] : (k4_relat_1(k5_relat_1(X0,k4_relat_1(sK1))) = k5_relat_1(k4_relat_1(k4_relat_1(sK1)),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.59/0.60    inference(resolution,[],[f42,f55])).
% 1.59/0.60  fof(f42,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f23])).
% 1.59/0.60  fof(f23,plain,(
% 1.59/0.60    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.59/0.60    inference(ennf_transformation,[],[f10])).
% 1.59/0.60  fof(f10,axiom,(
% 1.59/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 1.59/0.60  fof(f1146,plain,(
% 1.59/0.60    ( ! [X40] : (k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X40))) = k9_relat_1(k4_relat_1(sK1),X40)) )),
% 1.59/0.60    inference(backward_demodulation,[],[f277,f1038])).
% 1.59/0.60  fof(f1038,plain,(
% 1.59/0.60    ( ! [X0] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) = k9_relat_1(k4_relat_1(sK1),X0)) )),
% 1.59/0.60    inference(resolution,[],[f49,f55])).
% 1.59/0.60  fof(f49,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f28])).
% 1.59/0.60  fof(f28,plain,(
% 1.59/0.60    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.59/0.60    inference(ennf_transformation,[],[f7])).
% 1.59/0.60  fof(f7,axiom,(
% 1.59/0.60    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.59/0.60  fof(f277,plain,(
% 1.59/0.60    ( ! [X40] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X40)) = k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X40)))) )),
% 1.59/0.60    inference(resolution,[],[f40,f70])).
% 1.59/0.60  fof(f70,plain,(
% 1.59/0.60    ( ! [X3] : (v1_relat_1(k7_relat_1(k4_relat_1(sK1),X3))) )),
% 1.59/0.60    inference(resolution,[],[f47,f55])).
% 1.59/0.60  fof(f47,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.59/0.60    inference(cnf_transformation,[],[f26])).
% 1.59/0.60  fof(f26,plain,(
% 1.59/0.60    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.59/0.60    inference(ennf_transformation,[],[f5])).
% 1.59/0.60  fof(f5,axiom,(
% 1.59/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.59/0.60  fof(f40,plain,(
% 1.59/0.60    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.59/0.60    inference(cnf_transformation,[],[f22])).
% 1.59/0.60  fof(f22,plain,(
% 1.59/0.60    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.59/0.60    inference(ennf_transformation,[],[f9])).
% 1.59/0.60  fof(f9,axiom,(
% 1.59/0.60    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 1.59/0.60  fof(f4446,plain,(
% 1.59/0.60    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1)))))) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f4445,f68])).
% 1.59/0.60  fof(f68,plain,(
% 1.59/0.60    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.59/0.60    inference(resolution,[],[f47,f33])).
% 1.59/0.60  fof(f4445,plain,(
% 1.59/0.60    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1))))) | ~v1_relat_1(k7_relat_1(sK1,X1))) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f4438,f3309])).
% 1.59/0.60  fof(f3309,plain,(
% 1.59/0.60    ( ! [X2] : (v1_relat_1(k5_relat_1(sK1,k6_relat_1(X2)))) )),
% 1.59/0.60    inference(backward_demodulation,[],[f79,f3308])).
% 1.59/0.60  fof(f79,plain,(
% 1.59/0.60    ( ! [X2] : (v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(sK1),X2)))) )),
% 1.59/0.60    inference(resolution,[],[f70,f37])).
% 1.59/0.60  fof(f4438,plain,(
% 1.59/0.60    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1))))) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X1)))) | ~v1_relat_1(k7_relat_1(sK1,X1))) )),
% 1.59/0.60    inference(resolution,[],[f4397,f43])).
% 1.59/0.60  fof(f43,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f25])).
% 1.59/0.60  fof(f25,plain,(
% 1.59/0.60    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.59/0.60    inference(flattening,[],[f24])).
% 1.59/0.60  fof(f24,plain,(
% 1.59/0.60    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.59/0.60    inference(ennf_transformation,[],[f8])).
% 1.59/0.60  fof(f8,axiom,(
% 1.59/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.59/0.60  fof(f4397,plain,(
% 1.59/0.60    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k5_relat_1(sK1,k6_relat_1(k9_relat_1(sK1,X0))))) )),
% 1.59/0.60    inference(superposition,[],[f4391,f1144])).
% 1.59/0.60  fof(f1144,plain,(
% 1.59/0.60    ( ! [X85] : (k7_relat_1(sK1,X85) = k5_relat_1(k7_relat_1(sK1,X85),k6_relat_1(k9_relat_1(sK1,X85)))) )),
% 1.59/0.60    inference(backward_demodulation,[],[f550,f1143])).
% 1.59/0.60  fof(f1143,plain,(
% 1.59/0.60    ( ! [X429] : (k2_relat_1(k7_relat_1(sK1,X429)) = k9_relat_1(sK1,X429)) )),
% 1.59/0.60    inference(resolution,[],[f49,f33])).
% 1.59/0.60  fof(f550,plain,(
% 1.59/0.60    ( ! [X85] : (k7_relat_1(sK1,X85) = k5_relat_1(k7_relat_1(sK1,X85),k6_relat_1(k2_relat_1(k7_relat_1(sK1,X85))))) )),
% 1.59/0.60    inference(resolution,[],[f39,f68])).
% 1.59/0.60  fof(f39,plain,(
% 1.59/0.60    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.59/0.60    inference(cnf_transformation,[],[f21])).
% 1.59/0.60  fof(f21,plain,(
% 1.59/0.60    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.59/0.60    inference(ennf_transformation,[],[f12])).
% 1.59/0.60  fof(f12,axiom,(
% 1.59/0.60    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.59/0.60  fof(f4391,plain,(
% 1.59/0.60    ( ! [X1000,X1001] : (r1_tarski(k5_relat_1(k7_relat_1(sK1,X1000),k6_relat_1(X1001)),k5_relat_1(sK1,k6_relat_1(X1001)))) )),
% 1.59/0.60    inference(resolution,[],[f1917,f33])).
% 1.59/0.60  fof(f1917,plain,(
% 1.59/0.60    ( ! [X445,X443,X444] : (~v1_relat_1(X443) | r1_tarski(k5_relat_1(k7_relat_1(X443,X444),k6_relat_1(X445)),k5_relat_1(X443,k6_relat_1(X445)))) )),
% 1.59/0.60    inference(resolution,[],[f51,f35])).
% 1.59/0.60  fof(f51,plain,(
% 1.59/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) | ~v1_relat_1(X1)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f30])).
% 1.59/0.60  fof(f30,plain,(
% 1.59/0.60    ! [X0,X1] : (! [X2] : (r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.59/0.60    inference(ennf_transformation,[],[f14])).
% 1.59/0.60  fof(f14,axiom,(
% 1.59/0.60    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_relat_1)).
% 1.59/0.60  % SZS output end Proof for theBenchmark
% 1.59/0.60  % (4904)------------------------------
% 1.59/0.60  % (4904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.60  % (4904)Termination reason: Refutation
% 1.59/0.60  
% 1.59/0.60  % (4904)Memory used [KB]: 4861
% 1.59/0.60  % (4904)Time elapsed: 0.159 s
% 1.59/0.60  % (4904)------------------------------
% 1.59/0.60  % (4904)------------------------------
% 1.59/0.61  % (4891)Success in time 0.244 s
%------------------------------------------------------------------------------
