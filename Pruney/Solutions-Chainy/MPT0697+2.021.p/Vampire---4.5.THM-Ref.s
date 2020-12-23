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
% DateTime   : Thu Dec  3 12:54:08 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  153 (1165 expanded)
%              Number of leaves         :   20 ( 285 expanded)
%              Depth                    :   19
%              Number of atoms          :  351 (4197 expanded)
%              Number of equality atoms :   96 ( 258 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2931,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2930,f86])).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f2930,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,k1_relat_1(sK1)),sK0) ),
    inference(backward_demodulation,[],[f71,f2914])).

fof(f2914,plain,(
    ! [X1] : k3_xboole_0(X1,k1_relat_1(sK1)) = k10_relat_1(sK1,k9_relat_1(sK1,X1)) ),
    inference(backward_demodulation,[],[f2857,f2903])).

fof(f2903,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k4_relat_1(sK1),X0) ),
    inference(forward_demodulation,[],[f2902,f491])).

fof(f491,plain,(
    ! [X13] : k9_relat_1(sK1,X13) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X13))) ),
    inference(forward_demodulation,[],[f490,f118])).

fof(f118,plain,(
    ! [X6] : k2_relat_1(k7_relat_1(sK1,X6)) = k9_relat_1(sK1,X6) ),
    inference(resolution,[],[f68,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f68,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f66])).

fof(f66,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f490,plain,(
    ! [X13] : k2_relat_1(k7_relat_1(sK1,X13)) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X13))) ),
    inference(forward_demodulation,[],[f489,f484])).

fof(f484,plain,(
    ! [X12] : k4_relat_1(k7_relat_1(sK1,X12)) = k2_funct_1(k7_relat_1(sK1,X12)) ),
    inference(subsumption_resolution,[],[f483,f156])).

fof(f156,plain,(
    ! [X18] : v1_funct_1(k7_relat_1(sK1,X18)) ),
    inference(subsumption_resolution,[],[f128,f69])).

fof(f69,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f128,plain,(
    ! [X18] :
      ( v1_funct_1(k7_relat_1(sK1,X18))
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f68,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f483,plain,(
    ! [X12] :
      ( k4_relat_1(k7_relat_1(sK1,X12)) = k2_funct_1(k7_relat_1(sK1,X12))
      | ~ v1_funct_1(k7_relat_1(sK1,X12)) ) ),
    inference(subsumption_resolution,[],[f453,f160])).

fof(f160,plain,(
    ! [X20] : v2_funct_1(k7_relat_1(sK1,X20)) ),
    inference(subsumption_resolution,[],[f159,f69])).

fof(f159,plain,(
    ! [X20] :
      ( v2_funct_1(k7_relat_1(sK1,X20))
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f130,f70])).

fof(f70,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f130,plain,(
    ! [X20] :
      ( v2_funct_1(k7_relat_1(sK1,X20))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f68,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k7_relat_1(X1,X0))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k7_relat_1(X1,X0))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k7_relat_1(X1,X0))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k7_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_funct_1)).

fof(f453,plain,(
    ! [X12] :
      ( k4_relat_1(k7_relat_1(sK1,X12)) = k2_funct_1(k7_relat_1(sK1,X12))
      | ~ v2_funct_1(k7_relat_1(sK1,X12))
      | ~ v1_funct_1(k7_relat_1(sK1,X12)) ) ),
    inference(resolution,[],[f155,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f155,plain,(
    ! [X17] : v1_relat_1(k7_relat_1(sK1,X17)) ),
    inference(subsumption_resolution,[],[f127,f69])).

fof(f127,plain,(
    ! [X17] :
      ( v1_relat_1(k7_relat_1(sK1,X17))
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f68,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f489,plain,(
    ! [X13] : k2_relat_1(k7_relat_1(sK1,X13)) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X13))) ),
    inference(subsumption_resolution,[],[f488,f156])).

fof(f488,plain,(
    ! [X13] :
      ( k2_relat_1(k7_relat_1(sK1,X13)) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X13)))
      | ~ v1_funct_1(k7_relat_1(sK1,X13)) ) ),
    inference(subsumption_resolution,[],[f454,f160])).

fof(f454,plain,(
    ! [X13] :
      ( k2_relat_1(k7_relat_1(sK1,X13)) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X13)))
      | ~ v2_funct_1(k7_relat_1(sK1,X13))
      | ~ v1_funct_1(k7_relat_1(sK1,X13)) ) ),
    inference(resolution,[],[f155,f83])).

fof(f83,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f2902,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK1),X0) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f2901,f1047])).

fof(f1047,plain,(
    ! [X0] : k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f1046,f117])).

fof(f117,plain,(
    ! [X5] : k7_relat_1(sK1,X5) = k5_relat_1(k6_relat_1(X5),sK1) ),
    inference(resolution,[],[f68,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f1046,plain,(
    ! [X0] : k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) ),
    inference(subsumption_resolution,[],[f1045,f72])).

fof(f72,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f1045,plain,(
    ! [X0] :
      ( k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),sK1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f109,f73])).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f109,plain,(
    ! [X3] :
      ( k4_relat_1(k5_relat_1(X3,sK1)) = k5_relat_1(k4_relat_1(sK1),k4_relat_1(X3))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f68,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f2901,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK1),X0) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f2883,f74])).

fof(f74,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f2883,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f291,f72])).

fof(f291,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k4_relat_1(sK1),X0)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f145,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f145,plain,(
    v1_relat_1(k4_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f136,f142])).

fof(f142,plain,(
    k4_relat_1(sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f141,f69])).

fof(f141,plain,
    ( k4_relat_1(sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f113,f70])).

fof(f113,plain,
    ( k4_relat_1(sK1) = k2_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f68,f82])).

fof(f136,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f135,f69])).

fof(f135,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f110,f70])).

fof(f110,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f68,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f2857,plain,(
    ! [X1] : k3_xboole_0(X1,k1_relat_1(sK1)) = k10_relat_1(sK1,k10_relat_1(k4_relat_1(sK1),X1)) ),
    inference(superposition,[],[f2117,f1020])).

fof(f1020,plain,(
    ! [X6] : k9_relat_1(k4_relat_1(sK1),X6) = k10_relat_1(sK1,X6) ),
    inference(forward_demodulation,[],[f1008,f843])).

fof(f843,plain,(
    ! [X14] : k10_relat_1(sK1,X14) = k2_relat_1(k4_relat_1(k8_relat_1(X14,sK1))) ),
    inference(backward_demodulation,[],[f391,f840])).

fof(f840,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k1_relat_1(k8_relat_1(X0,sK1)) ),
    inference(forward_demodulation,[],[f839,f116])).

fof(f116,plain,(
    ! [X4] : k8_relat_1(X4,sK1) = k5_relat_1(sK1,k6_relat_1(X4)) ),
    inference(resolution,[],[f68,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f839,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ),
    inference(subsumption_resolution,[],[f834,f72])).

fof(f834,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,X0) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f106,f74])).

fof(f106,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(sK1,X0)) = k10_relat_1(sK1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f68,f77])).

fof(f391,plain,(
    ! [X14] : k1_relat_1(k8_relat_1(X14,sK1)) = k2_relat_1(k4_relat_1(k8_relat_1(X14,sK1))) ),
    inference(forward_demodulation,[],[f390,f382])).

fof(f382,plain,(
    ! [X12] : k4_relat_1(k8_relat_1(X12,sK1)) = k2_funct_1(k8_relat_1(X12,sK1)) ),
    inference(subsumption_resolution,[],[f381,f154])).

fof(f154,plain,(
    ! [X16] : v1_funct_1(k8_relat_1(X16,sK1)) ),
    inference(subsumption_resolution,[],[f126,f69])).

fof(f126,plain,(
    ! [X16] :
      ( v1_funct_1(k8_relat_1(X16,sK1))
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f68,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

fof(f381,plain,(
    ! [X12] :
      ( k4_relat_1(k8_relat_1(X12,sK1)) = k2_funct_1(k8_relat_1(X12,sK1))
      | ~ v1_funct_1(k8_relat_1(X12,sK1)) ) ),
    inference(subsumption_resolution,[],[f352,f158])).

fof(f158,plain,(
    ! [X19] : v2_funct_1(k8_relat_1(X19,sK1)) ),
    inference(subsumption_resolution,[],[f157,f69])).

fof(f157,plain,(
    ! [X19] :
      ( v2_funct_1(k8_relat_1(X19,sK1))
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f129,f70])).

fof(f129,plain,(
    ! [X19] :
      ( v2_funct_1(k8_relat_1(X19,sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f68,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k8_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k8_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k8_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_funct_1)).

fof(f352,plain,(
    ! [X12] :
      ( k4_relat_1(k8_relat_1(X12,sK1)) = k2_funct_1(k8_relat_1(X12,sK1))
      | ~ v2_funct_1(k8_relat_1(X12,sK1))
      | ~ v1_funct_1(k8_relat_1(X12,sK1)) ) ),
    inference(resolution,[],[f153,f82])).

fof(f153,plain,(
    ! [X15] : v1_relat_1(k8_relat_1(X15,sK1)) ),
    inference(subsumption_resolution,[],[f125,f69])).

fof(f125,plain,(
    ! [X15] :
      ( v1_relat_1(k8_relat_1(X15,sK1))
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f68,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f390,plain,(
    ! [X14] : k1_relat_1(k8_relat_1(X14,sK1)) = k2_relat_1(k2_funct_1(k8_relat_1(X14,sK1))) ),
    inference(subsumption_resolution,[],[f389,f154])).

fof(f389,plain,(
    ! [X14] :
      ( k1_relat_1(k8_relat_1(X14,sK1)) = k2_relat_1(k2_funct_1(k8_relat_1(X14,sK1)))
      | ~ v1_funct_1(k8_relat_1(X14,sK1)) ) ),
    inference(subsumption_resolution,[],[f354,f158])).

fof(f354,plain,(
    ! [X14] :
      ( k1_relat_1(k8_relat_1(X14,sK1)) = k2_relat_1(k2_funct_1(k8_relat_1(X14,sK1)))
      | ~ v2_funct_1(k8_relat_1(X14,sK1))
      | ~ v1_funct_1(k8_relat_1(X14,sK1)) ) ),
    inference(resolution,[],[f153,f84])).

fof(f84,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1008,plain,(
    ! [X6] : k9_relat_1(k4_relat_1(sK1),X6) = k2_relat_1(k4_relat_1(k8_relat_1(X6,sK1))) ),
    inference(backward_demodulation,[],[f303,f1004])).

fof(f1004,plain,(
    ! [X5] : k7_relat_1(k4_relat_1(sK1),X5) = k4_relat_1(k8_relat_1(X5,sK1)) ),
    inference(backward_demodulation,[],[f302,f1003])).

fof(f1003,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k8_relat_1(X0,sK1)) ),
    inference(forward_demodulation,[],[f1002,f116])).

fof(f1002,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ),
    inference(subsumption_resolution,[],[f1001,f72])).

fof(f1001,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f108,f73])).

fof(f108,plain,(
    ! [X2] :
      ( k4_relat_1(k5_relat_1(sK1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(sK1))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f68,f78])).

fof(f302,plain,(
    ! [X5] : k7_relat_1(k4_relat_1(sK1),X5) = k5_relat_1(k6_relat_1(X5),k4_relat_1(sK1)) ),
    inference(resolution,[],[f145,f88])).

fof(f303,plain,(
    ! [X6] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X6)) = k9_relat_1(k4_relat_1(sK1),X6) ),
    inference(resolution,[],[f145,f89])).

fof(f2117,plain,(
    ! [X0] : k9_relat_1(k4_relat_1(sK1),k10_relat_1(k4_relat_1(sK1),X0)) = k3_xboole_0(X0,k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f1025,f2111])).

fof(f2111,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(superposition,[],[f840,f105])).

fof(f105,plain,(
    sK1 = k8_relat_1(k2_relat_1(sK1),sK1) ),
    inference(resolution,[],[f68,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(f1025,plain,(
    ! [X0] : k9_relat_1(k4_relat_1(sK1),k10_relat_1(k4_relat_1(sK1),X0)) = k3_xboole_0(X0,k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f283,f1020])).

fof(f283,plain,(
    ! [X0] : k9_relat_1(k4_relat_1(sK1),k10_relat_1(k4_relat_1(sK1),X0)) = k3_xboole_0(X0,k9_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f282,f148])).

fof(f148,plain,(
    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f147,f142])).

fof(f147,plain,(
    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f146,f69])).

fof(f146,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f114,f70])).

fof(f114,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f68,f83])).

fof(f282,plain,(
    ! [X0] : k9_relat_1(k4_relat_1(sK1),k10_relat_1(k4_relat_1(sK1),X0)) = k3_xboole_0(X0,k9_relat_1(k4_relat_1(sK1),k1_relat_1(k4_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f256,f145])).

fof(f256,plain,(
    ! [X0] :
      ( k9_relat_1(k4_relat_1(sK1),k10_relat_1(k4_relat_1(sK1),X0)) = k3_xboole_0(X0,k9_relat_1(k4_relat_1(sK1),k1_relat_1(k4_relat_1(sK1))))
      | ~ v1_relat_1(k4_relat_1(sK1)) ) ),
    inference(resolution,[],[f144,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f144,plain,(
    v1_funct_1(k4_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f138,f142])).

fof(f138,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f137,f69])).

fof(f137,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f111,f70])).

fof(f111,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f68,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:42:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (17757)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.46  % (17749)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.48  % (17743)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (17758)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.49  % (17747)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (17752)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (17750)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.50  % (17762)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (17754)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (17746)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (17759)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (17760)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (17763)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (17745)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (17751)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (17755)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (17744)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (17764)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (17744)Refutation not found, incomplete strategy% (17744)------------------------------
% 0.21/0.51  % (17744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17744)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17744)Memory used [KB]: 10618
% 0.21/0.51  % (17744)Time elapsed: 0.113 s
% 0.21/0.51  % (17744)------------------------------
% 0.21/0.51  % (17744)------------------------------
% 0.21/0.52  % (17742)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (17764)Refutation not found, incomplete strategy% (17764)------------------------------
% 0.21/0.52  % (17764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17764)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17764)Memory used [KB]: 10618
% 0.21/0.52  % (17764)Time elapsed: 0.113 s
% 0.21/0.52  % (17764)------------------------------
% 0.21/0.52  % (17764)------------------------------
% 0.21/0.52  % (17741)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.52  % (17748)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (17753)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.53  % (17761)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.44/0.55  % (17756)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.59/0.61  % (17752)Refutation found. Thanks to Tanya!
% 1.59/0.61  % SZS status Theorem for theBenchmark
% 1.59/0.61  % SZS output start Proof for theBenchmark
% 1.59/0.61  fof(f2931,plain,(
% 1.59/0.61    $false),
% 1.59/0.61    inference(subsumption_resolution,[],[f2930,f86])).
% 1.59/0.61  fof(f86,plain,(
% 1.59/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f2])).
% 1.59/0.61  fof(f2,axiom,(
% 1.59/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.59/0.61  fof(f2930,plain,(
% 1.59/0.61    ~r1_tarski(k3_xboole_0(sK0,k1_relat_1(sK1)),sK0)),
% 1.59/0.61    inference(backward_demodulation,[],[f71,f2914])).
% 1.59/0.61  fof(f2914,plain,(
% 1.59/0.61    ( ! [X1] : (k3_xboole_0(X1,k1_relat_1(sK1)) = k10_relat_1(sK1,k9_relat_1(sK1,X1))) )),
% 1.59/0.61    inference(backward_demodulation,[],[f2857,f2903])).
% 1.59/0.61  fof(f2903,plain,(
% 1.59/0.61    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k4_relat_1(sK1),X0)) )),
% 1.59/0.61    inference(forward_demodulation,[],[f2902,f491])).
% 1.59/0.61  fof(f491,plain,(
% 1.59/0.61    ( ! [X13] : (k9_relat_1(sK1,X13) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X13)))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f490,f118])).
% 1.59/0.61  fof(f118,plain,(
% 1.59/0.61    ( ! [X6] : (k2_relat_1(k7_relat_1(sK1,X6)) = k9_relat_1(sK1,X6)) )),
% 1.59/0.61    inference(resolution,[],[f68,f89])).
% 1.59/0.61  fof(f89,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f44])).
% 1.59/0.61  fof(f44,plain,(
% 1.59/0.61    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f8])).
% 1.59/0.61  fof(f8,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.59/0.61  fof(f68,plain,(
% 1.59/0.61    v1_relat_1(sK1)),
% 1.59/0.61    inference(cnf_transformation,[],[f67])).
% 1.59/0.61  fof(f67,plain,(
% 1.59/0.61    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.59/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f66])).
% 1.59/0.61  fof(f66,plain,(
% 1.59/0.61    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.59/0.61    introduced(choice_axiom,[])).
% 1.59/0.61  fof(f32,plain,(
% 1.59/0.61    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.59/0.61    inference(flattening,[],[f31])).
% 1.59/0.61  fof(f31,plain,(
% 1.59/0.61    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.59/0.61    inference(ennf_transformation,[],[f29])).
% 1.59/0.61  fof(f29,negated_conjecture,(
% 1.59/0.61    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.59/0.61    inference(negated_conjecture,[],[f28])).
% 1.59/0.61  fof(f28,conjecture,(
% 1.59/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 1.59/0.61  fof(f490,plain,(
% 1.59/0.61    ( ! [X13] : (k2_relat_1(k7_relat_1(sK1,X13)) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X13)))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f489,f484])).
% 1.59/0.61  fof(f484,plain,(
% 1.59/0.61    ( ! [X12] : (k4_relat_1(k7_relat_1(sK1,X12)) = k2_funct_1(k7_relat_1(sK1,X12))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f483,f156])).
% 1.59/0.61  fof(f156,plain,(
% 1.59/0.61    ( ! [X18] : (v1_funct_1(k7_relat_1(sK1,X18))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f128,f69])).
% 1.59/0.61  fof(f69,plain,(
% 1.59/0.61    v1_funct_1(sK1)),
% 1.59/0.61    inference(cnf_transformation,[],[f67])).
% 1.59/0.61  fof(f128,plain,(
% 1.59/0.61    ( ! [X18] : (v1_funct_1(k7_relat_1(sK1,X18)) | ~v1_funct_1(sK1)) )),
% 1.59/0.61    inference(resolution,[],[f68,f98])).
% 1.59/0.61  fof(f98,plain,(
% 1.59/0.61    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f55])).
% 1.59/0.61  fof(f55,plain,(
% 1.59/0.61    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(flattening,[],[f54])).
% 1.59/0.61  fof(f54,plain,(
% 1.59/0.61    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.59/0.61    inference(ennf_transformation,[],[f19])).
% 1.59/0.61  fof(f19,axiom,(
% 1.59/0.61    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 1.59/0.61  fof(f483,plain,(
% 1.59/0.61    ( ! [X12] : (k4_relat_1(k7_relat_1(sK1,X12)) = k2_funct_1(k7_relat_1(sK1,X12)) | ~v1_funct_1(k7_relat_1(sK1,X12))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f453,f160])).
% 1.59/0.61  fof(f160,plain,(
% 1.59/0.61    ( ! [X20] : (v2_funct_1(k7_relat_1(sK1,X20))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f159,f69])).
% 1.59/0.61  fof(f159,plain,(
% 1.59/0.61    ( ! [X20] : (v2_funct_1(k7_relat_1(sK1,X20)) | ~v1_funct_1(sK1)) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f130,f70])).
% 1.59/0.61  fof(f70,plain,(
% 1.59/0.61    v2_funct_1(sK1)),
% 1.59/0.61    inference(cnf_transformation,[],[f67])).
% 1.59/0.61  fof(f130,plain,(
% 1.59/0.61    ( ! [X20] : (v2_funct_1(k7_relat_1(sK1,X20)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1)) )),
% 1.59/0.61    inference(resolution,[],[f68,f100])).
% 1.59/0.61  fof(f100,plain,(
% 1.59/0.61    ( ! [X0,X1] : (v2_funct_1(k7_relat_1(X1,X0)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f59])).
% 1.59/0.61  fof(f59,plain,(
% 1.59/0.61    ! [X0,X1] : (v2_funct_1(k7_relat_1(X1,X0)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(flattening,[],[f58])).
% 1.59/0.61  fof(f58,plain,(
% 1.59/0.61    ! [X0,X1] : ((v2_funct_1(k7_relat_1(X1,X0)) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.59/0.61    inference(ennf_transformation,[],[f26])).
% 1.59/0.61  fof(f26,axiom,(
% 1.59/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => v2_funct_1(k7_relat_1(X1,X0))))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_funct_1)).
% 1.59/0.61  fof(f453,plain,(
% 1.59/0.61    ( ! [X12] : (k4_relat_1(k7_relat_1(sK1,X12)) = k2_funct_1(k7_relat_1(sK1,X12)) | ~v2_funct_1(k7_relat_1(sK1,X12)) | ~v1_funct_1(k7_relat_1(sK1,X12))) )),
% 1.59/0.61    inference(resolution,[],[f155,f82])).
% 1.59/0.61  fof(f82,plain,(
% 1.59/0.61    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f39])).
% 1.59/0.61  fof(f39,plain,(
% 1.59/0.61    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(flattening,[],[f38])).
% 1.59/0.61  fof(f38,plain,(
% 1.59/0.61    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.59/0.61    inference(ennf_transformation,[],[f17])).
% 1.59/0.61  fof(f17,axiom,(
% 1.59/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 1.59/0.61  fof(f155,plain,(
% 1.59/0.61    ( ! [X17] : (v1_relat_1(k7_relat_1(sK1,X17))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f127,f69])).
% 1.59/0.61  fof(f127,plain,(
% 1.59/0.61    ( ! [X17] : (v1_relat_1(k7_relat_1(sK1,X17)) | ~v1_funct_1(sK1)) )),
% 1.59/0.61    inference(resolution,[],[f68,f97])).
% 1.59/0.61  fof(f97,plain,(
% 1.59/0.61    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f55])).
% 1.59/0.61  fof(f489,plain,(
% 1.59/0.61    ( ! [X13] : (k2_relat_1(k7_relat_1(sK1,X13)) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X13)))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f488,f156])).
% 1.59/0.61  fof(f488,plain,(
% 1.59/0.61    ( ! [X13] : (k2_relat_1(k7_relat_1(sK1,X13)) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X13))) | ~v1_funct_1(k7_relat_1(sK1,X13))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f454,f160])).
% 1.59/0.61  fof(f454,plain,(
% 1.59/0.61    ( ! [X13] : (k2_relat_1(k7_relat_1(sK1,X13)) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X13))) | ~v2_funct_1(k7_relat_1(sK1,X13)) | ~v1_funct_1(k7_relat_1(sK1,X13))) )),
% 1.59/0.61    inference(resolution,[],[f155,f83])).
% 1.59/0.61  fof(f83,plain,(
% 1.59/0.61    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f41])).
% 1.59/0.61  fof(f41,plain,(
% 1.59/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(flattening,[],[f40])).
% 1.59/0.61  fof(f40,plain,(
% 1.59/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.59/0.61    inference(ennf_transformation,[],[f25])).
% 1.59/0.61  fof(f25,axiom,(
% 1.59/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.59/0.61  fof(f2902,plain,(
% 1.59/0.61    ( ! [X0] : (k10_relat_1(k4_relat_1(sK1),X0) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f2901,f1047])).
% 1.59/0.61  fof(f1047,plain,(
% 1.59/0.61    ( ! [X0] : (k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(sK1,X0))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f1046,f117])).
% 1.59/0.61  fof(f117,plain,(
% 1.59/0.61    ( ! [X5] : (k7_relat_1(sK1,X5) = k5_relat_1(k6_relat_1(X5),sK1)) )),
% 1.59/0.61    inference(resolution,[],[f68,f88])).
% 1.59/0.61  fof(f88,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f43])).
% 1.59/0.61  fof(f43,plain,(
% 1.59/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f16])).
% 1.59/0.61  fof(f16,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.59/0.61  fof(f1046,plain,(
% 1.59/0.61    ( ! [X0] : (k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),sK1))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f1045,f72])).
% 1.59/0.61  fof(f72,plain,(
% 1.59/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f3])).
% 1.59/0.61  fof(f3,axiom,(
% 1.59/0.61    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.59/0.61  fof(f1045,plain,(
% 1.59/0.61    ( ! [X0] : (k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.59/0.61    inference(superposition,[],[f109,f73])).
% 1.59/0.61  fof(f73,plain,(
% 1.59/0.61    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f14])).
% 1.59/0.61  fof(f14,axiom,(
% 1.59/0.61    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 1.59/0.61  fof(f109,plain,(
% 1.59/0.61    ( ! [X3] : (k4_relat_1(k5_relat_1(X3,sK1)) = k5_relat_1(k4_relat_1(sK1),k4_relat_1(X3)) | ~v1_relat_1(X3)) )),
% 1.59/0.61    inference(resolution,[],[f68,f78])).
% 1.59/0.61  fof(f78,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f35])).
% 1.59/0.61  fof(f35,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f12])).
% 1.59/0.61  fof(f12,axiom,(
% 1.59/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 1.59/0.61  fof(f2901,plain,(
% 1.59/0.61    ( ! [X0] : (k10_relat_1(k4_relat_1(sK1),X0) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0)))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f2883,f74])).
% 1.59/0.61  fof(f74,plain,(
% 1.59/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.59/0.61    inference(cnf_transformation,[],[f13])).
% 1.59/0.61  fof(f13,axiom,(
% 1.59/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.59/0.61  fof(f2883,plain,(
% 1.59/0.61    ( ! [X0] : (k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(k6_relat_1(X0)))) )),
% 1.59/0.61    inference(resolution,[],[f291,f72])).
% 1.59/0.61  fof(f291,plain,(
% 1.59/0.61    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k4_relat_1(sK1),X0)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(X0))) )),
% 1.59/0.61    inference(resolution,[],[f145,f77])).
% 1.59/0.61  fof(f77,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f34])).
% 1.59/0.61  fof(f34,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f10])).
% 1.59/0.61  fof(f10,axiom,(
% 1.59/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.59/0.61  fof(f145,plain,(
% 1.59/0.61    v1_relat_1(k4_relat_1(sK1))),
% 1.59/0.61    inference(backward_demodulation,[],[f136,f142])).
% 1.59/0.61  fof(f142,plain,(
% 1.59/0.61    k4_relat_1(sK1) = k2_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f141,f69])).
% 1.59/0.61  fof(f141,plain,(
% 1.59/0.61    k4_relat_1(sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f113,f70])).
% 1.59/0.61  fof(f113,plain,(
% 1.59/0.61    k4_relat_1(sK1) = k2_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(resolution,[],[f68,f82])).
% 1.59/0.61  fof(f136,plain,(
% 1.59/0.61    v1_relat_1(k2_funct_1(sK1))),
% 1.59/0.61    inference(subsumption_resolution,[],[f135,f69])).
% 1.59/0.61  fof(f135,plain,(
% 1.59/0.61    v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f110,f70])).
% 1.59/0.61  fof(f110,plain,(
% 1.59/0.61    v1_relat_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(resolution,[],[f68,f79])).
% 1.59/0.61  fof(f79,plain,(
% 1.59/0.61    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f37])).
% 1.59/0.61  fof(f37,plain,(
% 1.59/0.61    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(flattening,[],[f36])).
% 1.59/0.61  fof(f36,plain,(
% 1.59/0.61    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.59/0.61    inference(ennf_transformation,[],[f18])).
% 1.59/0.61  fof(f18,axiom,(
% 1.59/0.61    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.59/0.61  fof(f2857,plain,(
% 1.59/0.61    ( ! [X1] : (k3_xboole_0(X1,k1_relat_1(sK1)) = k10_relat_1(sK1,k10_relat_1(k4_relat_1(sK1),X1))) )),
% 1.59/0.61    inference(superposition,[],[f2117,f1020])).
% 1.59/0.61  fof(f1020,plain,(
% 1.59/0.61    ( ! [X6] : (k9_relat_1(k4_relat_1(sK1),X6) = k10_relat_1(sK1,X6)) )),
% 1.59/0.61    inference(forward_demodulation,[],[f1008,f843])).
% 1.59/0.61  fof(f843,plain,(
% 1.59/0.61    ( ! [X14] : (k10_relat_1(sK1,X14) = k2_relat_1(k4_relat_1(k8_relat_1(X14,sK1)))) )),
% 1.59/0.61    inference(backward_demodulation,[],[f391,f840])).
% 1.59/0.61  fof(f840,plain,(
% 1.59/0.61    ( ! [X0] : (k10_relat_1(sK1,X0) = k1_relat_1(k8_relat_1(X0,sK1))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f839,f116])).
% 1.59/0.61  fof(f116,plain,(
% 1.59/0.61    ( ! [X4] : (k8_relat_1(X4,sK1) = k5_relat_1(sK1,k6_relat_1(X4))) )),
% 1.59/0.61    inference(resolution,[],[f68,f87])).
% 1.59/0.61  fof(f87,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f42])).
% 1.59/0.61  fof(f42,plain,(
% 1.59/0.61    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f5])).
% 1.59/0.61  fof(f5,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 1.59/0.61  fof(f839,plain,(
% 1.59/0.61    ( ! [X0] : (k10_relat_1(sK1,X0) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f834,f72])).
% 1.59/0.61  fof(f834,plain,(
% 1.59/0.61    ( ! [X0] : (k10_relat_1(sK1,X0) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.59/0.61    inference(superposition,[],[f106,f74])).
% 1.59/0.61  fof(f106,plain,(
% 1.59/0.61    ( ! [X0] : (k1_relat_1(k5_relat_1(sK1,X0)) = k10_relat_1(sK1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(resolution,[],[f68,f77])).
% 1.59/0.61  fof(f391,plain,(
% 1.59/0.61    ( ! [X14] : (k1_relat_1(k8_relat_1(X14,sK1)) = k2_relat_1(k4_relat_1(k8_relat_1(X14,sK1)))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f390,f382])).
% 1.59/0.61  fof(f382,plain,(
% 1.59/0.61    ( ! [X12] : (k4_relat_1(k8_relat_1(X12,sK1)) = k2_funct_1(k8_relat_1(X12,sK1))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f381,f154])).
% 1.59/0.61  fof(f154,plain,(
% 1.59/0.61    ( ! [X16] : (v1_funct_1(k8_relat_1(X16,sK1))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f126,f69])).
% 1.59/0.61  fof(f126,plain,(
% 1.59/0.61    ( ! [X16] : (v1_funct_1(k8_relat_1(X16,sK1)) | ~v1_funct_1(sK1)) )),
% 1.59/0.61    inference(resolution,[],[f68,f96])).
% 1.59/0.61  fof(f96,plain,(
% 1.59/0.61    ( ! [X0,X1] : (v1_funct_1(k8_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f53])).
% 1.59/0.61  fof(f53,plain,(
% 1.59/0.61    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(flattening,[],[f52])).
% 1.59/0.61  fof(f52,plain,(
% 1.59/0.61    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.59/0.61    inference(ennf_transformation,[],[f20])).
% 1.59/0.61  fof(f20,axiom,(
% 1.59/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).
% 1.59/0.61  fof(f381,plain,(
% 1.59/0.61    ( ! [X12] : (k4_relat_1(k8_relat_1(X12,sK1)) = k2_funct_1(k8_relat_1(X12,sK1)) | ~v1_funct_1(k8_relat_1(X12,sK1))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f352,f158])).
% 1.59/0.61  fof(f158,plain,(
% 1.59/0.61    ( ! [X19] : (v2_funct_1(k8_relat_1(X19,sK1))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f157,f69])).
% 1.59/0.61  fof(f157,plain,(
% 1.59/0.61    ( ! [X19] : (v2_funct_1(k8_relat_1(X19,sK1)) | ~v1_funct_1(sK1)) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f129,f70])).
% 1.59/0.61  fof(f129,plain,(
% 1.59/0.61    ( ! [X19] : (v2_funct_1(k8_relat_1(X19,sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1)) )),
% 1.59/0.61    inference(resolution,[],[f68,f99])).
% 1.59/0.61  fof(f99,plain,(
% 1.59/0.61    ( ! [X0,X1] : (v2_funct_1(k8_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f57])).
% 1.59/0.61  fof(f57,plain,(
% 1.59/0.61    ! [X0,X1] : (v2_funct_1(k8_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(flattening,[],[f56])).
% 1.59/0.61  fof(f56,plain,(
% 1.59/0.61    ! [X0,X1] : ((v2_funct_1(k8_relat_1(X0,X1)) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.59/0.61    inference(ennf_transformation,[],[f27])).
% 1.59/0.61  fof(f27,axiom,(
% 1.59/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => v2_funct_1(k8_relat_1(X0,X1))))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_funct_1)).
% 1.59/0.61  fof(f352,plain,(
% 1.59/0.61    ( ! [X12] : (k4_relat_1(k8_relat_1(X12,sK1)) = k2_funct_1(k8_relat_1(X12,sK1)) | ~v2_funct_1(k8_relat_1(X12,sK1)) | ~v1_funct_1(k8_relat_1(X12,sK1))) )),
% 1.59/0.61    inference(resolution,[],[f153,f82])).
% 1.59/0.61  fof(f153,plain,(
% 1.59/0.61    ( ! [X15] : (v1_relat_1(k8_relat_1(X15,sK1))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f125,f69])).
% 1.59/0.61  fof(f125,plain,(
% 1.59/0.61    ( ! [X15] : (v1_relat_1(k8_relat_1(X15,sK1)) | ~v1_funct_1(sK1)) )),
% 1.59/0.61    inference(resolution,[],[f68,f95])).
% 1.59/0.61  fof(f95,plain,(
% 1.59/0.61    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f53])).
% 1.59/0.61  fof(f390,plain,(
% 1.59/0.61    ( ! [X14] : (k1_relat_1(k8_relat_1(X14,sK1)) = k2_relat_1(k2_funct_1(k8_relat_1(X14,sK1)))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f389,f154])).
% 1.59/0.61  fof(f389,plain,(
% 1.59/0.61    ( ! [X14] : (k1_relat_1(k8_relat_1(X14,sK1)) = k2_relat_1(k2_funct_1(k8_relat_1(X14,sK1))) | ~v1_funct_1(k8_relat_1(X14,sK1))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f354,f158])).
% 1.59/0.61  fof(f354,plain,(
% 1.59/0.61    ( ! [X14] : (k1_relat_1(k8_relat_1(X14,sK1)) = k2_relat_1(k2_funct_1(k8_relat_1(X14,sK1))) | ~v2_funct_1(k8_relat_1(X14,sK1)) | ~v1_funct_1(k8_relat_1(X14,sK1))) )),
% 1.59/0.61    inference(resolution,[],[f153,f84])).
% 1.59/0.61  fof(f84,plain,(
% 1.59/0.61    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f41])).
% 1.59/0.61  fof(f1008,plain,(
% 1.59/0.61    ( ! [X6] : (k9_relat_1(k4_relat_1(sK1),X6) = k2_relat_1(k4_relat_1(k8_relat_1(X6,sK1)))) )),
% 1.59/0.61    inference(backward_demodulation,[],[f303,f1004])).
% 1.59/0.61  fof(f1004,plain,(
% 1.59/0.61    ( ! [X5] : (k7_relat_1(k4_relat_1(sK1),X5) = k4_relat_1(k8_relat_1(X5,sK1))) )),
% 1.59/0.61    inference(backward_demodulation,[],[f302,f1003])).
% 1.59/0.61  fof(f1003,plain,(
% 1.59/0.61    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k8_relat_1(X0,sK1))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f1002,f116])).
% 1.59/0.61  fof(f1002,plain,(
% 1.59/0.61    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f1001,f72])).
% 1.59/0.61  fof(f1001,plain,(
% 1.59/0.61    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.59/0.61    inference(superposition,[],[f108,f73])).
% 1.59/0.61  fof(f108,plain,(
% 1.59/0.61    ( ! [X2] : (k4_relat_1(k5_relat_1(sK1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(sK1)) | ~v1_relat_1(X2)) )),
% 1.59/0.61    inference(resolution,[],[f68,f78])).
% 1.59/0.61  fof(f302,plain,(
% 1.59/0.61    ( ! [X5] : (k7_relat_1(k4_relat_1(sK1),X5) = k5_relat_1(k6_relat_1(X5),k4_relat_1(sK1))) )),
% 1.59/0.61    inference(resolution,[],[f145,f88])).
% 1.59/0.61  fof(f303,plain,(
% 1.59/0.61    ( ! [X6] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X6)) = k9_relat_1(k4_relat_1(sK1),X6)) )),
% 1.59/0.61    inference(resolution,[],[f145,f89])).
% 1.59/0.61  fof(f2117,plain,(
% 1.59/0.61    ( ! [X0] : (k9_relat_1(k4_relat_1(sK1),k10_relat_1(k4_relat_1(sK1),X0)) = k3_xboole_0(X0,k1_relat_1(sK1))) )),
% 1.59/0.61    inference(backward_demodulation,[],[f1025,f2111])).
% 1.59/0.61  fof(f2111,plain,(
% 1.59/0.61    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 1.59/0.61    inference(superposition,[],[f840,f105])).
% 1.59/0.61  fof(f105,plain,(
% 1.59/0.61    sK1 = k8_relat_1(k2_relat_1(sK1),sK1)),
% 1.59/0.61    inference(resolution,[],[f68,f76])).
% 1.59/0.61  fof(f76,plain,(
% 1.59/0.61    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f33])).
% 1.59/0.61  fof(f33,plain,(
% 1.59/0.61    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f6])).
% 1.59/0.61  fof(f6,axiom,(
% 1.59/0.61    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
% 1.59/0.61  fof(f1025,plain,(
% 1.59/0.61    ( ! [X0] : (k9_relat_1(k4_relat_1(sK1),k10_relat_1(k4_relat_1(sK1),X0)) = k3_xboole_0(X0,k10_relat_1(sK1,k2_relat_1(sK1)))) )),
% 1.59/0.61    inference(backward_demodulation,[],[f283,f1020])).
% 1.59/0.61  fof(f283,plain,(
% 1.59/0.61    ( ! [X0] : (k9_relat_1(k4_relat_1(sK1),k10_relat_1(k4_relat_1(sK1),X0)) = k3_xboole_0(X0,k9_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f282,f148])).
% 1.59/0.61  fof(f148,plain,(
% 1.59/0.61    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1))),
% 1.59/0.61    inference(forward_demodulation,[],[f147,f142])).
% 1.59/0.61  fof(f147,plain,(
% 1.59/0.61    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 1.59/0.61    inference(subsumption_resolution,[],[f146,f69])).
% 1.59/0.61  fof(f146,plain,(
% 1.59/0.61    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f114,f70])).
% 1.59/0.61  fof(f114,plain,(
% 1.59/0.61    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(resolution,[],[f68,f83])).
% 1.59/0.61  fof(f282,plain,(
% 1.59/0.61    ( ! [X0] : (k9_relat_1(k4_relat_1(sK1),k10_relat_1(k4_relat_1(sK1),X0)) = k3_xboole_0(X0,k9_relat_1(k4_relat_1(sK1),k1_relat_1(k4_relat_1(sK1))))) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f256,f145])).
% 1.59/0.61  fof(f256,plain,(
% 1.59/0.61    ( ! [X0] : (k9_relat_1(k4_relat_1(sK1),k10_relat_1(k4_relat_1(sK1),X0)) = k3_xboole_0(X0,k9_relat_1(k4_relat_1(sK1),k1_relat_1(k4_relat_1(sK1)))) | ~v1_relat_1(k4_relat_1(sK1))) )),
% 1.59/0.61    inference(resolution,[],[f144,f94])).
% 1.59/0.61  fof(f94,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f51])).
% 1.59/0.61  fof(f51,plain,(
% 1.59/0.61    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(flattening,[],[f50])).
% 1.59/0.61  fof(f50,plain,(
% 1.59/0.61    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.59/0.61    inference(ennf_transformation,[],[f24])).
% 1.59/0.61  fof(f24,axiom,(
% 1.59/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 1.59/0.61  fof(f144,plain,(
% 1.59/0.61    v1_funct_1(k4_relat_1(sK1))),
% 1.59/0.61    inference(backward_demodulation,[],[f138,f142])).
% 1.59/0.61  fof(f138,plain,(
% 1.59/0.61    v1_funct_1(k2_funct_1(sK1))),
% 1.59/0.61    inference(subsumption_resolution,[],[f137,f69])).
% 1.59/0.61  fof(f137,plain,(
% 1.59/0.61    v1_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(subsumption_resolution,[],[f111,f70])).
% 1.59/0.61  fof(f111,plain,(
% 1.59/0.61    v1_funct_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.59/0.61    inference(resolution,[],[f68,f80])).
% 1.59/0.61  fof(f80,plain,(
% 1.59/0.61    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f37])).
% 1.59/0.61  fof(f71,plain,(
% 1.59/0.61    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.59/0.61    inference(cnf_transformation,[],[f67])).
% 1.59/0.61  % SZS output end Proof for theBenchmark
% 1.59/0.61  % (17752)------------------------------
% 1.59/0.61  % (17752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.61  % (17752)Termination reason: Refutation
% 1.59/0.61  
% 1.59/0.61  % (17752)Memory used [KB]: 3198
% 1.59/0.61  % (17752)Time elapsed: 0.213 s
% 1.59/0.61  % (17752)------------------------------
% 1.59/0.61  % (17752)------------------------------
% 1.59/0.61  % (17740)Success in time 0.258 s
%------------------------------------------------------------------------------
