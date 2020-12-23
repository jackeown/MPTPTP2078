%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:29 EST 2020

% Result     : Theorem 3.23s
% Output     : Refutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  105 (1056 expanded)
%              Number of leaves         :   18 ( 305 expanded)
%              Depth                    :   19
%              Number of atoms          :  191 (1875 expanded)
%              Number of equality atoms :   69 ( 606 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6363,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f784,f6354])).

fof(f6354,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f6353])).

fof(f6353,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f789,f6307])).

fof(f6307,plain,(
    ! [X14,X13] : r1_tarski(k7_relat_1(k6_relat_1(X13),X14),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X13),X14)))) ),
    inference(forward_demodulation,[],[f6251,f164])).

fof(f164,plain,(
    ! [X4,X5] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(X4),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) ),
    inference(resolution,[],[f157,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f118,f88])).

fof(f88,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f46,f37])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f117,f37])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f50,f40])).

fof(f40,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f157,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(backward_demodulation,[],[f61,f156])).

fof(f156,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f153,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f153,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(resolution,[],[f62,f37])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f6251,plain,(
    ! [X14,X13] : r1_tarski(k7_relat_1(k6_relat_1(X13),X14),k7_relat_1(k6_relat_1(X13),k1_relat_1(k7_relat_1(k6_relat_1(X13),X14)))) ),
    inference(superposition,[],[f260,f1545])).

fof(f1545,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    inference(superposition,[],[f130,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f100,f46])).

fof(f100,plain,(
    ! [X6,X5] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) ),
    inference(subsumption_resolution,[],[f99,f37])).

fof(f99,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(subsumption_resolution,[],[f96,f37])).

fof(f96,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))
      | ~ v1_relat_1(k6_relat_1(X6))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(superposition,[],[f53,f88])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f130,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(resolution,[],[f124,f100])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(resolution,[],[f51,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f260,plain,(
    ! [X28,X29,X27] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X28),X27),X29),k7_relat_1(k6_relat_1(X28),X29)) ),
    inference(superposition,[],[f204,f247])).

fof(f247,plain,(
    ! [X4,X5] : k7_relat_1(k6_relat_1(X4),X5) = k7_relat_1(k6_relat_1(X5),X4) ),
    inference(subsumption_resolution,[],[f244,f240])).

fof(f240,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[],[f204,f228])).

fof(f228,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[],[f113,f167])).

fof(f167,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(subsumption_resolution,[],[f162,f100])).

fof(f162,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f157,f51])).

fof(f244,plain,(
    ! [X4,X5] :
      ( k7_relat_1(k6_relat_1(X4),X5) = k7_relat_1(k6_relat_1(X5),X4)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k7_relat_1(k6_relat_1(X5),X4)) ) ),
    inference(resolution,[],[f240,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f204,plain,(
    ! [X4,X5,X3] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(subsumption_resolution,[],[f200,f100])).

fof(f200,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(superposition,[],[f48,f196])).

fof(f196,plain,(
    ! [X2,X0,X1] : k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(forward_demodulation,[],[f193,f88])).

fof(f193,plain,(
    ! [X2,X0,X1] : k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f138,f37])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f52,f37])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f789,plain,
    ( ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))))
    | spl2_4 ),
    inference(forward_demodulation,[],[f110,f156])).

fof(f110,plain,
    ( ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_4
  <=> r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f784,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f774])).

fof(f774,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f753,f158])).

fof(f158,plain,
    ( ~ r1_tarski(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))),k7_relat_1(k6_relat_1(sK0),sK1))
    | spl2_3 ),
    inference(backward_demodulation,[],[f106,f156])).

fof(f106,plain,
    ( ~ r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl2_3
  <=> r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f753,plain,(
    ! [X2,X1] : r1_tarski(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(superposition,[],[f733,f247])).

fof(f733,plain,(
    ! [X0,X1] : r1_tarski(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[],[f681,f163])).

fof(f163,plain,(
    ! [X2,X3] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2) ),
    inference(resolution,[],[f157,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f126,f88])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f125,f37])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f51,f39])).

fof(f681,plain,(
    ! [X4,X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X2))),X4),k7_relat_1(k6_relat_1(X2),X4)) ),
    inference(superposition,[],[f526,f247])).

fof(f526,plain,(
    ! [X30,X31,X29] : r1_tarski(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X29),X30))),X31),k7_relat_1(k6_relat_1(X29),X31)) ),
    inference(superposition,[],[f204,f163])).

fof(f112,plain,
    ( ~ spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f102,f104,f108])).

fof(f102,plain,
    ( ~ r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))
    | ~ r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) ),
    inference(extensionality_resolution,[],[f56,f91])).

fof(f91,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f60,f88])).

fof(f60,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f36,f59])).

fof(f36,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f32])).

fof(f32,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (2677)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (2659)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (2669)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.21/0.51  % (2658)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.21/0.51  % (2670)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.21/0.51  % (2655)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.21/0.52  % (2677)Refutation not found, incomplete strategy% (2677)------------------------------
% 1.21/0.52  % (2677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (2669)Refutation not found, incomplete strategy% (2669)------------------------------
% 1.21/0.52  % (2669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (2669)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (2669)Memory used [KB]: 1663
% 1.21/0.52  % (2669)Time elapsed: 0.116 s
% 1.21/0.52  % (2669)------------------------------
% 1.21/0.52  % (2669)------------------------------
% 1.21/0.52  % (2677)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (2677)Memory used [KB]: 6140
% 1.21/0.52  % (2677)Time elapsed: 0.116 s
% 1.21/0.52  % (2677)------------------------------
% 1.21/0.52  % (2677)------------------------------
% 1.21/0.52  % (2673)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.21/0.52  % (2678)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.21/0.52  % (2678)Refutation not found, incomplete strategy% (2678)------------------------------
% 1.21/0.52  % (2678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (2652)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.21/0.52  % (2678)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (2678)Memory used [KB]: 6140
% 1.21/0.52  % (2678)Time elapsed: 0.114 s
% 1.21/0.52  % (2678)------------------------------
% 1.21/0.52  % (2678)------------------------------
% 1.21/0.52  % (2652)Refutation not found, incomplete strategy% (2652)------------------------------
% 1.21/0.52  % (2652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (2652)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (2652)Memory used [KB]: 1663
% 1.21/0.52  % (2652)Time elapsed: 0.115 s
% 1.21/0.52  % (2652)------------------------------
% 1.21/0.52  % (2652)------------------------------
% 1.35/0.53  % (2653)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.35/0.53  % (2665)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.35/0.53  % (2665)Refutation not found, incomplete strategy% (2665)------------------------------
% 1.35/0.53  % (2665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (2665)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (2665)Memory used [KB]: 1663
% 1.35/0.53  % (2665)Time elapsed: 0.093 s
% 1.35/0.53  % (2665)------------------------------
% 1.35/0.53  % (2665)------------------------------
% 1.35/0.53  % (2676)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.35/0.53  % (2651)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.35/0.53  % (2654)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.35/0.53  % (2674)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.35/0.53  % (2676)Refutation not found, incomplete strategy% (2676)------------------------------
% 1.35/0.53  % (2676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (2676)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (2676)Memory used [KB]: 6140
% 1.35/0.53  % (2676)Time elapsed: 0.129 s
% 1.35/0.53  % (2676)------------------------------
% 1.35/0.53  % (2676)------------------------------
% 1.35/0.53  % (2672)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.35/0.53  % (2675)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.35/0.54  % (2656)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.35/0.54  % (2660)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.35/0.54  % (2675)Refutation not found, incomplete strategy% (2675)------------------------------
% 1.35/0.54  % (2675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (2675)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (2675)Memory used [KB]: 10618
% 1.35/0.54  % (2675)Time elapsed: 0.127 s
% 1.35/0.54  % (2675)------------------------------
% 1.35/0.54  % (2675)------------------------------
% 1.35/0.54  % (2667)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.35/0.54  % (2671)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.35/0.54  % (2657)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.54  % (2667)Refutation not found, incomplete strategy% (2667)------------------------------
% 1.35/0.54  % (2667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (2667)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (2667)Memory used [KB]: 10618
% 1.35/0.54  % (2667)Time elapsed: 0.139 s
% 1.35/0.54  % (2667)------------------------------
% 1.35/0.54  % (2667)------------------------------
% 1.35/0.54  % (2666)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.35/0.54  % (2668)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.35/0.54  % (2668)Refutation not found, incomplete strategy% (2668)------------------------------
% 1.35/0.54  % (2668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (2668)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (2668)Memory used [KB]: 1663
% 1.35/0.54  % (2668)Time elapsed: 0.140 s
% 1.35/0.54  % (2668)------------------------------
% 1.35/0.54  % (2668)------------------------------
% 1.35/0.54  % (2663)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.35/0.54  % (2663)Refutation not found, incomplete strategy% (2663)------------------------------
% 1.35/0.54  % (2663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (2663)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (2663)Memory used [KB]: 10618
% 1.35/0.54  % (2663)Time elapsed: 0.141 s
% 1.35/0.54  % (2663)------------------------------
% 1.35/0.54  % (2663)------------------------------
% 1.35/0.54  % (2680)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.35/0.55  % (2680)Refutation not found, incomplete strategy% (2680)------------------------------
% 1.35/0.55  % (2680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (2680)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (2680)Memory used [KB]: 1663
% 1.35/0.55  % (2680)Time elapsed: 0.138 s
% 1.35/0.55  % (2680)------------------------------
% 1.35/0.55  % (2680)------------------------------
% 1.35/0.55  % (2662)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.35/0.55  % (2662)Refutation not found, incomplete strategy% (2662)------------------------------
% 1.35/0.55  % (2662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (2662)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (2662)Memory used [KB]: 6140
% 1.35/0.55  % (2662)Time elapsed: 0.139 s
% 1.35/0.55  % (2662)------------------------------
% 1.35/0.55  % (2662)------------------------------
% 1.35/0.55  % (2664)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.35/0.55  % (2679)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.35/0.55  % (2679)Refutation not found, incomplete strategy% (2679)------------------------------
% 1.35/0.55  % (2679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (2679)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (2679)Memory used [KB]: 10618
% 1.35/0.55  % (2679)Time elapsed: 0.148 s
% 1.35/0.55  % (2679)------------------------------
% 1.35/0.55  % (2679)------------------------------
% 1.35/0.55  % (2661)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.35/0.55  % (2661)Refutation not found, incomplete strategy% (2661)------------------------------
% 1.35/0.55  % (2661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (2661)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (2661)Memory used [KB]: 10618
% 1.35/0.55  % (2661)Time elapsed: 0.149 s
% 1.35/0.55  % (2661)------------------------------
% 1.35/0.55  % (2661)------------------------------
% 1.35/0.60  % (2681)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.35/0.62  % (2682)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.91/0.63  % (2659)Refutation not found, incomplete strategy% (2659)------------------------------
% 1.91/0.63  % (2659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.63  % (2659)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.63  
% 1.91/0.63  % (2659)Memory used [KB]: 6140
% 1.91/0.63  % (2659)Time elapsed: 0.217 s
% 1.91/0.63  % (2659)------------------------------
% 1.91/0.63  % (2659)------------------------------
% 1.91/0.65  % (2687)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.91/0.65  % (2653)Refutation not found, incomplete strategy% (2653)------------------------------
% 1.91/0.65  % (2653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.65  % (2653)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.65  
% 1.91/0.65  % (2653)Memory used [KB]: 6140
% 1.91/0.65  % (2653)Time elapsed: 0.246 s
% 1.91/0.65  % (2653)------------------------------
% 1.91/0.65  % (2653)------------------------------
% 1.91/0.66  % (2654)Refutation not found, incomplete strategy% (2654)------------------------------
% 1.91/0.66  % (2654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.66  % (2654)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.66  
% 1.91/0.66  % (2654)Memory used [KB]: 6140
% 1.91/0.66  % (2654)Time elapsed: 0.245 s
% 1.91/0.66  % (2654)------------------------------
% 1.91/0.66  % (2654)------------------------------
% 1.91/0.66  % (2685)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.91/0.66  % (2685)Refutation not found, incomplete strategy% (2685)------------------------------
% 1.91/0.66  % (2685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.66  % (2685)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.66  
% 1.91/0.66  % (2685)Memory used [KB]: 10618
% 1.91/0.66  % (2685)Time elapsed: 0.109 s
% 1.91/0.66  % (2685)------------------------------
% 1.91/0.66  % (2685)------------------------------
% 1.91/0.67  % (2688)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 1.91/0.67  % (2688)Refutation not found, incomplete strategy% (2688)------------------------------
% 1.91/0.67  % (2688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.67  % (2688)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.67  
% 1.91/0.67  % (2688)Memory used [KB]: 10618
% 1.91/0.67  % (2688)Time elapsed: 0.100 s
% 1.91/0.67  % (2688)------------------------------
% 1.91/0.67  % (2688)------------------------------
% 1.91/0.67  % (2683)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.91/0.67  % (2687)Refutation not found, incomplete strategy% (2687)------------------------------
% 1.91/0.67  % (2687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.67  % (2687)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.67  
% 1.91/0.67  % (2687)Memory used [KB]: 1663
% 1.91/0.67  % (2687)Time elapsed: 0.113 s
% 1.91/0.67  % (2687)------------------------------
% 1.91/0.67  % (2687)------------------------------
% 1.91/0.67  % (2691)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 1.91/0.67  % (2666)Refutation not found, incomplete strategy% (2666)------------------------------
% 1.91/0.67  % (2666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.67  % (2666)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.67  
% 1.91/0.67  % (2666)Memory used [KB]: 6140
% 1.91/0.67  % (2666)Time elapsed: 0.248 s
% 1.91/0.67  % (2666)------------------------------
% 1.91/0.67  % (2666)------------------------------
% 1.91/0.67  % (2691)Refutation not found, incomplete strategy% (2691)------------------------------
% 1.91/0.67  % (2691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.67  % (2691)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.67  
% 1.91/0.67  % (2691)Memory used [KB]: 10618
% 1.91/0.67  % (2691)Time elapsed: 0.102 s
% 1.91/0.67  % (2691)------------------------------
% 1.91/0.67  % (2691)------------------------------
% 1.91/0.68  % (2693)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 1.91/0.68  % (2693)Refutation not found, incomplete strategy% (2693)------------------------------
% 1.91/0.68  % (2693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.68  % (2693)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.68  
% 1.91/0.68  % (2693)Memory used [KB]: 10618
% 1.91/0.68  % (2693)Time elapsed: 0.112 s
% 1.91/0.68  % (2693)------------------------------
% 1.91/0.68  % (2693)------------------------------
% 1.91/0.68  % (2694)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 1.91/0.69  % (2689)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 1.91/0.69  % (2695)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 1.91/0.70  % (2695)Refutation not found, incomplete strategy% (2695)------------------------------
% 1.91/0.70  % (2695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.70  % (2695)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.70  
% 1.91/0.70  % (2695)Memory used [KB]: 10618
% 1.91/0.70  % (2695)Time elapsed: 0.119 s
% 1.91/0.70  % (2695)------------------------------
% 1.91/0.70  % (2695)------------------------------
% 2.39/0.70  % (2686)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.39/0.70  % (2686)Refutation not found, incomplete strategy% (2686)------------------------------
% 2.39/0.70  % (2686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.39/0.70  % (2686)Termination reason: Refutation not found, incomplete strategy
% 2.39/0.70  
% 2.39/0.70  % (2686)Memory used [KB]: 10618
% 2.39/0.70  % (2686)Time elapsed: 0.144 s
% 2.39/0.70  % (2686)------------------------------
% 2.39/0.70  % (2686)------------------------------
% 2.39/0.70  % (2690)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.39/0.71  % (2692)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.39/0.75  % (2696)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.39/0.76  % (2698)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.73/0.78  % (2699)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.73/0.79  % (2697)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.73/0.80  % (2700)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 2.73/0.80  % (2701)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 2.73/0.80  % (2701)Refutation not found, incomplete strategy% (2701)------------------------------
% 2.73/0.80  % (2701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.80  % (2701)Termination reason: Refutation not found, incomplete strategy
% 2.73/0.80  
% 2.73/0.80  % (2701)Memory used [KB]: 1663
% 2.73/0.80  % (2701)Time elapsed: 0.107 s
% 2.73/0.80  % (2701)------------------------------
% 2.73/0.80  % (2701)------------------------------
% 2.73/0.82  % (2690)Refutation not found, incomplete strategy% (2690)------------------------------
% 2.73/0.82  % (2690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.82  % (2690)Termination reason: Refutation not found, incomplete strategy
% 2.73/0.82  
% 2.73/0.82  % (2690)Memory used [KB]: 6268
% 2.73/0.82  % (2690)Time elapsed: 0.233 s
% 2.73/0.82  % (2690)------------------------------
% 2.73/0.82  % (2690)------------------------------
% 2.73/0.82  % (2702)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.23/0.87  % (2696)Refutation not found, incomplete strategy% (2696)------------------------------
% 3.23/0.87  % (2696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.23/0.87  % (2696)Termination reason: Refutation not found, incomplete strategy
% 3.23/0.87  
% 3.23/0.87  % (2696)Memory used [KB]: 6140
% 3.23/0.87  % (2696)Time elapsed: 0.146 s
% 3.23/0.87  % (2696)------------------------------
% 3.23/0.87  % (2696)------------------------------
% 3.23/0.90  % (2657)Refutation found. Thanks to Tanya!
% 3.23/0.90  % SZS status Theorem for theBenchmark
% 3.23/0.90  % SZS output start Proof for theBenchmark
% 3.23/0.90  fof(f6363,plain,(
% 3.23/0.90    $false),
% 3.23/0.90    inference(avatar_sat_refutation,[],[f112,f784,f6354])).
% 3.23/0.90  fof(f6354,plain,(
% 3.23/0.90    spl2_4),
% 3.23/0.90    inference(avatar_contradiction_clause,[],[f6353])).
% 3.23/0.90  fof(f6353,plain,(
% 3.23/0.90    $false | spl2_4),
% 3.23/0.90    inference(subsumption_resolution,[],[f789,f6307])).
% 3.23/0.90  fof(f6307,plain,(
% 3.23/0.90    ( ! [X14,X13] : (r1_tarski(k7_relat_1(k6_relat_1(X13),X14),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X13),X14))))) )),
% 3.23/0.90    inference(forward_demodulation,[],[f6251,f164])).
% 3.23/0.90  fof(f164,plain,(
% 3.23/0.90    ( ! [X4,X5] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(X4),k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)))) )),
% 3.23/0.90    inference(resolution,[],[f157,f119])).
% 3.23/0.90  fof(f119,plain,(
% 3.23/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 3.23/0.90    inference(forward_demodulation,[],[f118,f88])).
% 3.23/0.90  fof(f88,plain,(
% 3.23/0.90    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 3.23/0.90    inference(resolution,[],[f46,f37])).
% 3.23/0.90  fof(f37,plain,(
% 3.23/0.90    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.23/0.90    inference(cnf_transformation,[],[f16])).
% 3.23/0.90  fof(f16,axiom,(
% 3.23/0.90    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 3.23/0.90  fof(f46,plain,(
% 3.23/0.90    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 3.23/0.90    inference(cnf_transformation,[],[f22])).
% 3.23/0.90  fof(f22,plain,(
% 3.23/0.90    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.23/0.90    inference(ennf_transformation,[],[f15])).
% 3.23/0.90  fof(f15,axiom,(
% 3.23/0.90    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 3.23/0.90  fof(f118,plain,(
% 3.23/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 3.23/0.90    inference(subsumption_resolution,[],[f117,f37])).
% 3.23/0.90  fof(f117,plain,(
% 3.23/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.23/0.90    inference(superposition,[],[f50,f40])).
% 3.23/0.90  fof(f40,plain,(
% 3.23/0.90    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.23/0.90    inference(cnf_transformation,[],[f9])).
% 3.23/0.90  fof(f9,axiom,(
% 3.23/0.90    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 3.23/0.90  fof(f50,plain,(
% 3.23/0.90    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 3.23/0.90    inference(cnf_transformation,[],[f26])).
% 3.23/0.90  fof(f26,plain,(
% 3.23/0.90    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.23/0.90    inference(flattening,[],[f25])).
% 3.23/0.90  fof(f25,plain,(
% 3.23/0.90    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.23/0.90    inference(ennf_transformation,[],[f12])).
% 3.23/0.90  fof(f12,axiom,(
% 3.23/0.90    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 3.23/0.90  fof(f157,plain,(
% 3.23/0.90    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 3.23/0.90    inference(backward_demodulation,[],[f61,f156])).
% 3.23/0.90  fof(f156,plain,(
% 3.23/0.90    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 3.23/0.90    inference(forward_demodulation,[],[f153,f39])).
% 3.23/0.90  fof(f39,plain,(
% 3.23/0.90    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.23/0.90    inference(cnf_transformation,[],[f9])).
% 3.23/0.90  fof(f153,plain,(
% 3.23/0.90    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))) )),
% 3.23/0.90    inference(resolution,[],[f62,f37])).
% 3.23/0.90  fof(f62,plain,(
% 3.23/0.90    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 3.23/0.90    inference(definition_unfolding,[],[f47,f59])).
% 3.23/0.90  fof(f59,plain,(
% 3.23/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 3.23/0.90    inference(definition_unfolding,[],[f44,f58])).
% 3.23/0.90  fof(f58,plain,(
% 3.23/0.90    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.23/0.90    inference(definition_unfolding,[],[f45,f57])).
% 3.23/0.90  fof(f57,plain,(
% 3.23/0.90    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.23/0.90    inference(cnf_transformation,[],[f4])).
% 3.23/0.90  fof(f4,axiom,(
% 3.23/0.90    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.23/0.90  fof(f45,plain,(
% 3.23/0.90    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.23/0.90    inference(cnf_transformation,[],[f3])).
% 3.23/0.90  fof(f3,axiom,(
% 3.23/0.90    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.23/0.90  fof(f44,plain,(
% 3.23/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.23/0.90    inference(cnf_transformation,[],[f5])).
% 3.23/0.90  fof(f5,axiom,(
% 3.23/0.90    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.23/0.90  fof(f47,plain,(
% 3.23/0.90    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.23/0.90    inference(cnf_transformation,[],[f23])).
% 3.23/0.90  fof(f23,plain,(
% 3.23/0.90    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.23/0.90    inference(ennf_transformation,[],[f14])).
% 3.23/0.90  fof(f14,axiom,(
% 3.23/0.90    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 3.23/0.90  fof(f61,plain,(
% 3.23/0.90    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 3.23/0.90    inference(definition_unfolding,[],[f43,f59])).
% 3.23/0.90  fof(f43,plain,(
% 3.23/0.90    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.23/0.90    inference(cnf_transformation,[],[f2])).
% 3.23/0.90  fof(f2,axiom,(
% 3.23/0.90    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.23/0.90  fof(f6251,plain,(
% 3.23/0.90    ( ! [X14,X13] : (r1_tarski(k7_relat_1(k6_relat_1(X13),X14),k7_relat_1(k6_relat_1(X13),k1_relat_1(k7_relat_1(k6_relat_1(X13),X14))))) )),
% 3.23/0.90    inference(superposition,[],[f260,f1545])).
% 3.23/0.90  fof(f1545,plain,(
% 3.23/0.90    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) )),
% 3.23/0.90    inference(superposition,[],[f130,f113])).
% 3.23/0.90  fof(f113,plain,(
% 3.23/0.90    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) )),
% 3.23/0.90    inference(resolution,[],[f100,f46])).
% 3.23/0.90  fof(f100,plain,(
% 3.23/0.90    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5))) )),
% 3.23/0.90    inference(subsumption_resolution,[],[f99,f37])).
% 3.23/0.90  fof(f99,plain,(
% 3.23/0.90    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 3.23/0.90    inference(subsumption_resolution,[],[f96,f37])).
% 3.23/0.90  fof(f96,plain,(
% 3.23/0.90    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X5)) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 3.23/0.90    inference(superposition,[],[f53,f88])).
% 3.23/0.90  fof(f53,plain,(
% 3.23/0.90    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.23/0.90    inference(cnf_transformation,[],[f31])).
% 3.23/0.90  fof(f31,plain,(
% 3.23/0.90    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.23/0.90    inference(flattening,[],[f30])).
% 3.23/0.90  fof(f30,plain,(
% 3.23/0.90    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.23/0.90    inference(ennf_transformation,[],[f6])).
% 3.23/0.90  fof(f6,axiom,(
% 3.23/0.90    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 3.23/0.90  fof(f130,plain,(
% 3.23/0.90    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))),k7_relat_1(k6_relat_1(X3),X4))) )),
% 3.23/0.90    inference(resolution,[],[f124,f100])).
% 3.23/0.90  fof(f124,plain,(
% 3.23/0.90    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 3.23/0.90    inference(resolution,[],[f51,f63])).
% 3.23/0.90  fof(f63,plain,(
% 3.23/0.90    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.23/0.90    inference(equality_resolution,[],[f55])).
% 3.23/0.90  fof(f55,plain,(
% 3.23/0.90    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.23/0.90    inference(cnf_transformation,[],[f35])).
% 3.23/0.90  fof(f35,plain,(
% 3.23/0.90    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/0.90    inference(flattening,[],[f34])).
% 3.23/0.90  fof(f34,plain,(
% 3.23/0.90    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/0.90    inference(nnf_transformation,[],[f1])).
% 3.23/0.90  fof(f1,axiom,(
% 3.23/0.90    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.23/0.90  fof(f51,plain,(
% 3.23/0.90    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 3.23/0.90    inference(cnf_transformation,[],[f28])).
% 3.23/0.90  fof(f28,plain,(
% 3.23/0.90    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.23/0.90    inference(flattening,[],[f27])).
% 3.23/0.90  fof(f27,plain,(
% 3.23/0.90    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.23/0.90    inference(ennf_transformation,[],[f11])).
% 3.23/0.90  fof(f11,axiom,(
% 3.23/0.90    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 3.23/0.90  fof(f260,plain,(
% 3.23/0.90    ( ! [X28,X29,X27] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X28),X27),X29),k7_relat_1(k6_relat_1(X28),X29))) )),
% 3.23/0.90    inference(superposition,[],[f204,f247])).
% 3.23/0.90  fof(f247,plain,(
% 3.23/0.90    ( ! [X4,X5] : (k7_relat_1(k6_relat_1(X4),X5) = k7_relat_1(k6_relat_1(X5),X4)) )),
% 3.23/0.90    inference(subsumption_resolution,[],[f244,f240])).
% 3.23/0.90  fof(f240,plain,(
% 3.23/0.90    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0))) )),
% 3.23/0.90    inference(superposition,[],[f204,f228])).
% 3.23/0.90  fof(f228,plain,(
% 3.23/0.90    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 3.23/0.90    inference(superposition,[],[f113,f167])).
% 3.23/0.90  fof(f167,plain,(
% 3.23/0.90    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) )),
% 3.23/0.90    inference(subsumption_resolution,[],[f162,f100])).
% 3.23/0.90  fof(f162,plain,(
% 3.23/0.90    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 3.23/0.90    inference(resolution,[],[f157,f51])).
% 3.23/0.90  fof(f244,plain,(
% 3.23/0.90    ( ! [X4,X5] : (k7_relat_1(k6_relat_1(X4),X5) = k7_relat_1(k6_relat_1(X5),X4) | ~r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k7_relat_1(k6_relat_1(X5),X4))) )),
% 3.23/0.90    inference(resolution,[],[f240,f56])).
% 3.23/0.90  fof(f56,plain,(
% 3.23/0.90    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.23/0.90    inference(cnf_transformation,[],[f35])).
% 3.23/0.90  fof(f204,plain,(
% 3.23/0.90    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4))) )),
% 3.23/0.90    inference(subsumption_resolution,[],[f200,f100])).
% 3.23/0.90  fof(f200,plain,(
% 3.23/0.90    ( ! [X4,X5,X3] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4),k7_relat_1(k6_relat_1(X3),X4)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 3.23/0.90    inference(superposition,[],[f48,f196])).
% 3.23/0.90  fof(f196,plain,(
% 3.23/0.90    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) )),
% 3.23/0.90    inference(forward_demodulation,[],[f193,f88])).
% 3.23/0.90  fof(f193,plain,(
% 3.23/0.90    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))) )),
% 3.23/0.90    inference(resolution,[],[f138,f37])).
% 3.23/0.90  fof(f138,plain,(
% 3.23/0.90    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1))) )),
% 3.23/0.90    inference(resolution,[],[f52,f37])).
% 3.23/0.90  fof(f52,plain,(
% 3.23/0.90    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X1)) )),
% 3.23/0.90    inference(cnf_transformation,[],[f29])).
% 3.23/0.90  fof(f29,plain,(
% 3.23/0.90    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.23/0.90    inference(ennf_transformation,[],[f7])).
% 3.23/0.90  fof(f7,axiom,(
% 3.23/0.90    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 3.23/0.90  fof(f48,plain,(
% 3.23/0.90    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 3.23/0.90    inference(cnf_transformation,[],[f24])).
% 3.23/0.90  fof(f24,plain,(
% 3.23/0.90    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 3.23/0.90    inference(ennf_transformation,[],[f10])).
% 3.23/0.90  fof(f10,axiom,(
% 3.23/0.90    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 3.23/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 3.23/0.90  fof(f789,plain,(
% 3.23/0.90    ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))) | spl2_4),
% 3.23/0.90    inference(forward_demodulation,[],[f110,f156])).
% 3.23/0.90  fof(f110,plain,(
% 3.23/0.90    ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) | spl2_4),
% 3.23/0.90    inference(avatar_component_clause,[],[f108])).
% 3.23/0.90  fof(f108,plain,(
% 3.23/0.90    spl2_4 <=> r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))),
% 3.23/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 3.23/0.90  fof(f784,plain,(
% 3.23/0.90    spl2_3),
% 3.23/0.90    inference(avatar_contradiction_clause,[],[f774])).
% 3.23/0.90  fof(f774,plain,(
% 3.23/0.90    $false | spl2_3),
% 3.23/0.90    inference(resolution,[],[f753,f158])).
% 3.23/0.90  fof(f158,plain,(
% 3.23/0.90    ~r1_tarski(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) | spl2_3),
% 3.23/0.90    inference(backward_demodulation,[],[f106,f156])).
% 3.23/0.90  fof(f106,plain,(
% 3.23/0.90    ~r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) | spl2_3),
% 3.23/0.90    inference(avatar_component_clause,[],[f104])).
% 3.23/0.90  fof(f104,plain,(
% 3.23/0.90    spl2_3 <=> r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1))),
% 3.23/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.23/0.90  fof(f753,plain,(
% 3.23/0.90    ( ! [X2,X1] : (r1_tarski(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))),k7_relat_1(k6_relat_1(X2),X1))) )),
% 3.23/0.90    inference(superposition,[],[f733,f247])).
% 3.23/0.90  fof(f733,plain,(
% 3.23/0.90    ( ! [X0,X1] : (r1_tarski(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X1),X0))) )),
% 3.23/0.90    inference(superposition,[],[f681,f163])).
% 3.23/0.90  fof(f163,plain,(
% 3.23/0.90    ( ! [X2,X3] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2)) )),
% 3.23/0.90    inference(resolution,[],[f157,f127])).
% 3.23/0.90  fof(f127,plain,(
% 3.23/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 3.23/0.90    inference(forward_demodulation,[],[f126,f88])).
% 3.23/0.90  fof(f126,plain,(
% 3.23/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 3.23/0.90    inference(subsumption_resolution,[],[f125,f37])).
% 3.23/0.90  fof(f125,plain,(
% 3.23/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.23/0.90    inference(superposition,[],[f51,f39])).
% 3.23/0.90  fof(f681,plain,(
% 3.23/0.90    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X2))),X4),k7_relat_1(k6_relat_1(X2),X4))) )),
% 3.23/0.90    inference(superposition,[],[f526,f247])).
% 3.23/0.90  fof(f526,plain,(
% 3.23/0.90    ( ! [X30,X31,X29] : (r1_tarski(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X29),X30))),X31),k7_relat_1(k6_relat_1(X29),X31))) )),
% 3.23/0.90    inference(superposition,[],[f204,f163])).
% 3.23/0.90  fof(f112,plain,(
% 3.23/0.90    ~spl2_4 | ~spl2_3),
% 3.23/0.90    inference(avatar_split_clause,[],[f102,f104,f108])).
% 3.23/0.90  fof(f102,plain,(
% 3.23/0.90    ~r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k7_relat_1(k6_relat_1(sK0),sK1)) | ~r1_tarski(k7_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))),
% 3.23/0.90    inference(extensionality_resolution,[],[f56,f91])).
% 3.23/0.90  fof(f91,plain,(
% 3.23/0.90    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 3.23/0.90    inference(backward_demodulation,[],[f60,f88])).
% 3.23/0.90  fof(f60,plain,(
% 3.23/0.90    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 3.23/0.90    inference(definition_unfolding,[],[f36,f59])).
% 3.23/0.90  fof(f36,plain,(
% 3.23/0.90    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.23/0.90    inference(cnf_transformation,[],[f33])).
% 3.44/0.90  fof(f33,plain,(
% 3.44/0.90    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.44/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f32])).
% 3.44/0.90  fof(f32,plain,(
% 3.44/0.90    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.44/0.90    introduced(choice_axiom,[])).
% 3.44/0.90  fof(f19,plain,(
% 3.44/0.90    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.44/0.90    inference(ennf_transformation,[],[f18])).
% 3.44/0.90  fof(f18,negated_conjecture,(
% 3.44/0.90    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.44/0.90    inference(negated_conjecture,[],[f17])).
% 3.44/0.90  fof(f17,conjecture,(
% 3.44/0.90    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.44/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 3.44/0.90  % SZS output end Proof for theBenchmark
% 3.44/0.90  % (2657)------------------------------
% 3.44/0.90  % (2657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.44/0.90  % (2657)Termination reason: Refutation
% 3.44/0.90  
% 3.44/0.90  % (2657)Memory used [KB]: 14583
% 3.44/0.90  % (2657)Time elapsed: 0.459 s
% 3.44/0.90  % (2657)------------------------------
% 3.44/0.90  % (2657)------------------------------
% 3.44/0.90  % (2650)Success in time 0.531 s
%------------------------------------------------------------------------------
