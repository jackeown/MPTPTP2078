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
% DateTime   : Thu Dec  3 12:52:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 222 expanded)
%              Number of leaves         :   14 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          :  177 ( 407 expanded)
%              Number of equality atoms :   63 ( 152 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1009,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f998])).

fof(f998,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f90,f883])).

fof(f883,plain,(
    ! [X6,X5] : k7_relat_1(k6_relat_1(X6),X5) = k6_relat_1(k3_xboole_0(X6,X5)) ),
    inference(backward_demodulation,[],[f113,f882])).

fof(f882,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k3_xboole_0(X2,X3)) ),
    inference(subsumption_resolution,[],[f860,f251])).

fof(f251,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f221,f63])).

fof(f63,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f59,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f45,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f221,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(subsumption_resolution,[],[f216,f38])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f216,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f212,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f212,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f135,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

% (12898)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% (12897)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% (12911)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f135,plain,(
    ! [X6,X5] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X6,X5)),X5)
      | ~ v1_relat_1(X6) ) ),
    inference(forward_demodulation,[],[f134,f39])).

fof(f134,plain,(
    ! [X6,X5] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X6,X5)),k1_relat_1(k6_relat_1(X5)))
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f125,f38])).

fof(f125,plain,(
    ! [X6,X5] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X6,X5)),k1_relat_1(k6_relat_1(X5)))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X6,X5] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X6,X5)),k1_relat_1(k6_relat_1(X5)))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(k6_relat_1(X5))
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f43,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f860,plain,(
    ! [X2,X3] :
      ( k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k3_xboole_0(X2,X3))
      | ~ r1_tarski(k3_xboole_0(X2,X3),X2) ) ),
    inference(superposition,[],[f626,f159])).

fof(f159,plain,(
    ! [X8,X7] :
      ( k6_relat_1(X7) = k8_relat_1(X8,k6_relat_1(X7))
      | ~ r1_tarski(X7,X8) ) ),
    inference(forward_demodulation,[],[f158,f40])).

fof(f40,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f158,plain,(
    ! [X8,X7] :
      ( k6_relat_1(X7) = k8_relat_1(X8,k6_relat_1(X7))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X7)),X8) ) ),
    inference(forward_demodulation,[],[f157,f113])).

fof(f157,plain,(
    ! [X8,X7] :
      ( k6_relat_1(X7) = k7_relat_1(k6_relat_1(X8),X7)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X7)),X8) ) ),
    inference(subsumption_resolution,[],[f156,f38])).

fof(f156,plain,(
    ! [X8,X7] :
      ( k6_relat_1(X7) = k7_relat_1(k6_relat_1(X8),X7)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X7)),X8)
      | ~ v1_relat_1(k6_relat_1(X8)) ) ),
    inference(subsumption_resolution,[],[f143,f38])).

fof(f143,plain,(
    ! [X8,X7] :
      ( k6_relat_1(X7) = k7_relat_1(k6_relat_1(X8),X7)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X7)),X8)
      | ~ v1_relat_1(k6_relat_1(X7))
      | ~ v1_relat_1(k6_relat_1(X8)) ) ),
    inference(superposition,[],[f51,f48])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f626,plain,(
    ! [X14,X13] : k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14))) ),
    inference(subsumption_resolution,[],[f625,f221])).

fof(f625,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(k3_xboole_0(X13,X14),X14)
      | k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14))) ) ),
    inference(forward_demodulation,[],[f624,f234])).

fof(f234,plain,(
    ! [X4,X3] : k1_relat_1(k8_relat_1(X3,k6_relat_1(X4))) = k3_xboole_0(X3,X4) ),
    inference(forward_demodulation,[],[f233,f39])).

fof(f233,plain,(
    ! [X4,X3] : k3_xboole_0(k1_relat_1(k6_relat_1(X3)),X4) = k1_relat_1(k8_relat_1(X3,k6_relat_1(X4))) ),
    inference(subsumption_resolution,[],[f227,f38])).

fof(f227,plain,(
    ! [X4,X3] :
      ( k3_xboole_0(k1_relat_1(k6_relat_1(X3)),X4) = k1_relat_1(k8_relat_1(X3,k6_relat_1(X4)))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f50,f113])).

fof(f624,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))),X14)
      | k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14))) ) ),
    inference(forward_demodulation,[],[f623,f40])).

fof(f623,plain,(
    ! [X14,X13] :
      ( k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14)))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14) ) ),
    inference(forward_demodulation,[],[f622,f234])).

fof(f622,plain,(
    ! [X14,X13] :
      ( k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14)))))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14) ) ),
    inference(subsumption_resolution,[],[f621,f236])).

% (12905)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f236,plain,(
    ! [X6,X5] : v1_relat_1(k8_relat_1(X5,k6_relat_1(X6))) ),
    inference(subsumption_resolution,[],[f228,f38])).

fof(f228,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k8_relat_1(X5,k6_relat_1(X6)))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(superposition,[],[f91,f113])).

fof(f91,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k7_relat_1(X3,X2))
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f83,f38])).

fof(f83,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k7_relat_1(X3,X2))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k7_relat_1(X3,X2))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f53,f48])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f621,plain,(
    ! [X14,X13] :
      ( k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14)))))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14)
      | ~ v1_relat_1(k8_relat_1(X13,k6_relat_1(X14))) ) ),
    inference(subsumption_resolution,[],[f594,f38])).

fof(f594,plain,(
    ! [X14,X13] :
      ( k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14)))))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14)))))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14)
      | ~ v1_relat_1(k8_relat_1(X13,k6_relat_1(X14))) ) ),
    inference(superposition,[],[f185,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

% (12904)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f185,plain,(
    ! [X4,X2,X3] :
      ( k5_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k8_relat_1(X4,X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X3) ) ),
    inference(subsumption_resolution,[],[f182,f38])).

fof(f182,plain,(
    ! [X4,X2,X3] :
      ( k5_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k8_relat_1(X4,X2)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X3) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X4,X2,X3] :
      ( k5_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k8_relat_1(X4,X2)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f52,f51])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f113,plain,(
    ! [X6,X5] : k7_relat_1(k6_relat_1(X6),X5) = k8_relat_1(X6,k6_relat_1(X5)) ),
    inference(subsumption_resolution,[],[f112,f38])).

fof(f112,plain,(
    ! [X6,X5] :
      ( k7_relat_1(k6_relat_1(X6),X5) = k8_relat_1(X6,k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(subsumption_resolution,[],[f98,f38])).

fof(f98,plain,(
    ! [X6,X5] :
      ( k7_relat_1(k6_relat_1(X6),X5) = k8_relat_1(X6,k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(superposition,[],[f49,f48])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f90,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(subsumption_resolution,[],[f78,f38])).

fof(f78,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f37,f48])).

fof(f37,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f35])).

fof(f35,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (12912)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (12900)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (12916)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (12899)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (12915)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (12909)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (12903)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (12900)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f1009,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f998])).
% 0.21/0.51  fof(f998,plain,(
% 0.21/0.51    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.51    inference(superposition,[],[f90,f883])).
% 0.21/0.51  fof(f883,plain,(
% 0.21/0.51    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X6),X5) = k6_relat_1(k3_xboole_0(X6,X5))) )),
% 0.21/0.51    inference(backward_demodulation,[],[f113,f882])).
% 0.21/0.51  fof(f882,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k3_xboole_0(X2,X3))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f860,f251])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X1)) )),
% 0.21/0.51    inference(superposition,[],[f221,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.21/0.51    inference(superposition,[],[f59,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.21/0.51    inference(superposition,[],[f45,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f216,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(superposition,[],[f212,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X0),X1),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f211])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X0),X1),X1) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(superposition,[],[f135,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  % (12898)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.31/0.52  % (12897)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.31/0.52  % (12911)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.31/0.52  fof(f29,plain,(
% 1.31/0.52    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.31/0.52    inference(ennf_transformation,[],[f19])).
% 1.31/0.52  fof(f19,axiom,(
% 1.31/0.52    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.31/0.52  fof(f135,plain,(
% 1.31/0.52    ( ! [X6,X5] : (r1_tarski(k1_relat_1(k7_relat_1(X6,X5)),X5) | ~v1_relat_1(X6)) )),
% 1.31/0.52    inference(forward_demodulation,[],[f134,f39])).
% 1.31/0.52  fof(f134,plain,(
% 1.31/0.52    ( ! [X6,X5] : (r1_tarski(k1_relat_1(k7_relat_1(X6,X5)),k1_relat_1(k6_relat_1(X5))) | ~v1_relat_1(X6)) )),
% 1.31/0.52    inference(subsumption_resolution,[],[f125,f38])).
% 1.31/0.52  fof(f125,plain,(
% 1.31/0.52    ( ! [X6,X5] : (r1_tarski(k1_relat_1(k7_relat_1(X6,X5)),k1_relat_1(k6_relat_1(X5))) | ~v1_relat_1(X6) | ~v1_relat_1(k6_relat_1(X5))) )),
% 1.31/0.52    inference(duplicate_literal_removal,[],[f123])).
% 1.31/0.52  fof(f123,plain,(
% 1.31/0.52    ( ! [X6,X5] : (r1_tarski(k1_relat_1(k7_relat_1(X6,X5)),k1_relat_1(k6_relat_1(X5))) | ~v1_relat_1(X6) | ~v1_relat_1(k6_relat_1(X5)) | ~v1_relat_1(X6)) )),
% 1.31/0.52    inference(superposition,[],[f43,f48])).
% 1.31/0.52  fof(f48,plain,(
% 1.31/0.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f27])).
% 1.31/0.52  fof(f27,plain,(
% 1.31/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.31/0.52    inference(ennf_transformation,[],[f20])).
% 1.31/0.52  fof(f20,axiom,(
% 1.31/0.52    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.31/0.52  fof(f43,plain,(
% 1.31/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f26])).
% 1.31/0.52  fof(f26,plain,(
% 1.31/0.52    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.31/0.52    inference(ennf_transformation,[],[f14])).
% 1.31/0.52  fof(f14,axiom,(
% 1.31/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 1.31/0.52  fof(f860,plain,(
% 1.31/0.52    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k3_xboole_0(X2,X3)) | ~r1_tarski(k3_xboole_0(X2,X3),X2)) )),
% 1.31/0.52    inference(superposition,[],[f626,f159])).
% 1.31/0.52  fof(f159,plain,(
% 1.31/0.52    ( ! [X8,X7] : (k6_relat_1(X7) = k8_relat_1(X8,k6_relat_1(X7)) | ~r1_tarski(X7,X8)) )),
% 1.31/0.52    inference(forward_demodulation,[],[f158,f40])).
% 1.31/0.52  fof(f40,plain,(
% 1.31/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.31/0.52    inference(cnf_transformation,[],[f15])).
% 1.31/0.52  fof(f158,plain,(
% 1.31/0.52    ( ! [X8,X7] : (k6_relat_1(X7) = k8_relat_1(X8,k6_relat_1(X7)) | ~r1_tarski(k2_relat_1(k6_relat_1(X7)),X8)) )),
% 1.31/0.52    inference(forward_demodulation,[],[f157,f113])).
% 1.31/0.52  fof(f157,plain,(
% 1.31/0.52    ( ! [X8,X7] : (k6_relat_1(X7) = k7_relat_1(k6_relat_1(X8),X7) | ~r1_tarski(k2_relat_1(k6_relat_1(X7)),X8)) )),
% 1.31/0.52    inference(subsumption_resolution,[],[f156,f38])).
% 1.31/0.52  fof(f156,plain,(
% 1.31/0.52    ( ! [X8,X7] : (k6_relat_1(X7) = k7_relat_1(k6_relat_1(X8),X7) | ~r1_tarski(k2_relat_1(k6_relat_1(X7)),X8) | ~v1_relat_1(k6_relat_1(X8))) )),
% 1.31/0.52    inference(subsumption_resolution,[],[f143,f38])).
% 1.31/0.52  fof(f143,plain,(
% 1.31/0.52    ( ! [X8,X7] : (k6_relat_1(X7) = k7_relat_1(k6_relat_1(X8),X7) | ~r1_tarski(k2_relat_1(k6_relat_1(X7)),X8) | ~v1_relat_1(k6_relat_1(X7)) | ~v1_relat_1(k6_relat_1(X8))) )),
% 1.31/0.52    inference(superposition,[],[f51,f48])).
% 1.31/0.52  fof(f51,plain,(
% 1.31/0.52    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f31])).
% 1.31/0.52  fof(f31,plain,(
% 1.31/0.52    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.31/0.52    inference(flattening,[],[f30])).
% 1.31/0.52  fof(f30,plain,(
% 1.31/0.52    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.31/0.52    inference(ennf_transformation,[],[f17])).
% 1.31/0.52  fof(f17,axiom,(
% 1.31/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 1.31/0.52  fof(f626,plain,(
% 1.31/0.52    ( ! [X14,X13] : (k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14)))) )),
% 1.31/0.52    inference(subsumption_resolution,[],[f625,f221])).
% 1.31/0.52  fof(f625,plain,(
% 1.31/0.52    ( ! [X14,X13] : (~r1_tarski(k3_xboole_0(X13,X14),X14) | k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14)))) )),
% 1.31/0.52    inference(forward_demodulation,[],[f624,f234])).
% 1.31/0.52  fof(f234,plain,(
% 1.31/0.52    ( ! [X4,X3] : (k1_relat_1(k8_relat_1(X3,k6_relat_1(X4))) = k3_xboole_0(X3,X4)) )),
% 1.31/0.52    inference(forward_demodulation,[],[f233,f39])).
% 1.31/0.52  fof(f233,plain,(
% 1.31/0.52    ( ! [X4,X3] : (k3_xboole_0(k1_relat_1(k6_relat_1(X3)),X4) = k1_relat_1(k8_relat_1(X3,k6_relat_1(X4)))) )),
% 1.31/0.52    inference(subsumption_resolution,[],[f227,f38])).
% 1.31/0.52  fof(f227,plain,(
% 1.31/0.52    ( ! [X4,X3] : (k3_xboole_0(k1_relat_1(k6_relat_1(X3)),X4) = k1_relat_1(k8_relat_1(X3,k6_relat_1(X4))) | ~v1_relat_1(k6_relat_1(X3))) )),
% 1.31/0.52    inference(superposition,[],[f50,f113])).
% 1.31/0.52  fof(f624,plain,(
% 1.31/0.52    ( ! [X14,X13] : (~r1_tarski(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))),X14) | k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14)))) )),
% 1.31/0.52    inference(forward_demodulation,[],[f623,f40])).
% 1.31/0.52  fof(f623,plain,(
% 1.31/0.52    ( ! [X14,X13] : (k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14)) )),
% 1.31/0.52    inference(forward_demodulation,[],[f622,f234])).
% 1.31/0.52  fof(f622,plain,(
% 1.31/0.52    ( ! [X14,X13] : (k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14)) )),
% 1.31/0.52    inference(subsumption_resolution,[],[f621,f236])).
% 1.31/0.52  % (12905)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.31/0.52  fof(f236,plain,(
% 1.31/0.52    ( ! [X6,X5] : (v1_relat_1(k8_relat_1(X5,k6_relat_1(X6)))) )),
% 1.31/0.52    inference(subsumption_resolution,[],[f228,f38])).
% 1.31/0.52  fof(f228,plain,(
% 1.31/0.52    ( ! [X6,X5] : (v1_relat_1(k8_relat_1(X5,k6_relat_1(X6))) | ~v1_relat_1(k6_relat_1(X5))) )),
% 1.31/0.52    inference(superposition,[],[f91,f113])).
% 1.31/0.52  fof(f91,plain,(
% 1.31/0.52    ( ! [X2,X3] : (v1_relat_1(k7_relat_1(X3,X2)) | ~v1_relat_1(X3)) )),
% 1.31/0.52    inference(subsumption_resolution,[],[f83,f38])).
% 1.31/0.52  fof(f83,plain,(
% 1.31/0.52    ( ! [X2,X3] : (v1_relat_1(k7_relat_1(X3,X2)) | ~v1_relat_1(X3) | ~v1_relat_1(k6_relat_1(X2))) )),
% 1.31/0.52    inference(duplicate_literal_removal,[],[f81])).
% 1.31/0.52  fof(f81,plain,(
% 1.31/0.52    ( ! [X2,X3] : (v1_relat_1(k7_relat_1(X3,X2)) | ~v1_relat_1(X3) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(X3)) )),
% 1.31/0.52    inference(superposition,[],[f53,f48])).
% 1.31/0.52  fof(f53,plain,(
% 1.31/0.52    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f34])).
% 1.31/0.52  fof(f34,plain,(
% 1.31/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.31/0.52    inference(flattening,[],[f33])).
% 1.31/0.52  fof(f33,plain,(
% 1.31/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.31/0.52    inference(ennf_transformation,[],[f10])).
% 1.31/0.52  fof(f10,axiom,(
% 1.31/0.52    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.31/0.53  fof(f621,plain,(
% 1.31/0.53    ( ! [X14,X13] : (k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14) | ~v1_relat_1(k8_relat_1(X13,k6_relat_1(X14)))) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f594,f38])).
% 1.31/0.53  fof(f594,plain,(
% 1.31/0.53    ( ! [X14,X13] : (k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))) | ~v1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14) | ~v1_relat_1(k8_relat_1(X13,k6_relat_1(X14)))) )),
% 1.31/0.53    inference(superposition,[],[f185,f42])).
% 1.31/0.53  fof(f42,plain,(
% 1.31/0.53    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f25])).
% 1.31/0.53  fof(f25,plain,(
% 1.31/0.53    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f16])).
% 1.31/0.53  % (12904)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.31/0.53  fof(f16,axiom,(
% 1.31/0.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 1.31/0.53  fof(f185,plain,(
% 1.31/0.53    ( ! [X4,X2,X3] : (k5_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k8_relat_1(X4,X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X3)) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f182,f38])).
% 1.31/0.53  fof(f182,plain,(
% 1.31/0.53    ( ! [X4,X2,X3] : (k5_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k8_relat_1(X4,X2) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X3)) )),
% 1.31/0.53    inference(duplicate_literal_removal,[],[f172])).
% 1.31/0.53  fof(f172,plain,(
% 1.31/0.53    ( ! [X4,X2,X3] : (k5_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k8_relat_1(X4,X2) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X3) | ~v1_relat_1(X2)) )),
% 1.31/0.53    inference(superposition,[],[f52,f51])).
% 1.31/0.53  fof(f52,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f32])).
% 1.31/0.53  fof(f32,plain,(
% 1.31/0.53    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f13])).
% 1.31/0.53  fof(f13,axiom,(
% 1.31/0.53    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 1.31/0.53  fof(f113,plain,(
% 1.31/0.53    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X6),X5) = k8_relat_1(X6,k6_relat_1(X5))) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f112,f38])).
% 1.31/0.53  fof(f112,plain,(
% 1.31/0.53    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X6),X5) = k8_relat_1(X6,k6_relat_1(X5)) | ~v1_relat_1(k6_relat_1(X6))) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f98,f38])).
% 1.31/0.53  fof(f98,plain,(
% 1.31/0.53    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X6),X5) = k8_relat_1(X6,k6_relat_1(X5)) | ~v1_relat_1(k6_relat_1(X5)) | ~v1_relat_1(k6_relat_1(X6))) )),
% 1.31/0.53    inference(superposition,[],[f49,f48])).
% 1.31/0.53  fof(f49,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f28])).
% 1.31/0.53  fof(f28,plain,(
% 1.31/0.53    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f12])).
% 1.31/0.53  fof(f12,axiom,(
% 1.31/0.53    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 1.31/0.53  fof(f90,plain,(
% 1.31/0.53    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.31/0.53    inference(subsumption_resolution,[],[f78,f38])).
% 1.31/0.53  fof(f78,plain,(
% 1.31/0.53    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK0))),
% 1.31/0.53    inference(superposition,[],[f37,f48])).
% 1.31/0.53  fof(f37,plain,(
% 1.31/0.53    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.31/0.53    inference(cnf_transformation,[],[f36])).
% 1.31/0.53  fof(f36,plain,(
% 1.31/0.53    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.31/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f35])).
% 1.31/0.53  fof(f35,plain,(
% 1.31/0.53    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f23,plain,(
% 1.31/0.53    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f22])).
% 1.31/0.53  fof(f22,negated_conjecture,(
% 1.31/0.53    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.31/0.53    inference(negated_conjecture,[],[f21])).
% 1.31/0.53  fof(f21,conjecture,(
% 1.31/0.53    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.31/0.53  % SZS output end Proof for theBenchmark
% 1.31/0.53  % (12900)------------------------------
% 1.31/0.53  % (12900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (12900)Termination reason: Refutation
% 1.31/0.53  
% 1.31/0.53  % (12900)Memory used [KB]: 2174
% 1.31/0.53  % (12900)Time elapsed: 0.102 s
% 1.31/0.53  % (12900)------------------------------
% 1.31/0.53  % (12900)------------------------------
% 1.31/0.53  % (12914)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.31/0.53  % (12910)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.31/0.53  % (12906)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.31/0.53  % (12894)Success in time 0.163 s
%------------------------------------------------------------------------------
