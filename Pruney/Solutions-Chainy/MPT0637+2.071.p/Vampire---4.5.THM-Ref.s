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
% DateTime   : Thu Dec  3 12:52:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 844 expanded)
%              Number of leaves         :   20 ( 216 expanded)
%              Depth                    :   18
%              Number of atoms          :  199 (1614 expanded)
%              Number of equality atoms :   91 ( 439 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1365,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1256,f520])).

fof(f520,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3) ),
    inference(superposition,[],[f512,f232])).

fof(f232,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f231,f85])).

fof(f85,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f58,f47])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f231,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f230,f85])).

fof(f230,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f227,f46])).

fof(f46,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f227,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f226,f47])).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f223,f46])).

fof(f223,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f52,f47])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f512,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(superposition,[],[f237,f467])).

fof(f467,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X1) ),
    inference(superposition,[],[f210,f175])).

fof(f175,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(X3)) ),
    inference(subsumption_resolution,[],[f170,f97])).

fof(f97,plain,(
    ! [X4,X5] : v1_relat_1(k7_relat_1(k6_relat_1(X5),X4)) ),
    inference(subsumption_resolution,[],[f96,f47])).

fof(f96,plain,(
    ! [X4,X5] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X5),X4))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(subsumption_resolution,[],[f93,f47])).

fof(f93,plain,(
    ! [X4,X5] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X5),X4))
      | ~ v1_relat_1(k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(superposition,[],[f64,f85])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f170,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(X3))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(resolution,[],[f63,f156])).

fof(f156,plain,(
    ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X1) ),
    inference(subsumption_resolution,[],[f155,f97])).

fof(f155,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
      | r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X1) ) ),
    inference(forward_demodulation,[],[f154,f85])).

fof(f154,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X1)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ) ),
    inference(forward_demodulation,[],[f153,f85])).

fof(f153,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ) ),
    inference(subsumption_resolution,[],[f145,f47])).

fof(f145,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f140,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k6_relat_1(X0))
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f138,f47])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ r1_tarski(X1,k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f54,f50])).

fof(f50,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f210,plain,(
    ! [X4,X5,X3] : k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) ),
    inference(backward_demodulation,[],[f99,f209])).

fof(f209,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(forward_demodulation,[],[f206,f87])).

fof(f87,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f82,f85])).

fof(f82,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f57,f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f206,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) ),
    inference(resolution,[],[f67,f47])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f99,plain,(
    ! [X4,X5,X3] : k8_relat_1(X3,k7_relat_1(k6_relat_1(X4),X5)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3)) ),
    inference(resolution,[],[f97,f57])).

fof(f237,plain,(
    ! [X6,X7,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6)) ),
    inference(forward_demodulation,[],[f236,f210])).

fof(f236,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) ),
    inference(forward_demodulation,[],[f235,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f97,f58])).

fof(f235,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k5_relat_1(k6_relat_1(X7),k7_relat_1(k6_relat_1(X6),X5)) ),
    inference(forward_demodulation,[],[f229,f232])).

fof(f229,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k5_relat_1(k6_relat_1(X7),k4_relat_1(k7_relat_1(k6_relat_1(X5),X6))) ),
    inference(resolution,[],[f226,f97])).

fof(f1256,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(superposition,[],[f802,f1228])).

fof(f1228,plain,(
    ! [X12,X11] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X11),X12))) = k7_relat_1(k6_relat_1(X12),X11) ),
    inference(backward_demodulation,[],[f195,f1227])).

fof(f1227,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(forward_demodulation,[],[f1223,f49])).

fof(f49,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f1223,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X0))))) ),
    inference(resolution,[],[f800,f47])).

fof(f800,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k2_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(X1)))) ) ),
    inference(backward_demodulation,[],[f77,f793])).

fof(f793,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) ),
    inference(forward_demodulation,[],[f792,f87])).

fof(f792,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) ),
    inference(forward_demodulation,[],[f788,f50])).

fof(f788,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),X0)) ),
    inference(resolution,[],[f76,f47])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k4_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f60,f74])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f195,plain,(
    ! [X12,X11] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X11),X12))) = k7_relat_1(k6_relat_1(X12),k2_relat_1(k7_relat_1(k6_relat_1(X11),X12))) ),
    inference(resolution,[],[f178,f156])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f177,f85])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f173,f47])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f63,f50])).

fof(f802,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(forward_demodulation,[],[f801,f520])).

fof(f801,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) ),
    inference(backward_demodulation,[],[f88,f793])).

fof(f88,plain,(
    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f84,f87])).

fof(f84,plain,(
    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f75,f82])).

fof(f75,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f45,f74])).

fof(f45,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f43])).

fof(f43,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (5740)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.44  % (5756)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (5744)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (5753)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (5757)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (5742)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (5745)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (5748)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (5747)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (5755)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (5743)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (5752)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (5754)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (5746)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (5751)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (5751)Refutation not found, incomplete strategy% (5751)------------------------------
% 0.20/0.50  % (5751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (5751)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (5751)Memory used [KB]: 10618
% 0.20/0.50  % (5751)Time elapsed: 0.061 s
% 0.20/0.50  % (5751)------------------------------
% 0.20/0.50  % (5751)------------------------------
% 0.20/0.50  % (5749)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (5741)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.52  % (5750)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.56  % (5749)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 1.62/0.57  % SZS output start Proof for theBenchmark
% 1.62/0.57  fof(f1365,plain,(
% 1.62/0.57    $false),
% 1.62/0.57    inference(subsumption_resolution,[],[f1256,f520])).
% 1.62/0.57  fof(f520,plain,(
% 1.62/0.57    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3)) )),
% 1.62/0.57    inference(superposition,[],[f512,f232])).
% 1.62/0.57  fof(f232,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.62/0.57    inference(forward_demodulation,[],[f231,f85])).
% 1.62/0.57  fof(f85,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.62/0.57    inference(resolution,[],[f58,f47])).
% 1.62/0.57  fof(f47,plain,(
% 1.62/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f24])).
% 1.62/0.57  fof(f24,plain,(
% 1.62/0.57    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.62/0.57    inference(pure_predicate_removal,[],[f21])).
% 1.62/0.57  fof(f21,axiom,(
% 1.62/0.57    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 1.62/0.57  fof(f58,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f31])).
% 1.62/0.57  fof(f31,plain,(
% 1.62/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.62/0.57    inference(ennf_transformation,[],[f20])).
% 1.62/0.57  fof(f20,axiom,(
% 1.62/0.57    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.62/0.57  fof(f231,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.62/0.57    inference(forward_demodulation,[],[f230,f85])).
% 1.62/0.57  fof(f230,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.62/0.57    inference(forward_demodulation,[],[f227,f46])).
% 1.62/0.57  fof(f46,plain,(
% 1.62/0.57    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f17])).
% 1.62/0.57  fof(f17,axiom,(
% 1.62/0.57    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 1.62/0.57  fof(f227,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0)))) )),
% 1.62/0.57    inference(resolution,[],[f226,f47])).
% 1.62/0.57  fof(f226,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))) )),
% 1.62/0.57    inference(forward_demodulation,[],[f223,f46])).
% 1.62/0.57  fof(f223,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.62/0.57    inference(resolution,[],[f52,f47])).
% 1.62/0.57  fof(f52,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f27])).
% 1.62/0.57  fof(f27,plain,(
% 1.62/0.57    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.57    inference(ennf_transformation,[],[f15])).
% 1.62/0.57  fof(f15,axiom,(
% 1.62/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.62/0.57  fof(f512,plain,(
% 1.62/0.57    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2))) )),
% 1.62/0.57    inference(superposition,[],[f237,f467])).
% 1.62/0.57  fof(f467,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X1)) )),
% 1.62/0.57    inference(superposition,[],[f210,f175])).
% 1.62/0.57  fof(f175,plain,(
% 1.62/0.57    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(X3))) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f170,f97])).
% 1.62/0.57  fof(f97,plain,(
% 1.62/0.57    ( ! [X4,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f96,f47])).
% 1.62/0.57  fof(f96,plain,(
% 1.62/0.57    ( ! [X4,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X5),X4)) | ~v1_relat_1(k6_relat_1(X4))) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f93,f47])).
% 1.62/0.57  fof(f93,plain,(
% 1.62/0.57    ( ! [X4,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X5),X4)) | ~v1_relat_1(k6_relat_1(X5)) | ~v1_relat_1(k6_relat_1(X4))) )),
% 1.62/0.57    inference(superposition,[],[f64,f85])).
% 1.62/0.57  fof(f64,plain,(
% 1.62/0.57    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f38])).
% 1.62/0.57  fof(f38,plain,(
% 1.62/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.62/0.57    inference(flattening,[],[f37])).
% 1.62/0.57  fof(f37,plain,(
% 1.62/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.62/0.57    inference(ennf_transformation,[],[f6])).
% 1.62/0.57  fof(f6,axiom,(
% 1.62/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.62/0.57  fof(f170,plain,(
% 1.62/0.57    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(X3)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) )),
% 1.62/0.57    inference(resolution,[],[f63,f156])).
% 1.62/0.57  fof(f156,plain,(
% 1.62/0.57    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X1)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f155,f97])).
% 1.62/0.57  fof(f155,plain,(
% 1.62/0.57    ( ! [X2,X1] : (~v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X1)) )),
% 1.62/0.57    inference(forward_demodulation,[],[f154,f85])).
% 1.62/0.57  fof(f154,plain,(
% 1.62/0.57    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X1) | ~v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) )),
% 1.62/0.57    inference(forward_demodulation,[],[f153,f85])).
% 1.62/0.57  fof(f153,plain,(
% 1.62/0.57    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1) | ~v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f145,f47])).
% 1.62/0.57  fof(f145,plain,(
% 1.62/0.57    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1) | ~v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.62/0.57    inference(resolution,[],[f140,f61])).
% 1.62/0.57  fof(f61,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f34])).
% 1.62/0.57  fof(f34,plain,(
% 1.62/0.57    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.62/0.57    inference(ennf_transformation,[],[f18])).
% 1.62/0.57  fof(f18,axiom,(
% 1.62/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 1.62/0.57  fof(f140,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k6_relat_1(X0)) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f138,f47])).
% 1.62/0.57  fof(f138,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~r1_tarski(X1,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.62/0.57    inference(superposition,[],[f54,f50])).
% 1.62/0.57  fof(f50,plain,(
% 1.62/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.62/0.57    inference(cnf_transformation,[],[f16])).
% 1.62/0.57  fof(f16,axiom,(
% 1.62/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.62/0.57  fof(f54,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f29])).
% 1.62/0.57  fof(f29,plain,(
% 1.62/0.57    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.57    inference(flattening,[],[f28])).
% 1.62/0.57  fof(f28,plain,(
% 1.62/0.57    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.57    inference(ennf_transformation,[],[f14])).
% 1.62/0.57  fof(f14,axiom,(
% 1.62/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.62/0.57  fof(f63,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f36])).
% 1.62/0.57  fof(f36,plain,(
% 1.62/0.57    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.62/0.57    inference(flattening,[],[f35])).
% 1.62/0.57  fof(f35,plain,(
% 1.62/0.57    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.62/0.57    inference(ennf_transformation,[],[f19])).
% 1.62/0.57  fof(f19,axiom,(
% 1.62/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 1.62/0.57  fof(f210,plain,(
% 1.62/0.57    ( ! [X4,X5,X3] : (k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5)) )),
% 1.62/0.57    inference(backward_demodulation,[],[f99,f209])).
% 1.62/0.57  fof(f209,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2))) )),
% 1.62/0.57    inference(forward_demodulation,[],[f206,f87])).
% 1.62/0.57  fof(f87,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.62/0.57    inference(backward_demodulation,[],[f82,f85])).
% 1.62/0.57  fof(f82,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 1.62/0.57    inference(resolution,[],[f57,f47])).
% 1.62/0.57  fof(f57,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f30])).
% 1.62/0.57  fof(f30,plain,(
% 1.62/0.57    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.62/0.57    inference(ennf_transformation,[],[f10])).
% 1.62/0.57  fof(f10,axiom,(
% 1.62/0.57    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 1.62/0.57  fof(f206,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2)) )),
% 1.62/0.57    inference(resolution,[],[f67,f47])).
% 1.62/0.57  fof(f67,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f41])).
% 1.62/0.57  fof(f41,plain,(
% 1.62/0.57    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.62/0.57    inference(ennf_transformation,[],[f11])).
% 1.62/0.57  fof(f11,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 1.62/0.57  fof(f99,plain,(
% 1.62/0.57    ( ! [X4,X5,X3] : (k8_relat_1(X3,k7_relat_1(k6_relat_1(X4),X5)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(X3))) )),
% 1.62/0.57    inference(resolution,[],[f97,f57])).
% 1.62/0.57  fof(f237,plain,(
% 1.62/0.57    ( ! [X6,X7,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6))) )),
% 1.62/0.57    inference(forward_demodulation,[],[f236,f210])).
% 1.62/0.57  fof(f236,plain,(
% 1.62/0.57    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7)) )),
% 1.62/0.57    inference(forward_demodulation,[],[f235,f98])).
% 1.62/0.57  fof(f98,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.62/0.57    inference(resolution,[],[f97,f58])).
% 1.62/0.57  fof(f235,plain,(
% 1.62/0.57    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k5_relat_1(k6_relat_1(X7),k7_relat_1(k6_relat_1(X6),X5))) )),
% 1.62/0.57    inference(forward_demodulation,[],[f229,f232])).
% 1.62/0.57  fof(f229,plain,(
% 1.62/0.57    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k5_relat_1(k6_relat_1(X7),k4_relat_1(k7_relat_1(k6_relat_1(X5),X6)))) )),
% 1.62/0.57    inference(resolution,[],[f226,f97])).
% 1.62/0.57  fof(f1256,plain,(
% 1.62/0.57    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0)),
% 1.62/0.57    inference(superposition,[],[f802,f1228])).
% 1.62/0.57  fof(f1228,plain,(
% 1.62/0.57    ( ! [X12,X11] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X11),X12))) = k7_relat_1(k6_relat_1(X12),X11)) )),
% 1.62/0.57    inference(backward_demodulation,[],[f195,f1227])).
% 1.62/0.57  fof(f1227,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) )),
% 1.62/0.57    inference(forward_demodulation,[],[f1223,f49])).
% 1.62/0.57  fof(f49,plain,(
% 1.62/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.62/0.57    inference(cnf_transformation,[],[f16])).
% 1.62/0.57  fof(f1223,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X0)))))) )),
% 1.62/0.57    inference(resolution,[],[f800,f47])).
% 1.62/0.57  fof(f800,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k2_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))))) )),
% 1.62/0.57    inference(backward_demodulation,[],[f77,f793])).
% 1.62/0.57  fof(f793,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))) )),
% 1.62/0.57    inference(forward_demodulation,[],[f792,f87])).
% 1.62/0.57  fof(f792,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))) )),
% 1.62/0.57    inference(forward_demodulation,[],[f788,f50])).
% 1.62/0.57  fof(f788,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),X0))) )),
% 1.62/0.57    inference(resolution,[],[f76,f47])).
% 1.62/0.57  fof(f76,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) )),
% 1.62/0.57    inference(definition_unfolding,[],[f59,f74])).
% 1.62/0.57  fof(f74,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.62/0.57    inference(definition_unfolding,[],[f55,f73])).
% 1.62/0.57  fof(f73,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.62/0.57    inference(definition_unfolding,[],[f56,f72])).
% 1.62/0.57  fof(f72,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.62/0.57    inference(definition_unfolding,[],[f66,f71])).
% 1.62/0.57  fof(f71,plain,(
% 1.62/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.62/0.57    inference(definition_unfolding,[],[f69,f70])).
% 1.62/0.57  fof(f70,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f4])).
% 1.62/0.57  fof(f4,axiom,(
% 1.62/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.62/0.57  fof(f69,plain,(
% 1.62/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f3])).
% 1.62/0.57  fof(f3,axiom,(
% 1.62/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.62/0.57  fof(f66,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f2])).
% 1.62/0.57  fof(f2,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.62/0.57  fof(f56,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f1])).
% 1.62/0.57  fof(f1,axiom,(
% 1.62/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.62/0.57  fof(f55,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f5])).
% 1.62/0.57  fof(f5,axiom,(
% 1.62/0.57    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.62/0.57  fof(f59,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f32])).
% 1.62/0.57  fof(f32,plain,(
% 1.62/0.57    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.62/0.57    inference(ennf_transformation,[],[f9])).
% 1.62/0.57  fof(f9,axiom,(
% 1.62/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 1.62/0.57  fof(f77,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k4_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.62/0.57    inference(definition_unfolding,[],[f60,f74])).
% 1.62/0.57  fof(f60,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f33])).
% 1.62/0.57  fof(f33,plain,(
% 1.62/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.62/0.57    inference(ennf_transformation,[],[f12])).
% 1.62/0.57  fof(f12,axiom,(
% 1.62/0.57    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 1.62/0.57  fof(f195,plain,(
% 1.62/0.57    ( ! [X12,X11] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X11),X12))) = k7_relat_1(k6_relat_1(X12),k2_relat_1(k7_relat_1(k6_relat_1(X11),X12)))) )),
% 1.62/0.57    inference(resolution,[],[f178,f156])).
% 1.62/0.57  fof(f178,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 1.62/0.57    inference(forward_demodulation,[],[f177,f85])).
% 1.62/0.57  fof(f177,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f173,f47])).
% 1.62/0.57  fof(f173,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.62/0.57    inference(superposition,[],[f63,f50])).
% 1.62/0.57  fof(f802,plain,(
% 1.62/0.57    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 1.62/0.57    inference(forward_demodulation,[],[f801,f520])).
% 1.62/0.57  fof(f801,plain,(
% 1.62/0.57    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0)))),
% 1.62/0.57    inference(backward_demodulation,[],[f88,f793])).
% 1.62/0.57  fof(f88,plain,(
% 1.62/0.57    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.62/0.57    inference(backward_demodulation,[],[f84,f87])).
% 1.62/0.57  fof(f84,plain,(
% 1.62/0.57    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 1.62/0.57    inference(backward_demodulation,[],[f75,f82])).
% 1.62/0.57  fof(f75,plain,(
% 1.62/0.57    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.62/0.57    inference(definition_unfolding,[],[f45,f74])).
% 1.62/0.57  fof(f45,plain,(
% 1.62/0.57    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.62/0.57    inference(cnf_transformation,[],[f44])).
% 1.62/0.57  fof(f44,plain,(
% 1.62/0.57    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.62/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f43])).
% 1.62/0.57  fof(f43,plain,(
% 1.62/0.57    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.62/0.57    introduced(choice_axiom,[])).
% 1.62/0.57  fof(f25,plain,(
% 1.62/0.57    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.62/0.57    inference(ennf_transformation,[],[f23])).
% 1.62/0.57  fof(f23,negated_conjecture,(
% 1.62/0.57    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.62/0.57    inference(negated_conjecture,[],[f22])).
% 1.62/0.57  fof(f22,conjecture,(
% 1.62/0.57    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.62/0.57  % SZS output end Proof for theBenchmark
% 1.62/0.57  % (5749)------------------------------
% 1.62/0.57  % (5749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.57  % (5749)Termination reason: Refutation
% 1.62/0.57  
% 1.62/0.57  % (5749)Memory used [KB]: 11769
% 1.62/0.57  % (5749)Time elapsed: 0.144 s
% 1.62/0.57  % (5749)------------------------------
% 1.62/0.57  % (5749)------------------------------
% 1.62/0.57  % (5739)Success in time 0.211 s
%------------------------------------------------------------------------------
