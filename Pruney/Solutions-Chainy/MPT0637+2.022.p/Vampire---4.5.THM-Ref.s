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
% DateTime   : Thu Dec  3 12:52:25 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 909 expanded)
%              Number of leaves         :   19 ( 273 expanded)
%              Depth                    :   21
%              Number of atoms          :  186 (1344 expanded)
%              Number of equality atoms :   89 ( 686 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1400,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1399])).

fof(f1399,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f1016,f1282])).

fof(f1282,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(superposition,[],[f1018,f215])).

fof(f215,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f214,f88])).

fof(f88,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f59,f45])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f214,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f213,f88])).

fof(f213,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f210,f46])).

fof(f46,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f210,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f209,f45])).

fof(f209,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f206,f46])).

fof(f206,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f51,f45])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f1018,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(superposition,[],[f46,f951])).

fof(f951,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X4),X3) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) ),
    inference(backward_demodulation,[],[f879,f950])).

fof(f950,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f946,f923])).

fof(f923,plain,(
    ! [X6,X5] : v1_relat_1(k7_relat_1(k6_relat_1(X5),X6)) ),
    inference(forward_demodulation,[],[f922,f47])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f922,plain,(
    ! [X6,X5] : v1_relat_1(k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X5),X6)))) ),
    inference(subsumption_resolution,[],[f915,f45])).

fof(f915,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X5),X6))))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(superposition,[],[f833,f255])).

fof(f255,plain,(
    ! [X17,X18] : k6_relat_1(k7_relat_1(k6_relat_1(X17),X18)) = k7_relat_1(k6_relat_1(k6_relat_1(X17)),k7_relat_1(k6_relat_1(X17),X18)) ),
    inference(forward_demodulation,[],[f245,f46])).

fof(f245,plain,(
    ! [X17,X18] : k7_relat_1(k6_relat_1(k6_relat_1(X17)),k7_relat_1(k6_relat_1(X17),X18)) = k4_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X17),X18))) ),
    inference(superposition,[],[f215,f156])).

fof(f156,plain,(
    ! [X2,X1] : k6_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X2)),k6_relat_1(X1)) ),
    inference(resolution,[],[f151,f99])).

fof(f99,plain,(
    ! [X2,X1] : r1_tarski(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X2)) ),
    inference(subsumption_resolution,[],[f97,f45])).

fof(f97,plain,(
    ! [X2,X1] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f63,f88])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f150,f88])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f148,f45])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f64,f47])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f833,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f75,f832])).

fof(f832,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f829,f47])).

fof(f829,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k3_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(resolution,[],[f76,f45])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k3_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f60,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f72])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f946,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(backward_demodulation,[],[f167,f930])).

fof(f930,plain,(
    ! [X12,X10,X11] : k7_relat_1(k7_relat_1(k6_relat_1(X10),X11),X12) = k5_relat_1(k6_relat_1(X12),k7_relat_1(k6_relat_1(X10),X11)) ),
    inference(resolution,[],[f923,f59])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))
      | k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))
      | k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f114,f64])).

fof(f114,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ) ),
    inference(resolution,[],[f106,f99])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k6_relat_1(X0))
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ r1_tarski(X1,k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f52,f47])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f879,plain,(
    ! [X4,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X4) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) ),
    inference(backward_demodulation,[],[f620,f832])).

fof(f620,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X4) ),
    inference(forward_demodulation,[],[f619,f215])).

fof(f619,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X3),X4)),X4) ),
    inference(forward_demodulation,[],[f618,f95])).

fof(f95,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(superposition,[],[f88,f82])).

fof(f82,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f81,f48])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f50,f45])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f618,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4)),X4) ),
    inference(backward_demodulation,[],[f590,f602])).

fof(f602,plain,(
    ! [X35,X33,X34] : k7_relat_1(k6_relat_1(k1_setfam_1(k3_enumset1(X34,X34,X34,X34,X35))),X33) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X33),X34),X35)) ),
    inference(superposition,[],[f215,f581])).

fof(f581,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(resolution,[],[f78,f45])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f68,f72])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f590,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))),X3),X4) ),
    inference(superposition,[],[f581,f95])).

fof(f1016,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(superposition,[],[f884,f951])).

fof(f884,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(backward_demodulation,[],[f90,f832])).

fof(f90,plain,(
    k6_relat_1(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f87,f89])).

fof(f89,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f86,f88])).

fof(f86,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f58,f45])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f87,plain,(
    k6_relat_1(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f73,f86])).

fof(f73,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f44,f72])).

fof(f44,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f42])).

fof(f42,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
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
% 0.13/0.35  % DateTime   : Tue Dec  1 13:18:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (24123)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (24121)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (24122)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (24128)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (24132)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (24131)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (24124)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (24133)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (24119)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (24127)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (24129)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (24120)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (24135)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (24125)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.51  % (24130)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.51  % (24126)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.51  % (24129)Refutation not found, incomplete strategy% (24129)------------------------------
% 0.20/0.51  % (24129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24129)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24129)Memory used [KB]: 10618
% 0.20/0.51  % (24129)Time elapsed: 0.080 s
% 0.20/0.51  % (24129)------------------------------
% 0.20/0.51  % (24129)------------------------------
% 0.20/0.51  % (24118)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.51  % (24134)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.36/0.54  % (24127)Refutation found. Thanks to Tanya!
% 1.36/0.54  % SZS status Theorem for theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f1400,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(trivial_inequality_removal,[],[f1399])).
% 1.36/0.54  fof(f1399,plain,(
% 1.36/0.54    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.36/0.54    inference(superposition,[],[f1016,f1282])).
% 1.36/0.54  fof(f1282,plain,(
% 1.36/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 1.36/0.54    inference(superposition,[],[f1018,f215])).
% 1.36/0.54  fof(f215,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f214,f88])).
% 1.36/0.54  fof(f88,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.36/0.54    inference(resolution,[],[f59,f45])).
% 1.36/0.54  fof(f45,plain,(
% 1.36/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f6])).
% 1.36/0.54  fof(f6,axiom,(
% 1.36/0.54    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.36/0.54  fof(f59,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f33])).
% 1.36/0.54  fof(f33,plain,(
% 1.36/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f22])).
% 1.36/0.54  fof(f22,axiom,(
% 1.36/0.54    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.36/0.54  fof(f214,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f213,f88])).
% 1.36/0.54  fof(f213,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f210,f46])).
% 1.36/0.54  fof(f46,plain,(
% 1.36/0.54    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f17])).
% 1.36/0.54  fof(f17,axiom,(
% 1.36/0.54    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 1.36/0.54  fof(f210,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0)))) )),
% 1.36/0.54    inference(resolution,[],[f209,f45])).
% 1.36/0.54  fof(f209,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f206,f46])).
% 1.36/0.54  fof(f206,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(resolution,[],[f51,f45])).
% 1.36/0.54  fof(f51,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f28])).
% 1.36/0.54  fof(f28,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f15])).
% 1.36/0.54  fof(f15,axiom,(
% 1.36/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.36/0.54  fof(f1018,plain,(
% 1.36/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2))) )),
% 1.36/0.54    inference(superposition,[],[f46,f951])).
% 1.36/0.54  fof(f951,plain,(
% 1.36/0.54    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X4),X3) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)))) )),
% 1.36/0.54    inference(backward_demodulation,[],[f879,f950])).
% 1.36/0.54  fof(f950,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f946,f923])).
% 1.36/0.54  fof(f923,plain,(
% 1.36/0.54    ( ! [X6,X5] : (v1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f922,f47])).
% 1.36/0.54  fof(f47,plain,(
% 1.36/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f16])).
% 1.36/0.54  fof(f16,axiom,(
% 1.36/0.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.36/0.54  fof(f922,plain,(
% 1.36/0.54    ( ! [X6,X5] : (v1_relat_1(k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X5),X6))))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f915,f45])).
% 1.36/0.54  fof(f915,plain,(
% 1.36/0.54    ( ! [X6,X5] : (v1_relat_1(k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X5),X6)))) | ~v1_relat_1(k6_relat_1(X5))) )),
% 1.36/0.54    inference(superposition,[],[f833,f255])).
% 1.36/0.54  fof(f255,plain,(
% 1.36/0.54    ( ! [X17,X18] : (k6_relat_1(k7_relat_1(k6_relat_1(X17),X18)) = k7_relat_1(k6_relat_1(k6_relat_1(X17)),k7_relat_1(k6_relat_1(X17),X18))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f245,f46])).
% 1.36/0.54  fof(f245,plain,(
% 1.36/0.54    ( ! [X17,X18] : (k7_relat_1(k6_relat_1(k6_relat_1(X17)),k7_relat_1(k6_relat_1(X17),X18)) = k4_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X17),X18)))) )),
% 1.36/0.54    inference(superposition,[],[f215,f156])).
% 1.36/0.54  fof(f156,plain,(
% 1.36/0.54    ( ! [X2,X1] : (k6_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X2)),k6_relat_1(X1))) )),
% 1.36/0.54    inference(resolution,[],[f151,f99])).
% 1.36/0.54  fof(f99,plain,(
% 1.36/0.54    ( ! [X2,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X2))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f97,f45])).
% 1.36/0.54  fof(f97,plain,(
% 1.36/0.54    ( ! [X2,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 1.36/0.54    inference(superposition,[],[f63,f88])).
% 1.36/0.54  fof(f63,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f36])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f18])).
% 1.36/0.54  fof(f18,axiom,(
% 1.36/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 1.36/0.54  fof(f151,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.36/0.54    inference(forward_demodulation,[],[f150,f88])).
% 1.36/0.54  fof(f150,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f148,f45])).
% 1.36/0.54  fof(f148,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.36/0.54    inference(superposition,[],[f64,f47])).
% 1.36/0.54  fof(f64,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f38])).
% 1.36/0.54  fof(f38,plain,(
% 1.36/0.54    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.36/0.54    inference(flattening,[],[f37])).
% 1.36/0.54  fof(f37,plain,(
% 1.36/0.54    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f19])).
% 1.36/0.54  fof(f19,axiom,(
% 1.36/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 1.36/0.54  fof(f833,plain,(
% 1.36/0.54    ( ! [X0,X1] : (v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(backward_demodulation,[],[f75,f832])).
% 1.36/0.54  fof(f832,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f829,f47])).
% 1.36/0.54  fof(f829,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k3_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))) )),
% 1.36/0.54    inference(resolution,[],[f76,f45])).
% 1.36/0.54  fof(f76,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k3_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 1.36/0.54    inference(definition_unfolding,[],[f60,f72])).
% 1.36/0.54  fof(f72,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.36/0.54    inference(definition_unfolding,[],[f56,f71])).
% 1.36/0.54  fof(f71,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f55,f70])).
% 1.36/0.54  fof(f70,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f66,f69])).
% 1.36/0.54  fof(f69,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.36/0.54  fof(f66,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.54  fof(f55,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f2])).
% 1.36/0.54  fof(f2,axiom,(
% 1.36/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.54  fof(f56,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.36/0.54  fof(f60,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f34,plain,(
% 1.36/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f21])).
% 1.36/0.54  fof(f21,axiom,(
% 1.36/0.54    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.36/0.54  fof(f75,plain,(
% 1.36/0.54    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f57,f72])).
% 1.36/0.54  fof(f57,plain,(
% 1.36/0.54    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f31,plain,(
% 1.36/0.54    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f7])).
% 1.36/0.54  fof(f7,axiom,(
% 1.36/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.36/0.54  fof(f946,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.36/0.54    inference(backward_demodulation,[],[f167,f930])).
% 1.36/0.54  fof(f930,plain,(
% 1.36/0.54    ( ! [X12,X10,X11] : (k7_relat_1(k7_relat_1(k6_relat_1(X10),X11),X12) = k5_relat_1(k6_relat_1(X12),k7_relat_1(k6_relat_1(X10),X11))) )),
% 1.36/0.54    inference(resolution,[],[f923,f59])).
% 1.36/0.54  fof(f167,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) | k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.36/0.54    inference(duplicate_literal_removal,[],[f162])).
% 1.36/0.54  fof(f162,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) | k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.36/0.54    inference(resolution,[],[f114,f64])).
% 1.36/0.54  fof(f114,plain,(
% 1.36/0.54    ( ! [X2,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) | ~v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) )),
% 1.36/0.54    inference(resolution,[],[f106,f99])).
% 1.36/0.54  fof(f106,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(X1,k6_relat_1(X0)) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f104,f45])).
% 1.36/0.54  fof(f104,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~r1_tarski(X1,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.36/0.54    inference(superposition,[],[f52,f47])).
% 1.36/0.54  fof(f52,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f30])).
% 1.36/0.54  fof(f30,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(flattening,[],[f29])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,axiom,(
% 1.36/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.36/0.54  fof(f879,plain,(
% 1.36/0.54    ( ! [X4,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X4) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)))) )),
% 1.36/0.54    inference(backward_demodulation,[],[f620,f832])).
% 1.36/0.54  fof(f620,plain,(
% 1.36/0.54    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X4)) )),
% 1.36/0.54    inference(forward_demodulation,[],[f619,f215])).
% 1.36/0.55  fof(f619,plain,(
% 1.36/0.55    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X3),X4)),X4)) )),
% 1.36/0.55    inference(forward_demodulation,[],[f618,f95])).
% 1.36/0.55  fof(f95,plain,(
% 1.36/0.55    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.36/0.55    inference(superposition,[],[f88,f82])).
% 1.36/0.55  fof(f82,plain,(
% 1.36/0.55    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.36/0.55    inference(forward_demodulation,[],[f81,f48])).
% 1.36/0.55  fof(f48,plain,(
% 1.36/0.55    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f81,plain,(
% 1.36/0.55    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 1.36/0.55    inference(resolution,[],[f50,f45])).
% 1.36/0.55  fof(f50,plain,(
% 1.36/0.55    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f27])).
% 1.36/0.55  fof(f27,plain,(
% 1.36/0.55    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f20])).
% 1.36/0.55  fof(f20,axiom,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.36/0.55  fof(f618,plain,(
% 1.36/0.55    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4)),X4)) )),
% 1.36/0.55    inference(backward_demodulation,[],[f590,f602])).
% 1.36/0.55  fof(f602,plain,(
% 1.36/0.55    ( ! [X35,X33,X34] : (k7_relat_1(k6_relat_1(k1_setfam_1(k3_enumset1(X34,X34,X34,X34,X35))),X33) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X33),X34),X35))) )),
% 1.36/0.55    inference(superposition,[],[f215,f581])).
% 1.36/0.55  fof(f581,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 1.36/0.55    inference(resolution,[],[f78,f45])).
% 1.36/0.55  fof(f78,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f68,f72])).
% 1.36/0.55  fof(f68,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f41])).
% 1.36/0.55  fof(f41,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.36/0.55    inference(ennf_transformation,[],[f9])).
% 1.36/0.55  fof(f9,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 1.36/0.55  fof(f590,plain,(
% 1.36/0.55    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))),X3),X4)) )),
% 1.36/0.55    inference(superposition,[],[f581,f95])).
% 1.36/0.55  fof(f1016,plain,(
% 1.36/0.55    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0)),
% 1.36/0.55    inference(superposition,[],[f884,f951])).
% 1.36/0.55  fof(f884,plain,(
% 1.36/0.55    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 1.36/0.55    inference(backward_demodulation,[],[f90,f832])).
% 1.36/0.55  fof(f90,plain,(
% 1.36/0.55    k6_relat_1(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.36/0.55    inference(backward_demodulation,[],[f87,f89])).
% 1.36/0.55  fof(f89,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.36/0.55    inference(backward_demodulation,[],[f86,f88])).
% 1.36/0.55  fof(f86,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 1.36/0.55    inference(resolution,[],[f58,f45])).
% 1.36/0.55  fof(f58,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f32])).
% 1.36/0.55  fof(f32,plain,(
% 1.36/0.55    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.36/0.55    inference(ennf_transformation,[],[f11])).
% 1.36/0.55  fof(f11,axiom,(
% 1.36/0.55    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 1.36/0.55  fof(f87,plain,(
% 1.36/0.55    k6_relat_1(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 1.36/0.55    inference(backward_demodulation,[],[f73,f86])).
% 1.36/0.55  fof(f73,plain,(
% 1.36/0.55    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 1.36/0.55    inference(definition_unfolding,[],[f44,f72])).
% 1.36/0.55  fof(f44,plain,(
% 1.36/0.55    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(cnf_transformation,[],[f43])).
% 1.36/0.55  fof(f43,plain,(
% 1.36/0.55    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f42])).
% 1.36/0.55  fof(f42,plain,(
% 1.36/0.55    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.52/0.56  fof(f25,plain,(
% 1.52/0.56    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.52/0.56    inference(ennf_transformation,[],[f24])).
% 1.52/0.56  fof(f24,negated_conjecture,(
% 1.52/0.56    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.52/0.56    inference(negated_conjecture,[],[f23])).
% 1.52/0.56  fof(f23,conjecture,(
% 1.52/0.56    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.52/0.56  % SZS output end Proof for theBenchmark
% 1.52/0.56  % (24127)------------------------------
% 1.52/0.56  % (24127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (24127)Termination reason: Refutation
% 1.52/0.56  
% 1.52/0.56  % (24127)Memory used [KB]: 12025
% 1.52/0.56  % (24127)Time elapsed: 0.130 s
% 1.52/0.56  % (24127)------------------------------
% 1.52/0.56  % (24127)------------------------------
% 1.52/0.56  % (24117)Success in time 0.196 s
%------------------------------------------------------------------------------
