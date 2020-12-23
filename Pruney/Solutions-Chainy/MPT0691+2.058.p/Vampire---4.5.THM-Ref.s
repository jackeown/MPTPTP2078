%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:53 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 392 expanded)
%              Number of leaves         :   20 ( 112 expanded)
%              Depth                    :   18
%              Number of atoms          :  200 ( 800 expanded)
%              Number of equality atoms :   82 ( 247 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f749,plain,(
    $false ),
    inference(subsumption_resolution,[],[f747,f47])).

fof(f47,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f41])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f747,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f360,f743])).

fof(f743,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f737,f482])).

fof(f482,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f475,f421])).

fof(f421,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k1_relat_1(k7_relat_1(sK1,X8)))
      | k1_relat_1(k7_relat_1(sK1,X8)) = X8 ) ),
    inference(resolution,[],[f101,f45])).

fof(f45,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f101,plain,(
    ! [X6,X5] :
      ( ~ v1_relat_1(X6)
      | ~ r1_tarski(X5,k1_relat_1(k7_relat_1(X6,X5)))
      | k1_relat_1(k7_relat_1(X6,X5)) = X5 ) ),
    inference(resolution,[],[f67,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f475,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f470,f50])).

fof(f50,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f470,plain,(
    r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f234,f459])).

fof(f459,plain,(
    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(superposition,[],[f457,f83])).

fof(f83,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f80,f48])).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f80,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f52,f50])).

fof(f52,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f457,plain,(
    ! [X21] : k7_relat_1(k6_relat_1(X21),sK0) = k7_relat_1(k7_relat_1(k6_relat_1(X21),sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f139,f46])).

fof(f46,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f139,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k7_relat_1(k6_relat_1(X4),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X2),X3) ) ),
    inference(resolution,[],[f70,f48])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f234,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X1))) ),
    inference(subsumption_resolution,[],[f230,f48])).

fof(f230,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f62,f214])).

fof(f214,plain,(
    ! [X4] : k7_relat_1(k6_relat_1(X4),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X4),k1_relat_1(k7_relat_1(sK1,X4))) ),
    inference(forward_demodulation,[],[f211,f50])).

fof(f211,plain,(
    ! [X4] : k7_relat_1(k6_relat_1(X4),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X4),k1_relat_1(k7_relat_1(sK1,k1_relat_1(k6_relat_1(X4))))) ),
    inference(resolution,[],[f185,f48])).

fof(f185,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k7_relat_1(X8,k1_relat_1(sK1)) = k7_relat_1(X8,k1_relat_1(k7_relat_1(sK1,k1_relat_1(X8)))) ) ),
    inference(resolution,[],[f55,f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(f737,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f518,f697])).

fof(f697,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f574,f482])).

fof(f574,plain,(
    ! [X10] : k2_relat_1(k7_relat_1(sK1,X10)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X10))) ),
    inference(forward_demodulation,[],[f573,f560])).

fof(f560,plain,(
    ! [X9] : k1_relat_1(k7_relat_1(k6_relat_1(X9),k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X9)) ),
    inference(subsumption_resolution,[],[f555,f234])).

fof(f555,plain,(
    ! [X9] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X9),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X9)))
      | k1_relat_1(k7_relat_1(k6_relat_1(X9),k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X9)) ) ),
    inference(superposition,[],[f421,f466])).

fof(f466,plain,(
    ! [X8] : k7_relat_1(sK1,X8) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X8),k1_relat_1(sK1)))) ),
    inference(resolution,[],[f187,f45])).

fof(f187,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | k7_relat_1(X6,k1_relat_1(k7_relat_1(k6_relat_1(X7),k1_relat_1(X6)))) = k7_relat_1(X6,X7) ) ),
    inference(forward_demodulation,[],[f184,f50])).

fof(f184,plain,(
    ! [X6,X7] :
      ( k7_relat_1(X6,k1_relat_1(k6_relat_1(X7))) = k7_relat_1(X6,k1_relat_1(k7_relat_1(k6_relat_1(X7),k1_relat_1(X6))))
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f55,f48])).

fof(f573,plain,(
    ! [X10] : k9_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X10),k1_relat_1(sK1)))) = k2_relat_1(k7_relat_1(sK1,X10)) ),
    inference(subsumption_resolution,[],[f556,f45])).

fof(f556,plain,(
    ! [X10] :
      ( k9_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X10),k1_relat_1(sK1)))) = k2_relat_1(k7_relat_1(sK1,X10))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f63,f466])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f518,plain,(
    ! [X8] : k1_relat_1(k7_relat_1(sK1,X8)) = k10_relat_1(k7_relat_1(sK1,X8),k2_relat_1(k7_relat_1(sK1,X8))) ),
    inference(resolution,[],[f94,f45])).

fof(f94,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) = k1_relat_1(k7_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f53,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f360,plain,(
    ! [X2,X3] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X3),X2),k10_relat_1(sK1,X2)) ),
    inference(superposition,[],[f86,f353])).

fof(f353,plain,(
    ! [X12,X11] : k10_relat_1(k7_relat_1(sK1,X11),X12) = k10_relat_1(k6_relat_1(k10_relat_1(sK1,X12)),X11) ),
    inference(resolution,[],[f292,f45])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k10_relat_1(k6_relat_1(k10_relat_1(X2,X1)),X0) ) ),
    inference(backward_demodulation,[],[f153,f280])).

fof(f280,plain,(
    ! [X2,X3] : k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) = k10_relat_1(k6_relat_1(X2),X3) ),
    inference(forward_demodulation,[],[f279,f50])).

fof(f279,plain,(
    ! [X2,X3] : k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) = k10_relat_1(k6_relat_1(X2),k1_relat_1(k6_relat_1(X3))) ),
    inference(subsumption_resolution,[],[f278,f48])).

fof(f278,plain,(
    ! [X2,X3] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) = k10_relat_1(k6_relat_1(X2),k1_relat_1(k6_relat_1(X3)))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f274,f48])).

fof(f274,plain,(
    ! [X2,X3] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) = k10_relat_1(k6_relat_1(X2),k1_relat_1(k6_relat_1(X3)))
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f151,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f151,plain,(
    ! [X4,X5] : k1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X4))) = k2_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X4))) ),
    inference(backward_demodulation,[],[f143,f144])).

fof(f144,plain,(
    ! [X6,X7] : k1_setfam_1(k3_enumset1(X6,X6,X6,X6,X7)) = k2_relat_1(k5_relat_1(k6_relat_1(X7),k6_relat_1(X6))) ),
    inference(superposition,[],[f51,f76])).

fof(f76,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f59,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f59,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f51,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f143,plain,(
    ! [X4,X5] : k1_setfam_1(k3_enumset1(X4,X4,X4,X4,X5)) = k1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X4))) ),
    inference(superposition,[],[f50,f76])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k2_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(X2,X1)),k6_relat_1(X0))) ) ),
    inference(backward_demodulation,[],[f150,f151])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(X2,X1)),k6_relat_1(X0)))
      | ~ v1_relat_1(X2) ) ),
    inference(backward_demodulation,[],[f77,f143])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f69,f75])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f85,f48])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f61,f50])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (16330)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.49  % (16342)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.50  % (16334)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (16324)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (16332)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (16331)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (16347)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (16340)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (16326)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (16343)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (16339)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (16325)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (16323)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (16322)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (16335)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (16346)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (16321)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (16333)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (16327)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (16341)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (16348)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (16336)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (16345)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (16350)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (16328)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (16337)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (16329)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (16338)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (16349)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.56  % (16344)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.82/0.61  % (16343)Refutation found. Thanks to Tanya!
% 1.82/0.61  % SZS status Theorem for theBenchmark
% 1.82/0.61  % SZS output start Proof for theBenchmark
% 1.82/0.61  fof(f749,plain,(
% 1.82/0.61    $false),
% 1.82/0.61    inference(subsumption_resolution,[],[f747,f47])).
% 1.82/0.61  fof(f47,plain,(
% 1.82/0.61    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.82/0.61    inference(cnf_transformation,[],[f42])).
% 1.82/0.61  fof(f42,plain,(
% 1.82/0.61    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.82/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f41])).
% 1.82/0.61  fof(f41,plain,(
% 1.82/0.61    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.82/0.61    introduced(choice_axiom,[])).
% 1.82/0.61  fof(f25,plain,(
% 1.82/0.61    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.82/0.61    inference(flattening,[],[f24])).
% 1.82/0.61  fof(f24,plain,(
% 1.82/0.61    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.82/0.61    inference(ennf_transformation,[],[f23])).
% 1.82/0.61  fof(f23,negated_conjecture,(
% 1.82/0.61    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.82/0.61    inference(negated_conjecture,[],[f22])).
% 1.82/0.61  fof(f22,conjecture,(
% 1.82/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.82/0.61  fof(f747,plain,(
% 1.82/0.61    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.82/0.61    inference(superposition,[],[f360,f743])).
% 1.82/0.61  fof(f743,plain,(
% 1.82/0.61    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 1.82/0.61    inference(forward_demodulation,[],[f737,f482])).
% 1.82/0.61  fof(f482,plain,(
% 1.82/0.61    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.82/0.61    inference(resolution,[],[f475,f421])).
% 1.82/0.61  fof(f421,plain,(
% 1.82/0.61    ( ! [X8] : (~r1_tarski(X8,k1_relat_1(k7_relat_1(sK1,X8))) | k1_relat_1(k7_relat_1(sK1,X8)) = X8) )),
% 1.82/0.61    inference(resolution,[],[f101,f45])).
% 1.82/0.61  fof(f45,plain,(
% 1.82/0.61    v1_relat_1(sK1)),
% 1.82/0.61    inference(cnf_transformation,[],[f42])).
% 1.82/0.61  fof(f101,plain,(
% 1.82/0.61    ( ! [X6,X5] : (~v1_relat_1(X6) | ~r1_tarski(X5,k1_relat_1(k7_relat_1(X6,X5))) | k1_relat_1(k7_relat_1(X6,X5)) = X5) )),
% 1.82/0.61    inference(resolution,[],[f67,f62])).
% 1.82/0.61  fof(f62,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f33])).
% 1.82/0.61  fof(f33,plain,(
% 1.82/0.61    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.82/0.61    inference(ennf_transformation,[],[f17])).
% 1.82/0.61  fof(f17,axiom,(
% 1.82/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.82/0.61  fof(f67,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f44])).
% 1.82/0.61  fof(f44,plain,(
% 1.82/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.82/0.61    inference(flattening,[],[f43])).
% 1.82/0.61  fof(f43,plain,(
% 1.82/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.82/0.61    inference(nnf_transformation,[],[f1])).
% 1.82/0.61  fof(f1,axiom,(
% 1.82/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.82/0.61  fof(f475,plain,(
% 1.82/0.61    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.82/0.61    inference(forward_demodulation,[],[f470,f50])).
% 1.82/0.61  fof(f50,plain,(
% 1.82/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f16])).
% 1.82/0.61  fof(f16,axiom,(
% 1.82/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.82/0.61  fof(f470,plain,(
% 1.82/0.61    r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.82/0.61    inference(superposition,[],[f234,f459])).
% 1.82/0.61  fof(f459,plain,(
% 1.82/0.61    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),
% 1.82/0.61    inference(superposition,[],[f457,f83])).
% 1.82/0.61  fof(f83,plain,(
% 1.82/0.61    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f80,f48])).
% 1.82/0.61  fof(f48,plain,(
% 1.82/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f19])).
% 1.82/0.61  fof(f19,axiom,(
% 1.82/0.61    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.82/0.61  fof(f80,plain,(
% 1.82/0.61    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.82/0.61    inference(superposition,[],[f52,f50])).
% 1.82/0.61  fof(f52,plain,(
% 1.82/0.61    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f26])).
% 1.82/0.61  fof(f26,plain,(
% 1.82/0.61    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.82/0.61    inference(ennf_transformation,[],[f18])).
% 1.82/0.61  fof(f18,axiom,(
% 1.82/0.61    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 1.82/0.61  fof(f457,plain,(
% 1.82/0.61    ( ! [X21] : (k7_relat_1(k6_relat_1(X21),sK0) = k7_relat_1(k7_relat_1(k6_relat_1(X21),sK0),k1_relat_1(sK1))) )),
% 1.82/0.61    inference(resolution,[],[f139,f46])).
% 1.82/0.61  fof(f46,plain,(
% 1.82/0.61    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.82/0.61    inference(cnf_transformation,[],[f42])).
% 1.82/0.61  fof(f139,plain,(
% 1.82/0.61    ( ! [X4,X2,X3] : (~r1_tarski(X2,X3) | k7_relat_1(k6_relat_1(X4),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X2),X3)) )),
% 1.82/0.61    inference(resolution,[],[f70,f48])).
% 1.82/0.61  fof(f70,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f38])).
% 1.82/0.61  fof(f38,plain,(
% 1.82/0.61    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.82/0.61    inference(flattening,[],[f37])).
% 1.82/0.61  fof(f37,plain,(
% 1.82/0.61    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.82/0.61    inference(ennf_transformation,[],[f9])).
% 1.82/0.61  fof(f9,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 1.82/0.61  fof(f234,plain,(
% 1.82/0.61    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X1)))) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f230,f48])).
% 1.82/0.61  fof(f230,plain,(
% 1.82/0.61    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.82/0.61    inference(superposition,[],[f62,f214])).
% 1.82/0.61  fof(f214,plain,(
% 1.82/0.61    ( ! [X4] : (k7_relat_1(k6_relat_1(X4),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X4),k1_relat_1(k7_relat_1(sK1,X4)))) )),
% 1.82/0.61    inference(forward_demodulation,[],[f211,f50])).
% 1.82/0.61  fof(f211,plain,(
% 1.82/0.61    ( ! [X4] : (k7_relat_1(k6_relat_1(X4),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X4),k1_relat_1(k7_relat_1(sK1,k1_relat_1(k6_relat_1(X4)))))) )),
% 1.82/0.61    inference(resolution,[],[f185,f48])).
% 1.82/0.61  fof(f185,plain,(
% 1.82/0.61    ( ! [X8] : (~v1_relat_1(X8) | k7_relat_1(X8,k1_relat_1(sK1)) = k7_relat_1(X8,k1_relat_1(k7_relat_1(sK1,k1_relat_1(X8))))) )),
% 1.82/0.61    inference(resolution,[],[f55,f45])).
% 1.82/0.61  fof(f55,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f29])).
% 1.82/0.61  fof(f29,plain,(
% 1.82/0.61    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.82/0.61    inference(ennf_transformation,[],[f15])).
% 1.82/0.61  fof(f15,axiom,(
% 1.82/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).
% 1.82/0.61  fof(f737,plain,(
% 1.82/0.61    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 1.82/0.61    inference(superposition,[],[f518,f697])).
% 1.82/0.61  fof(f697,plain,(
% 1.82/0.61    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 1.82/0.61    inference(superposition,[],[f574,f482])).
% 1.82/0.61  fof(f574,plain,(
% 1.82/0.61    ( ! [X10] : (k2_relat_1(k7_relat_1(sK1,X10)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X10)))) )),
% 1.82/0.61    inference(forward_demodulation,[],[f573,f560])).
% 1.82/0.61  fof(f560,plain,(
% 1.82/0.61    ( ! [X9] : (k1_relat_1(k7_relat_1(k6_relat_1(X9),k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X9))) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f555,f234])).
% 1.82/0.61  fof(f555,plain,(
% 1.82/0.61    ( ! [X9] : (~r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X9),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X9))) | k1_relat_1(k7_relat_1(k6_relat_1(X9),k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X9))) )),
% 1.82/0.61    inference(superposition,[],[f421,f466])).
% 1.82/0.61  fof(f466,plain,(
% 1.82/0.61    ( ! [X8] : (k7_relat_1(sK1,X8) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X8),k1_relat_1(sK1))))) )),
% 1.82/0.61    inference(resolution,[],[f187,f45])).
% 1.82/0.61  fof(f187,plain,(
% 1.82/0.61    ( ! [X6,X7] : (~v1_relat_1(X6) | k7_relat_1(X6,k1_relat_1(k7_relat_1(k6_relat_1(X7),k1_relat_1(X6)))) = k7_relat_1(X6,X7)) )),
% 1.82/0.61    inference(forward_demodulation,[],[f184,f50])).
% 1.82/0.61  fof(f184,plain,(
% 1.82/0.61    ( ! [X6,X7] : (k7_relat_1(X6,k1_relat_1(k6_relat_1(X7))) = k7_relat_1(X6,k1_relat_1(k7_relat_1(k6_relat_1(X7),k1_relat_1(X6)))) | ~v1_relat_1(X6)) )),
% 1.82/0.61    inference(resolution,[],[f55,f48])).
% 1.82/0.61  fof(f573,plain,(
% 1.82/0.61    ( ! [X10] : (k9_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X10),k1_relat_1(sK1)))) = k2_relat_1(k7_relat_1(sK1,X10))) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f556,f45])).
% 1.82/0.61  fof(f556,plain,(
% 1.82/0.61    ( ! [X10] : (k9_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X10),k1_relat_1(sK1)))) = k2_relat_1(k7_relat_1(sK1,X10)) | ~v1_relat_1(sK1)) )),
% 1.82/0.61    inference(superposition,[],[f63,f466])).
% 1.82/0.61  fof(f63,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f34])).
% 1.82/0.61  fof(f34,plain,(
% 1.82/0.61    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.82/0.61    inference(ennf_transformation,[],[f10])).
% 1.82/0.61  fof(f10,axiom,(
% 1.82/0.61    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.82/0.61  fof(f518,plain,(
% 1.82/0.61    ( ! [X8] : (k1_relat_1(k7_relat_1(sK1,X8)) = k10_relat_1(k7_relat_1(sK1,X8),k2_relat_1(k7_relat_1(sK1,X8)))) )),
% 1.82/0.61    inference(resolution,[],[f94,f45])).
% 1.82/0.61  fof(f94,plain,(
% 1.82/0.61    ( ! [X2,X1] : (~v1_relat_1(X1) | k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) = k1_relat_1(k7_relat_1(X1,X2))) )),
% 1.82/0.61    inference(resolution,[],[f53,f60])).
% 1.82/0.61  fof(f60,plain,(
% 1.82/0.61    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f31])).
% 1.82/0.61  fof(f31,plain,(
% 1.82/0.61    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.82/0.61    inference(ennf_transformation,[],[f7])).
% 1.82/0.61  fof(f7,axiom,(
% 1.82/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.82/0.61  fof(f53,plain,(
% 1.82/0.61    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f27])).
% 1.82/0.61  fof(f27,plain,(
% 1.82/0.61    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.82/0.61    inference(ennf_transformation,[],[f13])).
% 1.82/0.61  fof(f13,axiom,(
% 1.82/0.61    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.82/0.61  fof(f360,plain,(
% 1.82/0.61    ( ! [X2,X3] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X3),X2),k10_relat_1(sK1,X2))) )),
% 1.82/0.61    inference(superposition,[],[f86,f353])).
% 1.82/0.61  fof(f353,plain,(
% 1.82/0.61    ( ! [X12,X11] : (k10_relat_1(k7_relat_1(sK1,X11),X12) = k10_relat_1(k6_relat_1(k10_relat_1(sK1,X12)),X11)) )),
% 1.82/0.61    inference(resolution,[],[f292,f45])).
% 1.82/0.61  fof(f292,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k10_relat_1(k6_relat_1(k10_relat_1(X2,X1)),X0)) )),
% 1.82/0.61    inference(backward_demodulation,[],[f153,f280])).
% 1.82/0.61  fof(f280,plain,(
% 1.82/0.61    ( ! [X2,X3] : (k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) = k10_relat_1(k6_relat_1(X2),X3)) )),
% 1.82/0.61    inference(forward_demodulation,[],[f279,f50])).
% 1.82/0.61  fof(f279,plain,(
% 1.82/0.61    ( ! [X2,X3] : (k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) = k10_relat_1(k6_relat_1(X2),k1_relat_1(k6_relat_1(X3)))) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f278,f48])).
% 1.82/0.61  fof(f278,plain,(
% 1.82/0.61    ( ! [X2,X3] : (k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) = k10_relat_1(k6_relat_1(X2),k1_relat_1(k6_relat_1(X3))) | ~v1_relat_1(k6_relat_1(X2))) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f274,f48])).
% 1.82/0.61  fof(f274,plain,(
% 1.82/0.61    ( ! [X2,X3] : (k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) = k10_relat_1(k6_relat_1(X2),k1_relat_1(k6_relat_1(X3))) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 1.82/0.61    inference(superposition,[],[f151,f54])).
% 1.82/0.61  fof(f54,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f28])).
% 1.82/0.61  fof(f28,plain,(
% 1.82/0.61    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.82/0.61    inference(ennf_transformation,[],[f14])).
% 1.82/0.61  fof(f14,axiom,(
% 1.82/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.82/0.61  fof(f151,plain,(
% 1.82/0.61    ( ! [X4,X5] : (k1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X4))) = k2_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X4)))) )),
% 1.82/0.61    inference(backward_demodulation,[],[f143,f144])).
% 1.82/0.61  fof(f144,plain,(
% 1.82/0.61    ( ! [X6,X7] : (k1_setfam_1(k3_enumset1(X6,X6,X6,X6,X7)) = k2_relat_1(k5_relat_1(k6_relat_1(X7),k6_relat_1(X6)))) )),
% 1.82/0.61    inference(superposition,[],[f51,f76])).
% 1.82/0.61  fof(f76,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.82/0.61    inference(definition_unfolding,[],[f59,f75])).
% 1.82/0.61  fof(f75,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.82/0.61    inference(definition_unfolding,[],[f57,f74])).
% 1.82/0.61  fof(f74,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f58,f73])).
% 1.82/0.61  fof(f73,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f68,f72])).
% 1.82/0.61  fof(f72,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f5])).
% 1.82/0.61  fof(f5,axiom,(
% 1.82/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.82/0.61  fof(f68,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f4])).
% 1.82/0.61  fof(f4,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.82/0.61  fof(f58,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f3])).
% 1.82/0.61  fof(f3,axiom,(
% 1.82/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.82/0.61  fof(f57,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f6])).
% 1.82/0.61  fof(f6,axiom,(
% 1.82/0.61    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.82/0.61  fof(f59,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f21])).
% 1.82/0.61  fof(f21,axiom,(
% 1.82/0.61    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.82/0.61  fof(f51,plain,(
% 1.82/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f16])).
% 1.82/0.61  fof(f143,plain,(
% 1.82/0.61    ( ! [X4,X5] : (k1_setfam_1(k3_enumset1(X4,X4,X4,X4,X5)) = k1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X4)))) )),
% 1.82/0.61    inference(superposition,[],[f50,f76])).
% 1.82/0.61  fof(f153,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k2_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(X2,X1)),k6_relat_1(X0)))) )),
% 1.82/0.61    inference(backward_demodulation,[],[f150,f151])).
% 1.82/0.61  fof(f150,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(X2,X1)),k6_relat_1(X0))) | ~v1_relat_1(X2)) )),
% 1.82/0.61    inference(backward_demodulation,[],[f77,f143])).
% 1.82/0.61  fof(f77,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f69,f75])).
% 1.82/0.61  fof(f69,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f36])).
% 1.82/0.61  fof(f36,plain,(
% 1.82/0.61    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.82/0.61    inference(ennf_transformation,[],[f20])).
% 1.82/0.61  fof(f20,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.82/0.61  fof(f86,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f85,f48])).
% 1.82/0.61  fof(f85,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.82/0.61    inference(superposition,[],[f61,f50])).
% 1.82/0.61  fof(f61,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f32])).
% 1.82/0.61  fof(f32,plain,(
% 1.82/0.61    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.82/0.61    inference(ennf_transformation,[],[f12])).
% 1.82/0.61  fof(f12,axiom,(
% 1.82/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.82/0.61  % SZS output end Proof for theBenchmark
% 1.82/0.61  % (16343)------------------------------
% 1.82/0.61  % (16343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (16343)Termination reason: Refutation
% 1.82/0.61  
% 1.82/0.61  % (16343)Memory used [KB]: 6908
% 1.82/0.61  % (16343)Time elapsed: 0.154 s
% 1.82/0.61  % (16343)------------------------------
% 1.82/0.61  % (16343)------------------------------
% 1.96/0.62  % (16320)Success in time 0.256 s
%------------------------------------------------------------------------------
