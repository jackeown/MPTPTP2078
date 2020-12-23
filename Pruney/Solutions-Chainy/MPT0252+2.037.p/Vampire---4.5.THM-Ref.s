%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:55 EST 2020

% Result     : Theorem 8.88s
% Output     : Refutation 8.88s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 273 expanded)
%              Number of leaves         :   18 (  83 expanded)
%              Depth                    :   24
%              Number of atoms          :  136 ( 417 expanded)
%              Number of equality atoms :   61 ( 221 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7290,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7277,f36])).

fof(f36,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f7277,plain,(
    r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f71,f7272])).

fof(f7272,plain,(
    sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f7120,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f7120,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f77,f6937])).

fof(f6937,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f6115,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f6115,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f44,f6103])).

fof(f6103,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k2_tarski(X5,X4) ),
    inference(subsumption_resolution,[],[f6102,f70])).

fof(f70,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f52,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f6102,plain,(
    ! [X4,X5] :
      ( k2_tarski(X4,X5) = k2_tarski(X5,X4)
      | ~ r2_hidden(X5,k2_tarski(X5,X4)) ) ),
    inference(subsumption_resolution,[],[f6098,f74])).

fof(f74,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(resolution,[],[f53,f64])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6098,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k2_tarski(X5,X4))
      | k2_tarski(X4,X5) = k2_tarski(X5,X4)
      | ~ r2_hidden(X5,k2_tarski(X5,X4)) ) ),
    inference(resolution,[],[f6075,f124])).

fof(f124,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X7,k2_tarski(X8,X6))
      | ~ r2_hidden(X8,X7)
      | k2_tarski(X8,X6) = X7
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f54,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6075,plain,(
    ! [X2,X3] : r1_tarski(k2_tarski(X2,X3),k2_tarski(X3,X2)) ),
    inference(backward_demodulation,[],[f6051,f6067])).

fof(f6067,plain,(
    ! [X4,X5] : k1_enumset1(X4,X5,X5) = k2_tarski(X5,X4) ),
    inference(subsumption_resolution,[],[f6062,f6047])).

fof(f6047,plain,(
    ! [X0,X1] : r1_tarski(k1_enumset1(X1,X0,X0),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f6039,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f6039,plain,(
    ! [X28,X29,X27] : r1_tarski(k1_enumset1(X27,X28,X29),k1_enumset1(X29,X28,X27)) ),
    inference(superposition,[],[f1045,f3041])).

fof(f3041,plain,(
    ! [X6,X8,X7] : k1_enumset1(X6,X7,X8) = k5_enumset1(X8,X7,X6,X6,X8,X7,X6) ),
    inference(forward_demodulation,[],[f3037,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f3037,plain,(
    ! [X6,X8,X7] : k2_enumset1(X6,X6,X7,X8) = k5_enumset1(X8,X7,X6,X6,X8,X7,X6) ),
    inference(superposition,[],[f2714,f187])).

fof(f187,plain,(
    ! [X10,X8,X11,X9] : k2_enumset1(X8,X9,X10,X11) = k6_enumset1(X8,X9,X10,X11,X8,X9,X10,X11) ),
    inference(superposition,[],[f61,f40])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f2714,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k5_enumset1(X6,X5,X4,X3,X2,X1,X0) ),
    inference(backward_demodulation,[],[f184,f2711])).

fof(f2711,plain,(
    ! [X28,X26,X24,X23,X29,X27,X25] : k2_xboole_0(k2_enumset1(X29,X28,X27,X26),k1_enumset1(X25,X24,X23)) = k5_enumset1(X26,X27,X28,X29,X23,X24,X25) ),
    inference(backward_demodulation,[],[f2028,f2710])).

fof(f2710,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X6,X0) = k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) ),
    inference(forward_demodulation,[],[f2700,f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(f2700,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0)) ),
    inference(superposition,[],[f248,f38])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f248,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(forward_demodulation,[],[f244,f221])).

fof(f221,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(forward_demodulation,[],[f215,f61])).

fof(f215,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(superposition,[],[f62,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(f244,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(superposition,[],[f63,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

fof(f2028,plain,(
    ! [X28,X26,X24,X23,X29,X27,X25] : k6_enumset1(X26,X27,X28,X29,X23,X24,X25,X25) = k2_xboole_0(k2_enumset1(X29,X28,X27,X26),k1_enumset1(X25,X24,X23)) ),
    inference(superposition,[],[f182,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0) ),
    inference(superposition,[],[f55,f50])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f182,plain,(
    ! [X14,X12,X10,X8,X7,X13,X11,X9] : k6_enumset1(X7,X8,X9,X10,X11,X12,X13,X14) = k2_xboole_0(k2_enumset1(X10,X9,X8,X7),k2_enumset1(X11,X12,X13,X14)) ),
    inference(superposition,[],[f61,f55])).

fof(f184,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f61,f50])).

fof(f1045,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(forward_demodulation,[],[f1039,f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f1039,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
    inference(superposition,[],[f190,f50])).

fof(f190,plain,(
    ! [X14,X12,X19,X17,X15,X13,X18,X16] : r1_tarski(k2_enumset1(X12,X13,X14,X15),k6_enumset1(X12,X13,X14,X15,X16,X17,X18,X19)) ),
    inference(superposition,[],[f41,f61])).

fof(f6062,plain,(
    ! [X4,X5] :
      ( k1_enumset1(X4,X5,X5) = k2_tarski(X5,X4)
      | ~ r1_tarski(k1_enumset1(X4,X5,X5),k2_tarski(X5,X4)) ) ),
    inference(resolution,[],[f6044,f49])).

fof(f6044,plain,(
    ! [X0,X1] : r1_tarski(k2_tarski(X0,X1),k1_enumset1(X1,X0,X0)) ),
    inference(superposition,[],[f6039,f45])).

fof(f6051,plain,(
    ! [X2,X3] : r1_tarski(k1_enumset1(X3,X2,X2),k2_tarski(X3,X2)) ),
    inference(forward_demodulation,[],[f6045,f45])).

fof(f6045,plain,(
    ! [X2,X3] : r1_tarski(k1_enumset1(X3,X2,X2),k1_enumset1(X3,X3,X2)) ),
    inference(superposition,[],[f6039,f299])).

fof(f299,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f129,f50])).

fof(f77,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2))
    | sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X4,X2,X3] : r2_hidden(X2,k2_xboole_0(k2_tarski(X2,X3),X4)) ),
    inference(resolution,[],[f52,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (20443)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.47  % (20443)Refutation not found, incomplete strategy% (20443)------------------------------
% 0.19/0.47  % (20443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (20443)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (20443)Memory used [KB]: 1663
% 0.19/0.47  % (20443)Time elapsed: 0.082 s
% 0.19/0.47  % (20443)------------------------------
% 0.19/0.47  % (20443)------------------------------
% 0.19/0.48  % (20456)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.48  % (20459)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.49  % (20451)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.49  % (20448)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (20465)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.49  % (20456)Refutation not found, incomplete strategy% (20456)------------------------------
% 0.19/0.49  % (20456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (20456)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (20456)Memory used [KB]: 1663
% 0.19/0.49  % (20456)Time elapsed: 0.083 s
% 0.19/0.49  % (20456)------------------------------
% 0.19/0.49  % (20456)------------------------------
% 0.19/0.49  % (20457)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.50  % (20446)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.50  % (20467)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.50  % (20467)Refutation not found, incomplete strategy% (20467)------------------------------
% 0.19/0.50  % (20467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (20467)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (20467)Memory used [KB]: 6140
% 0.19/0.50  % (20467)Time elapsed: 0.112 s
% 0.19/0.50  % (20467)------------------------------
% 0.19/0.50  % (20467)------------------------------
% 0.19/0.50  % (20464)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.50  % (20442)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.50  % (20459)Refutation not found, incomplete strategy% (20459)------------------------------
% 0.19/0.50  % (20459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (20459)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (20459)Memory used [KB]: 1791
% 0.19/0.50  % (20459)Time elapsed: 0.092 s
% 0.19/0.50  % (20459)------------------------------
% 0.19/0.50  % (20459)------------------------------
% 0.19/0.50  % (20449)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.50  % (20447)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (20444)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.51  % (20445)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.52  % (20462)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.52  % (20450)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.52  % (20463)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.52  % (20453)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.52  % (20455)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.52  % (20452)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.52  % (20471)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.53  % (20471)Refutation not found, incomplete strategy% (20471)------------------------------
% 0.19/0.53  % (20471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (20471)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (20471)Memory used [KB]: 1663
% 0.19/0.53  % (20471)Time elapsed: 0.129 s
% 0.19/0.53  % (20471)------------------------------
% 0.19/0.53  % (20471)------------------------------
% 0.19/0.53  % (20468)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (20454)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.53  % (20468)Refutation not found, incomplete strategy% (20468)------------------------------
% 0.19/0.53  % (20468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (20468)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (20468)Memory used [KB]: 6140
% 0.19/0.53  % (20468)Time elapsed: 0.129 s
% 0.19/0.53  % (20468)------------------------------
% 0.19/0.53  % (20468)------------------------------
% 0.19/0.53  % (20454)Refutation not found, incomplete strategy% (20454)------------------------------
% 0.19/0.53  % (20454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (20454)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (20454)Memory used [KB]: 10618
% 0.19/0.53  % (20454)Time elapsed: 0.131 s
% 0.19/0.53  % (20454)------------------------------
% 0.19/0.53  % (20454)------------------------------
% 0.19/0.53  % (20466)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.53  % (20470)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.53  % (20466)Refutation not found, incomplete strategy% (20466)------------------------------
% 0.19/0.53  % (20466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (20466)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (20466)Memory used [KB]: 10746
% 0.19/0.53  % (20466)Time elapsed: 0.129 s
% 0.19/0.53  % (20466)------------------------------
% 0.19/0.53  % (20466)------------------------------
% 0.19/0.53  % (20470)Refutation not found, incomplete strategy% (20470)------------------------------
% 0.19/0.53  % (20470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (20470)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (20470)Memory used [KB]: 10874
% 0.19/0.53  % (20470)Time elapsed: 0.131 s
% 0.19/0.53  % (20470)------------------------------
% 0.19/0.53  % (20470)------------------------------
% 0.19/0.53  % (20461)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.53  % (20458)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.53  % (20460)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.53  % (20458)Refutation not found, incomplete strategy% (20458)------------------------------
% 0.19/0.53  % (20458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (20458)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (20458)Memory used [KB]: 10618
% 0.19/0.53  % (20458)Time elapsed: 0.141 s
% 0.19/0.53  % (20458)------------------------------
% 0.19/0.53  % (20458)------------------------------
% 0.19/0.53  % (20460)Refutation not found, incomplete strategy% (20460)------------------------------
% 0.19/0.53  % (20460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (20460)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (20460)Memory used [KB]: 1663
% 0.19/0.53  % (20460)Time elapsed: 0.142 s
% 0.19/0.53  % (20460)------------------------------
% 0.19/0.53  % (20460)------------------------------
% 0.19/0.54  % (20452)Refutation not found, incomplete strategy% (20452)------------------------------
% 0.19/0.54  % (20452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (20452)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (20452)Memory used [KB]: 10874
% 0.19/0.54  % (20452)Time elapsed: 0.143 s
% 0.19/0.54  % (20452)------------------------------
% 0.19/0.54  % (20452)------------------------------
% 0.19/0.54  % (20469)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.54  % (20469)Refutation not found, incomplete strategy% (20469)------------------------------
% 0.19/0.54  % (20469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (20469)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (20469)Memory used [KB]: 6140
% 0.19/0.54  % (20469)Time elapsed: 0.141 s
% 0.19/0.54  % (20469)------------------------------
% 0.19/0.54  % (20469)------------------------------
% 0.19/0.54  % (20453)Refutation not found, incomplete strategy% (20453)------------------------------
% 0.19/0.54  % (20453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (20453)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (20453)Memory used [KB]: 6396
% 0.19/0.54  % (20453)Time elapsed: 0.134 s
% 0.19/0.54  % (20453)------------------------------
% 0.19/0.54  % (20453)------------------------------
% 0.19/0.60  % (20457)Refutation not found, incomplete strategy% (20457)------------------------------
% 0.19/0.60  % (20457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.60  % (20513)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.99/0.61  % (20505)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.99/0.61  % (20457)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.61  
% 1.99/0.61  % (20457)Memory used [KB]: 6140
% 1.99/0.61  % (20457)Time elapsed: 0.160 s
% 1.99/0.61  % (20457)------------------------------
% 1.99/0.61  % (20457)------------------------------
% 1.99/0.63  % (20517)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.99/0.63  % (20517)Refutation not found, incomplete strategy% (20517)------------------------------
% 1.99/0.63  % (20517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.63  % (20517)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.63  
% 1.99/0.63  % (20517)Memory used [KB]: 6268
% 1.99/0.63  % (20517)Time elapsed: 0.101 s
% 1.99/0.63  % (20517)------------------------------
% 1.99/0.63  % (20517)------------------------------
% 2.16/0.63  % (20518)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.18/0.63  % (20518)Refutation not found, incomplete strategy% (20518)------------------------------
% 2.18/0.63  % (20518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.63  % (20518)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.63  
% 2.18/0.63  % (20518)Memory used [KB]: 10618
% 2.18/0.63  % (20518)Time elapsed: 0.108 s
% 2.18/0.63  % (20518)------------------------------
% 2.18/0.63  % (20518)------------------------------
% 2.18/0.65  % (20532)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.18/0.65  % (20445)Refutation not found, incomplete strategy% (20445)------------------------------
% 2.18/0.65  % (20445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.65  % (20445)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.65  
% 2.18/0.65  % (20445)Memory used [KB]: 6140
% 2.18/0.65  % (20445)Time elapsed: 0.249 s
% 2.18/0.65  % (20445)------------------------------
% 2.18/0.65  % (20445)------------------------------
% 2.18/0.65  % (20532)Refutation not found, incomplete strategy% (20532)------------------------------
% 2.18/0.65  % (20532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.65  % (20532)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.65  
% 2.18/0.65  % (20532)Memory used [KB]: 1791
% 2.18/0.65  % (20532)Time elapsed: 0.103 s
% 2.18/0.65  % (20532)------------------------------
% 2.18/0.65  % (20532)------------------------------
% 2.18/0.65  % (20533)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.18/0.66  % (20533)Refutation not found, incomplete strategy% (20533)------------------------------
% 2.18/0.66  % (20533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.66  % (20533)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.66  
% 2.18/0.66  % (20533)Memory used [KB]: 10618
% 2.18/0.66  % (20533)Time elapsed: 0.102 s
% 2.18/0.66  % (20533)------------------------------
% 2.18/0.66  % (20533)------------------------------
% 2.18/0.66  % (20444)Refutation not found, incomplete strategy% (20444)------------------------------
% 2.18/0.66  % (20444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.66  % (20444)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.66  
% 2.18/0.66  % (20444)Memory used [KB]: 6268
% 2.18/0.66  % (20444)Time elapsed: 0.241 s
% 2.18/0.66  % (20444)------------------------------
% 2.18/0.66  % (20444)------------------------------
% 2.18/0.66  % (20539)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.18/0.66  % (20530)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.18/0.66  % (20530)Refutation not found, incomplete strategy% (20530)------------------------------
% 2.18/0.66  % (20530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.66  % (20530)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.66  
% 2.18/0.66  % (20530)Memory used [KB]: 10746
% 2.18/0.66  % (20530)Time elapsed: 0.113 s
% 2.18/0.66  % (20530)------------------------------
% 2.18/0.66  % (20530)------------------------------
% 2.18/0.66  % (20541)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.18/0.67  % (20442)Refutation not found, incomplete strategy% (20442)------------------------------
% 2.18/0.67  % (20442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.67  % (20442)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.67  
% 2.18/0.67  % (20442)Memory used [KB]: 1791
% 2.18/0.67  % (20442)Time elapsed: 0.271 s
% 2.18/0.67  % (20442)------------------------------
% 2.18/0.67  % (20442)------------------------------
% 2.18/0.67  % (20540)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.18/0.67  % (20536)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.18/0.67  % (20540)Refutation not found, incomplete strategy% (20540)------------------------------
% 2.18/0.67  % (20540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.67  % (20540)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.67  
% 2.18/0.67  % (20540)Memory used [KB]: 10746
% 2.18/0.67  % (20540)Time elapsed: 0.106 s
% 2.18/0.67  % (20540)------------------------------
% 2.18/0.67  % (20540)------------------------------
% 2.18/0.67  % (20543)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.18/0.67  % (20534)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.18/0.67  % (20543)Refutation not found, incomplete strategy% (20543)------------------------------
% 2.18/0.67  % (20543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.67  % (20543)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.67  
% 2.18/0.67  % (20543)Memory used [KB]: 10746
% 2.18/0.67  % (20543)Time elapsed: 0.104 s
% 2.18/0.67  % (20543)------------------------------
% 2.18/0.67  % (20543)------------------------------
% 2.18/0.68  % (20541)Refutation not found, incomplete strategy% (20541)------------------------------
% 2.18/0.68  % (20541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.68  % (20541)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.68  
% 2.18/0.68  % (20541)Memory used [KB]: 1791
% 2.18/0.68  % (20541)Time elapsed: 0.111 s
% 2.18/0.68  % (20541)------------------------------
% 2.18/0.68  % (20541)------------------------------
% 2.18/0.68  % (20538)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.18/0.69  % (20450)Refutation not found, incomplete strategy% (20450)------------------------------
% 2.18/0.69  % (20450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.69  % (20450)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.69  
% 2.18/0.69  % (20450)Memory used [KB]: 6140
% 2.18/0.69  % (20450)Time elapsed: 0.295 s
% 2.18/0.69  % (20450)------------------------------
% 2.18/0.69  % (20450)------------------------------
% 2.18/0.69  % (20538)Refutation not found, incomplete strategy% (20538)------------------------------
% 2.18/0.69  % (20538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.69  % (20538)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.69  
% 2.18/0.69  % (20538)Memory used [KB]: 10746
% 2.18/0.69  % (20538)Time elapsed: 0.138 s
% 2.18/0.69  % (20538)------------------------------
% 2.18/0.69  % (20538)------------------------------
% 2.76/0.72  % (20595)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.76/0.74  % (20617)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.76/0.75  % (20606)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.76/0.76  % (20618)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 2.76/0.76  % (20612)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.76/0.76  % (20620)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 2.76/0.76  % (20620)Refutation not found, incomplete strategy% (20620)------------------------------
% 2.76/0.76  % (20620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.76  % (20620)Termination reason: Refutation not found, incomplete strategy
% 2.76/0.76  
% 2.76/0.76  % (20620)Memory used [KB]: 1663
% 2.76/0.76  % (20620)Time elapsed: 0.093 s
% 2.76/0.76  % (20620)------------------------------
% 2.76/0.76  % (20620)------------------------------
% 3.08/0.76  % (20622)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.08/0.79  % (20536)Refutation not found, incomplete strategy% (20536)------------------------------
% 3.08/0.79  % (20536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.08/0.79  % (20536)Termination reason: Refutation not found, incomplete strategy
% 3.08/0.79  
% 3.08/0.79  % (20536)Memory used [KB]: 6140
% 3.08/0.79  % (20536)Time elapsed: 0.213 s
% 3.08/0.79  % (20536)------------------------------
% 3.08/0.79  % (20536)------------------------------
% 3.08/0.82  % (20595)Refutation not found, incomplete strategy% (20595)------------------------------
% 3.08/0.82  % (20595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.08/0.82  % (20595)Termination reason: Refutation not found, incomplete strategy
% 3.08/0.82  
% 3.08/0.82  % (20595)Memory used [KB]: 6268
% 3.08/0.82  % (20595)Time elapsed: 0.160 s
% 3.08/0.82  % (20595)------------------------------
% 3.08/0.82  % (20595)------------------------------
% 3.08/0.86  % (20606)Refutation not found, incomplete strategy% (20606)------------------------------
% 3.08/0.86  % (20606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.08/0.86  % (20606)Termination reason: Refutation not found, incomplete strategy
% 3.08/0.86  
% 3.08/0.86  % (20606)Memory used [KB]: 6140
% 3.08/0.86  % (20606)Time elapsed: 0.203 s
% 3.08/0.86  % (20606)------------------------------
% 3.08/0.86  % (20606)------------------------------
% 4.01/0.91  % (20448)Time limit reached!
% 4.01/0.91  % (20448)------------------------------
% 4.01/0.91  % (20448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.91  % (20448)Termination reason: Time limit
% 4.01/0.91  % (20448)Termination phase: Saturation
% 4.01/0.91  
% 4.01/0.91  % (20448)Memory used [KB]: 19445
% 4.01/0.91  % (20448)Time elapsed: 0.500 s
% 4.01/0.91  % (20448)------------------------------
% 4.01/0.91  % (20448)------------------------------
% 4.70/1.05  % (20449)Time limit reached!
% 4.70/1.05  % (20449)------------------------------
% 4.70/1.05  % (20449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.70/1.05  % (20449)Termination reason: Time limit
% 4.70/1.05  % (20449)Termination phase: Saturation
% 4.70/1.05  
% 4.70/1.05  % (20449)Memory used [KB]: 19573
% 4.70/1.05  % (20449)Time elapsed: 0.600 s
% 4.70/1.05  % (20449)------------------------------
% 4.70/1.05  % (20449)------------------------------
% 5.11/1.10  % (20622)Time limit reached!
% 5.11/1.10  % (20622)------------------------------
% 5.11/1.10  % (20622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.11/1.11  % (20622)Termination reason: Time limit
% 5.11/1.11  % (20622)Termination phase: Saturation
% 5.11/1.11  
% 5.11/1.11  % (20622)Memory used [KB]: 11769
% 5.11/1.11  % (20622)Time elapsed: 0.400 s
% 5.11/1.11  % (20622)------------------------------
% 5.11/1.11  % (20622)------------------------------
% 5.11/1.12  % (20617)Time limit reached!
% 5.11/1.12  % (20617)------------------------------
% 5.11/1.12  % (20617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.11/1.12  % (20617)Termination reason: Time limit
% 5.11/1.12  
% 5.11/1.12  % (20617)Memory used [KB]: 16119
% 5.11/1.12  % (20617)Time elapsed: 0.419 s
% 5.11/1.12  % (20617)------------------------------
% 5.11/1.12  % (20617)------------------------------
% 6.52/1.18  % (20612)Time limit reached!
% 6.52/1.18  % (20612)------------------------------
% 6.52/1.18  % (20612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.52/1.18  % (20612)Termination reason: Time limit
% 6.52/1.18  
% 6.52/1.18  % (20612)Memory used [KB]: 13816
% 6.52/1.18  % (20612)Time elapsed: 0.510 s
% 6.52/1.18  % (20612)------------------------------
% 6.52/1.18  % (20612)------------------------------
% 8.88/1.49  % (20451)Refutation found. Thanks to Tanya!
% 8.88/1.49  % SZS status Theorem for theBenchmark
% 8.88/1.49  % SZS output start Proof for theBenchmark
% 8.88/1.49  fof(f7290,plain,(
% 8.88/1.49    $false),
% 8.88/1.49    inference(subsumption_resolution,[],[f7277,f36])).
% 8.88/1.49  fof(f36,plain,(
% 8.88/1.49    ~r2_hidden(sK0,sK2)),
% 8.88/1.49    inference(cnf_transformation,[],[f30])).
% 8.88/1.49  fof(f30,plain,(
% 8.88/1.49    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 8.88/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).
% 8.88/1.49  fof(f29,plain,(
% 8.88/1.49    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 8.88/1.49    introduced(choice_axiom,[])).
% 8.88/1.49  fof(f28,plain,(
% 8.88/1.49    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 8.88/1.49    inference(ennf_transformation,[],[f25])).
% 8.88/1.49  fof(f25,negated_conjecture,(
% 8.88/1.49    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 8.88/1.49    inference(negated_conjecture,[],[f24])).
% 8.88/1.49  fof(f24,conjecture,(
% 8.88/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 8.88/1.49  fof(f7277,plain,(
% 8.88/1.49    r2_hidden(sK0,sK2)),
% 8.88/1.49    inference(superposition,[],[f71,f7272])).
% 8.88/1.49  fof(f7272,plain,(
% 8.88/1.49    sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 8.88/1.49    inference(subsumption_resolution,[],[f7120,f41])).
% 8.88/1.49  fof(f41,plain,(
% 8.88/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 8.88/1.49    inference(cnf_transformation,[],[f6])).
% 8.88/1.49  fof(f6,axiom,(
% 8.88/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 8.88/1.49  fof(f7120,plain,(
% 8.88/1.49    ~r1_tarski(sK2,k2_xboole_0(sK2,k2_tarski(sK0,sK1))) | sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 8.88/1.49    inference(backward_demodulation,[],[f77,f6937])).
% 8.88/1.49  fof(f6937,plain,(
% 8.88/1.49    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 8.88/1.49    inference(superposition,[],[f6115,f44])).
% 8.88/1.49  fof(f44,plain,(
% 8.88/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 8.88/1.49    inference(cnf_transformation,[],[f22])).
% 8.88/1.49  fof(f22,axiom,(
% 8.88/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 8.88/1.49  fof(f6115,plain,(
% 8.88/1.49    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 8.88/1.49    inference(superposition,[],[f44,f6103])).
% 8.88/1.49  fof(f6103,plain,(
% 8.88/1.49    ( ! [X4,X5] : (k2_tarski(X4,X5) = k2_tarski(X5,X4)) )),
% 8.88/1.49    inference(subsumption_resolution,[],[f6102,f70])).
% 8.88/1.49  fof(f70,plain,(
% 8.88/1.49    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 8.88/1.49    inference(resolution,[],[f52,f64])).
% 8.88/1.49  fof(f64,plain,(
% 8.88/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.88/1.49    inference(equality_resolution,[],[f48])).
% 8.88/1.49  fof(f48,plain,(
% 8.88/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 8.88/1.49    inference(cnf_transformation,[],[f32])).
% 8.88/1.49  fof(f32,plain,(
% 8.88/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.88/1.49    inference(flattening,[],[f31])).
% 8.88/1.49  fof(f31,plain,(
% 8.88/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.88/1.49    inference(nnf_transformation,[],[f4])).
% 8.88/1.49  fof(f4,axiom,(
% 8.88/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 8.88/1.49  fof(f52,plain,(
% 8.88/1.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 8.88/1.49    inference(cnf_transformation,[],[f34])).
% 8.88/1.49  fof(f34,plain,(
% 8.88/1.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 8.88/1.49    inference(flattening,[],[f33])).
% 8.88/1.49  fof(f33,plain,(
% 8.88/1.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 8.88/1.49    inference(nnf_transformation,[],[f23])).
% 8.88/1.49  fof(f23,axiom,(
% 8.88/1.49    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 8.88/1.49  fof(f6102,plain,(
% 8.88/1.49    ( ! [X4,X5] : (k2_tarski(X4,X5) = k2_tarski(X5,X4) | ~r2_hidden(X5,k2_tarski(X5,X4))) )),
% 8.88/1.49    inference(subsumption_resolution,[],[f6098,f74])).
% 8.88/1.49  fof(f74,plain,(
% 8.88/1.49    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 8.88/1.49    inference(resolution,[],[f53,f64])).
% 8.88/1.49  fof(f53,plain,(
% 8.88/1.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2)) )),
% 8.88/1.49    inference(cnf_transformation,[],[f34])).
% 8.88/1.49  fof(f6098,plain,(
% 8.88/1.49    ( ! [X4,X5] : (~r2_hidden(X4,k2_tarski(X5,X4)) | k2_tarski(X4,X5) = k2_tarski(X5,X4) | ~r2_hidden(X5,k2_tarski(X5,X4))) )),
% 8.88/1.49    inference(resolution,[],[f6075,f124])).
% 8.88/1.49  fof(f124,plain,(
% 8.88/1.49    ( ! [X6,X8,X7] : (~r1_tarski(X7,k2_tarski(X8,X6)) | ~r2_hidden(X8,X7) | k2_tarski(X8,X6) = X7 | ~r2_hidden(X6,X7)) )),
% 8.88/1.49    inference(resolution,[],[f54,f49])).
% 8.88/1.49  fof(f49,plain,(
% 8.88/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 8.88/1.49    inference(cnf_transformation,[],[f32])).
% 8.88/1.49  fof(f54,plain,(
% 8.88/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 8.88/1.49    inference(cnf_transformation,[],[f34])).
% 8.88/1.49  fof(f6075,plain,(
% 8.88/1.49    ( ! [X2,X3] : (r1_tarski(k2_tarski(X2,X3),k2_tarski(X3,X2))) )),
% 8.88/1.49    inference(backward_demodulation,[],[f6051,f6067])).
% 8.88/1.49  fof(f6067,plain,(
% 8.88/1.49    ( ! [X4,X5] : (k1_enumset1(X4,X5,X5) = k2_tarski(X5,X4)) )),
% 8.88/1.49    inference(subsumption_resolution,[],[f6062,f6047])).
% 8.88/1.49  fof(f6047,plain,(
% 8.88/1.49    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X1,X0,X0),k2_tarski(X0,X1))) )),
% 8.88/1.49    inference(superposition,[],[f6039,f45])).
% 8.88/1.49  fof(f45,plain,(
% 8.88/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 8.88/1.49    inference(cnf_transformation,[],[f16])).
% 8.88/1.49  fof(f16,axiom,(
% 8.88/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 8.88/1.49  fof(f6039,plain,(
% 8.88/1.49    ( ! [X28,X29,X27] : (r1_tarski(k1_enumset1(X27,X28,X29),k1_enumset1(X29,X28,X27))) )),
% 8.88/1.49    inference(superposition,[],[f1045,f3041])).
% 8.88/1.49  fof(f3041,plain,(
% 8.88/1.49    ( ! [X6,X8,X7] : (k1_enumset1(X6,X7,X8) = k5_enumset1(X8,X7,X6,X6,X8,X7,X6)) )),
% 8.88/1.49    inference(forward_demodulation,[],[f3037,f50])).
% 8.88/1.49  fof(f50,plain,(
% 8.88/1.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 8.88/1.49    inference(cnf_transformation,[],[f17])).
% 8.88/1.49  fof(f17,axiom,(
% 8.88/1.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 8.88/1.49  fof(f3037,plain,(
% 8.88/1.49    ( ! [X6,X8,X7] : (k2_enumset1(X6,X6,X7,X8) = k5_enumset1(X8,X7,X6,X6,X8,X7,X6)) )),
% 8.88/1.49    inference(superposition,[],[f2714,f187])).
% 8.88/1.49  fof(f187,plain,(
% 8.88/1.49    ( ! [X10,X8,X11,X9] : (k2_enumset1(X8,X9,X10,X11) = k6_enumset1(X8,X9,X10,X11,X8,X9,X10,X11)) )),
% 8.88/1.49    inference(superposition,[],[f61,f40])).
% 8.88/1.49  fof(f40,plain,(
% 8.88/1.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 8.88/1.49    inference(cnf_transformation,[],[f27])).
% 8.88/1.49  fof(f27,plain,(
% 8.88/1.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 8.88/1.49    inference(rectify,[],[f2])).
% 8.88/1.49  fof(f2,axiom,(
% 8.88/1.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 8.88/1.49  fof(f61,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 8.88/1.49    inference(cnf_transformation,[],[f10])).
% 8.88/1.49  fof(f10,axiom,(
% 8.88/1.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 8.88/1.49  fof(f2714,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k5_enumset1(X6,X5,X4,X3,X2,X1,X0)) )),
% 8.88/1.49    inference(backward_demodulation,[],[f184,f2711])).
% 8.88/1.49  fof(f2711,plain,(
% 8.88/1.49    ( ! [X28,X26,X24,X23,X29,X27,X25] : (k2_xboole_0(k2_enumset1(X29,X28,X27,X26),k1_enumset1(X25,X24,X23)) = k5_enumset1(X26,X27,X28,X29,X23,X24,X25)) )),
% 8.88/1.49    inference(backward_demodulation,[],[f2028,f2710])).
% 8.88/1.49  fof(f2710,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X6,X0) = k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0)) )),
% 8.88/1.49    inference(forward_demodulation,[],[f2700,f60])).
% 8.88/1.49  fof(f60,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 8.88/1.49    inference(cnf_transformation,[],[f14])).
% 8.88/1.49  fof(f14,axiom,(
% 8.88/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).
% 8.88/1.49  fof(f2700,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) )),
% 8.88/1.49    inference(superposition,[],[f248,f38])).
% 8.88/1.49  fof(f38,plain,(
% 8.88/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 8.88/1.49    inference(cnf_transformation,[],[f15])).
% 8.88/1.49  fof(f15,axiom,(
% 8.88/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 8.88/1.49  fof(f248,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 8.88/1.49    inference(forward_demodulation,[],[f244,f221])).
% 8.88/1.49  fof(f221,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 8.88/1.49    inference(forward_demodulation,[],[f215,f61])).
% 8.88/1.49  fof(f215,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 8.88/1.49    inference(superposition,[],[f62,f56])).
% 8.88/1.49  fof(f56,plain,(
% 8.88/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 8.88/1.49    inference(cnf_transformation,[],[f18])).
% 8.88/1.49  fof(f18,axiom,(
% 8.88/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 8.88/1.49  fof(f62,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 8.88/1.49    inference(cnf_transformation,[],[f12])).
% 8.88/1.49  fof(f12,axiom,(
% 8.88/1.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).
% 8.88/1.49  fof(f244,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 8.88/1.49    inference(superposition,[],[f63,f58])).
% 8.88/1.49  fof(f58,plain,(
% 8.88/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 8.88/1.49    inference(cnf_transformation,[],[f20])).
% 8.88/1.49  fof(f20,axiom,(
% 8.88/1.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 8.88/1.49  fof(f63,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) )),
% 8.88/1.49    inference(cnf_transformation,[],[f13])).
% 8.88/1.49  fof(f13,axiom,(
% 8.88/1.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).
% 8.88/1.49  fof(f2028,plain,(
% 8.88/1.49    ( ! [X28,X26,X24,X23,X29,X27,X25] : (k6_enumset1(X26,X27,X28,X29,X23,X24,X25,X25) = k2_xboole_0(k2_enumset1(X29,X28,X27,X26),k1_enumset1(X25,X24,X23))) )),
% 8.88/1.49    inference(superposition,[],[f182,f129])).
% 8.88/1.49  fof(f129,plain,(
% 8.88/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0)) )),
% 8.88/1.49    inference(superposition,[],[f55,f50])).
% 8.88/1.49  fof(f55,plain,(
% 8.88/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 8.88/1.49    inference(cnf_transformation,[],[f11])).
% 8.88/1.49  fof(f11,axiom,(
% 8.88/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 8.88/1.49  fof(f182,plain,(
% 8.88/1.49    ( ! [X14,X12,X10,X8,X7,X13,X11,X9] : (k6_enumset1(X7,X8,X9,X10,X11,X12,X13,X14) = k2_xboole_0(k2_enumset1(X10,X9,X8,X7),k2_enumset1(X11,X12,X13,X14))) )),
% 8.88/1.49    inference(superposition,[],[f61,f55])).
% 8.88/1.49  fof(f184,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2))) )),
% 8.88/1.49    inference(superposition,[],[f61,f50])).
% 8.88/1.49  fof(f1045,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 8.88/1.49    inference(forward_demodulation,[],[f1039,f59])).
% 8.88/1.49  fof(f59,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 8.88/1.49    inference(cnf_transformation,[],[f21])).
% 8.88/1.49  fof(f21,axiom,(
% 8.88/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 8.88/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 8.88/1.49  fof(f1039,plain,(
% 8.88/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) )),
% 8.88/1.49    inference(superposition,[],[f190,f50])).
% 8.88/1.49  fof(f190,plain,(
% 8.88/1.49    ( ! [X14,X12,X19,X17,X15,X13,X18,X16] : (r1_tarski(k2_enumset1(X12,X13,X14,X15),k6_enumset1(X12,X13,X14,X15,X16,X17,X18,X19))) )),
% 8.88/1.49    inference(superposition,[],[f41,f61])).
% 8.88/1.49  fof(f6062,plain,(
% 8.88/1.49    ( ! [X4,X5] : (k1_enumset1(X4,X5,X5) = k2_tarski(X5,X4) | ~r1_tarski(k1_enumset1(X4,X5,X5),k2_tarski(X5,X4))) )),
% 8.88/1.49    inference(resolution,[],[f6044,f49])).
% 8.88/1.49  fof(f6044,plain,(
% 8.88/1.49    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X1),k1_enumset1(X1,X0,X0))) )),
% 8.88/1.49    inference(superposition,[],[f6039,f45])).
% 8.88/1.49  fof(f6051,plain,(
% 8.88/1.49    ( ! [X2,X3] : (r1_tarski(k1_enumset1(X3,X2,X2),k2_tarski(X3,X2))) )),
% 8.88/1.49    inference(forward_demodulation,[],[f6045,f45])).
% 8.88/1.49  fof(f6045,plain,(
% 8.88/1.49    ( ! [X2,X3] : (r1_tarski(k1_enumset1(X3,X2,X2),k1_enumset1(X3,X3,X2))) )),
% 8.88/1.49    inference(superposition,[],[f6039,f299])).
% 8.88/1.49  fof(f299,plain,(
% 8.88/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X0,X0)) )),
% 8.88/1.49    inference(superposition,[],[f129,f50])).
% 8.88/1.49  fof(f77,plain,(
% 8.88/1.49    ~r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2)) | sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 8.88/1.49    inference(resolution,[],[f49,f35])).
% 8.88/1.49  fof(f35,plain,(
% 8.88/1.49    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 8.88/1.49    inference(cnf_transformation,[],[f30])).
% 8.88/1.49  fof(f71,plain,(
% 8.88/1.49    ( ! [X4,X2,X3] : (r2_hidden(X2,k2_xboole_0(k2_tarski(X2,X3),X4))) )),
% 8.88/1.49    inference(resolution,[],[f52,f41])).
% 8.88/1.49  % SZS output end Proof for theBenchmark
% 8.88/1.49  % (20451)------------------------------
% 8.88/1.49  % (20451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.88/1.49  % (20451)Termination reason: Refutation
% 8.88/1.49  
% 8.88/1.49  % (20451)Memory used [KB]: 21492
% 8.88/1.49  % (20451)Time elapsed: 1.106 s
% 8.88/1.49  % (20451)------------------------------
% 8.88/1.49  % (20451)------------------------------
% 8.88/1.49  % (20441)Success in time 1.127 s
%------------------------------------------------------------------------------
