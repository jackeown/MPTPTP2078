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
% DateTime   : Thu Dec  3 12:35:28 EST 2020

% Result     : Theorem 16.34s
% Output     : Refutation 16.67s
% Verified   : 
% Statistics : Number of formulae       :   96 (2027 expanded)
%              Number of leaves         :   17 ( 750 expanded)
%              Depth                    :   21
%              Number of atoms          :  120 (2062 expanded)
%              Number of equality atoms :  100 (2040 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9905,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9895,f91])).

fof(f91,plain,(
    ~ r2_hidden(sK1,k2_tarski(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f30,f82])).

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f30,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f9895,plain,(
    r2_hidden(sK1,k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f5200,f1818])).

fof(f1818,plain,(
    k2_tarski(sK0,sK0) = k5_enumset1(sK0,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[],[f472,f69])).

fof(f69,plain,(
    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0))) ),
    inference(definition_unfolding,[],[f29,f42,f37,f42,f42])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f29,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f472,plain,(
    ! [X6,X4,X5] : k5_enumset1(X6,X4,X4,X4,X4,X4,X5) = k5_xboole_0(k2_tarski(X6,X6),k4_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X6))) ),
    inference(superposition,[],[f216,f147])).

fof(f147,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(superposition,[],[f77,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X0),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f55,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f77,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f61,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f216,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k2_tarski(X0,X0))) ),
    inference(forward_demodulation,[],[f215,f67])).

fof(f215,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))),k4_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))))) ),
    inference(forward_demodulation,[],[f201,f170])).

fof(f170,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))))) ),
    inference(superposition,[],[f68,f77])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f34,f37,f63,f63])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f201,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))),k4_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))))) ),
    inference(superposition,[],[f70,f77])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k4_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))))) ),
    inference(definition_unfolding,[],[f32,f65,f37,f61,f46])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4))) ),
    inference(definition_unfolding,[],[f31,f37,f62,f63])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_enumset1)).

fof(f5200,plain,(
    ! [X23,X21,X22] : r2_hidden(X23,k5_enumset1(X21,X22,X23,X23,X23,X23,X22)) ),
    inference(forward_demodulation,[],[f5150,f3106])).

fof(f3106,plain,(
    ! [X269,X265,X267,X268,X270,X266] : k5_xboole_0(k2_tarski(X270,X270),k4_xboole_0(k5_enumset1(X265,X266,X267,X267,X267,X268,X269),k2_tarski(X270,X270))) = k5_enumset1(X270,X265,X266,X267,X267,X268,X269) ),
    inference(backward_demodulation,[],[f1575,f3104])).

fof(f3104,plain,(
    ! [X288,X285,X287,X289,X284,X286] : k5_xboole_0(k2_tarski(X289,X284),k4_xboole_0(k5_enumset1(X285,X285,X285,X286,X286,X287,X288),k2_tarski(X289,X284))) = k5_enumset1(X289,X284,X285,X286,X286,X287,X288) ),
    inference(forward_demodulation,[],[f3103,f216])).

fof(f3103,plain,(
    ! [X288,X285,X287,X289,X284,X286] : k5_xboole_0(k2_tarski(X289,X284),k4_xboole_0(k5_enumset1(X285,X285,X285,X286,X286,X287,X288),k2_tarski(X289,X284))) = k5_xboole_0(k2_tarski(X289,X289),k4_xboole_0(k5_enumset1(X284,X284,X285,X286,X286,X287,X288),k2_tarski(X289,X289))) ),
    inference(forward_demodulation,[],[f3079,f552])).

fof(f552,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k5_enumset1(X4,X0,X0,X0,X0,X1,X2),k2_tarski(X3,X3))) = k5_enumset1(X3,X3,X4,X0,X0,X1,X2) ),
    inference(backward_demodulation,[],[f498,f542])).

fof(f542,plain,(
    ! [X6,X10,X8,X7,X9] : k5_enumset1(X6,X6,X7,X8,X8,X9,X10) = k5_xboole_0(k2_tarski(X6,X7),k4_xboole_0(k5_xboole_0(k2_tarski(X9,X8),k4_xboole_0(k2_tarski(X10,X8),k2_tarski(X9,X8))),k2_tarski(X6,X7))) ),
    inference(superposition,[],[f169,f147])).

fof(f169,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X4,X5),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X3,X3,X4,X5))) ),
    inference(superposition,[],[f68,f77])).

fof(f498,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k5_enumset1(X4,X0,X0,X0,X0,X1,X2),k2_tarski(X3,X3))) = k5_xboole_0(k2_tarski(X3,X4),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k2_tarski(X3,X4))) ),
    inference(superposition,[],[f218,f77])).

fof(f218,plain,(
    ! [X14,X12,X10,X8,X7,X13,X11,X9] : k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k5_enumset1(X8,X9,X10,X11,X12,X13,X14),k2_tarski(X7,X7))) = k5_xboole_0(k2_tarski(X7,X8),k4_xboole_0(k5_enumset1(X9,X9,X10,X11,X12,X13,X14),k2_tarski(X7,X8))) ),
    inference(forward_demodulation,[],[f203,f67])).

fof(f203,plain,(
    ! [X14,X12,X10,X8,X7,X13,X11,X9] : k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k5_enumset1(X8,X9,X10,X11,X12,X13,X14),k2_tarski(X7,X7))) = k5_xboole_0(k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k2_tarski(X8,X7),k2_tarski(X7,X7))),k4_xboole_0(k5_enumset1(X9,X9,X10,X11,X12,X13,X14),k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k2_tarski(X8,X7),k2_tarski(X7,X7))))) ),
    inference(superposition,[],[f70,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f35,f64,f37,f42])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(f3079,plain,(
    ! [X288,X285,X287,X289,X284,X286] : k5_xboole_0(k2_tarski(X289,X284),k4_xboole_0(k5_enumset1(X285,X285,X285,X286,X286,X287,X288),k2_tarski(X289,X284))) = k5_xboole_0(k2_tarski(X289,X289),k4_xboole_0(k5_xboole_0(k2_tarski(X284,X284),k4_xboole_0(k5_enumset1(X285,X286,X286,X286,X286,X287,X288),k2_tarski(X284,X284))),k2_tarski(X289,X289))) ),
    inference(superposition,[],[f218,f930])).

fof(f930,plain,(
    ! [X6,X10,X8,X7,X9] : k5_xboole_0(k2_tarski(X6,X6),k4_xboole_0(k5_enumset1(X7,X8,X8,X8,X8,X9,X10),k2_tarski(X6,X6))) = k5_enumset1(X6,X7,X7,X8,X8,X9,X10) ),
    inference(forward_demodulation,[],[f905,f216])).

fof(f905,plain,(
    ! [X6,X10,X8,X7,X9] : k5_enumset1(X6,X7,X7,X8,X8,X9,X10) = k5_xboole_0(k2_tarski(X6,X6),k4_xboole_0(k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X9,X10),k2_tarski(X7,X7))),k2_tarski(X6,X6))) ),
    inference(superposition,[],[f183,f548])).

fof(f548,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_enumset1(X3,X3,X3,X4,X0,X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X4,X0,X0,X0))) = k5_enumset1(X3,X4,X4,X0,X0,X1,X2) ),
    inference(backward_demodulation,[],[f187,f547])).

fof(f547,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k2_tarski(X4,X4),k4_xboole_0(k5_xboole_0(k2_tarski(X3,X5),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k2_tarski(X3,X5))),k2_tarski(X4,X4))) = k5_enumset1(X4,X3,X5,X0,X0,X1,X2) ),
    inference(backward_demodulation,[],[f523,f541])).

fof(f541,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k4_xboole_0(k5_xboole_0(k2_tarski(X4,X3),k4_xboole_0(k2_tarski(X5,X3),k2_tarski(X4,X3))),k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))))) ),
    inference(superposition,[],[f169,f77])).

fof(f523,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k2_tarski(X3,X4),k4_xboole_0(k2_tarski(X5,X4),k2_tarski(X3,X4))),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_xboole_0(k2_tarski(X3,X4),k4_xboole_0(k2_tarski(X5,X4),k2_tarski(X3,X4))))) = k5_xboole_0(k2_tarski(X4,X4),k4_xboole_0(k5_xboole_0(k2_tarski(X3,X5),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k2_tarski(X3,X5))),k2_tarski(X4,X4))) ),
    inference(superposition,[],[f513,f77])).

fof(f513,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k4_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k2_tarski(X1,X2))),k2_tarski(X0,X0))) ),
    inference(backward_demodulation,[],[f70,f502])).

fof(f502,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X8,X8,X8,X0,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X0,X1,X2,X3))) = k5_xboole_0(k2_tarski(X8,X8),k4_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k5_enumset1(X2,X2,X3,X4,X5,X6,X7),k2_tarski(X0,X1))),k2_tarski(X8,X8))) ),
    inference(superposition,[],[f90,f218])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k2_tarski(X1,X1))),k2_tarski(X0,X0))) ),
    inference(backward_demodulation,[],[f71,f72])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4))),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f33,f65,f37,f42,f64])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

fof(f187,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_enumset1(X3,X3,X3,X4,X0,X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X4,X0,X0,X0))) = k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k5_xboole_0(k2_tarski(X4,X4),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k2_tarski(X4,X4))),k2_tarski(X3,X3))) ),
    inference(superposition,[],[f90,f77])).

fof(f183,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k5_xboole_0(k2_tarski(X4,X4),k4_xboole_0(k5_enumset1(X5,X6,X7,X0,X0,X1,X2),k2_tarski(X4,X4))),k2_tarski(X3,X3))) = k5_xboole_0(k5_enumset1(X3,X3,X3,X4,X5,X6,X7),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X4,X5,X6,X7))) ),
    inference(superposition,[],[f90,f77])).

fof(f1575,plain,(
    ! [X269,X265,X267,X268,X270,X266] : k5_xboole_0(k2_tarski(X270,X265),k4_xboole_0(k5_enumset1(X266,X266,X266,X267,X267,X268,X269),k2_tarski(X270,X265))) = k5_xboole_0(k2_tarski(X270,X270),k4_xboole_0(k5_enumset1(X265,X266,X267,X267,X267,X268,X269),k2_tarski(X270,X270))) ),
    inference(superposition,[],[f218,f572])).

fof(f572,plain,(
    ! [X6,X4,X8,X7,X5] : k5_enumset1(X4,X5,X5,X6,X6,X7,X8) = k5_enumset1(X4,X5,X6,X6,X6,X7,X8) ),
    inference(superposition,[],[f549,f548])).

fof(f549,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k5_xboole_0(k5_enumset1(X3,X3,X3,X4,X5,X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X4,X5,X0,X0))) ),
    inference(backward_demodulation,[],[f531,f547])).

fof(f531,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X3,X3,X3,X4,X5,X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X4,X5,X0,X0))) = k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k5_xboole_0(k2_tarski(X4,X5),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k2_tarski(X4,X5))),k2_tarski(X3,X3))) ),
    inference(backward_demodulation,[],[f205,f523])).

fof(f205,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X3,X3,X3,X4,X5,X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X4,X5,X0,X0))) = k5_xboole_0(k5_xboole_0(k2_tarski(X4,X3),k4_xboole_0(k2_tarski(X5,X3),k2_tarski(X4,X3))),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_xboole_0(k2_tarski(X4,X3),k4_xboole_0(k2_tarski(X5,X3),k2_tarski(X4,X3))))) ),
    inference(superposition,[],[f70,f77])).

fof(f5150,plain,(
    ! [X23,X21,X22] : r2_hidden(X23,k5_xboole_0(k2_tarski(X21,X21),k4_xboole_0(k5_enumset1(X22,X23,X23,X23,X23,X23,X22),k2_tarski(X21,X21)))) ),
    inference(superposition,[],[f133,f499])).

fof(f499,plain,(
    ! [X6,X8,X7,X5] : k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k5_enumset1(X8,X5,X5,X5,X5,X5,X6),k2_tarski(X7,X7))) = k5_xboole_0(k2_tarski(X7,X8),k4_xboole_0(k2_tarski(X5,X6),k2_tarski(X7,X8))) ),
    inference(superposition,[],[f218,f147])).

fof(f133,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X2)))) ),
    inference(unit_resulting_resolution,[],[f87,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))))
      | ~ sP4(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) != X3 ) ),
    inference(definition_unfolding,[],[f51,f61])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f87,plain,(
    ! [X4,X0,X1] : sP4(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP4(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:07:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (18804)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.51  % (18783)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (18806)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (18789)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (18800)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (18808)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % (18787)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (18786)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (18809)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (18792)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.23/0.54  % (18803)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.23/0.54  % (18790)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.23/0.54  % (18810)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.23/0.54  % (18805)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.23/0.54  % (18807)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.23/0.54  % (18801)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.23/0.54  % (18797)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.54  % (18801)Refutation not found, incomplete strategy% (18801)------------------------------
% 1.23/0.54  % (18801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (18801)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (18801)Memory used [KB]: 1663
% 1.23/0.54  % (18801)Time elapsed: 0.135 s
% 1.23/0.54  % (18801)------------------------------
% 1.23/0.54  % (18801)------------------------------
% 1.23/0.54  % (18811)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.23/0.55  % (18797)Refutation not found, incomplete strategy% (18797)------------------------------
% 1.23/0.55  % (18797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.55  % (18797)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.55  
% 1.23/0.55  % (18797)Memory used [KB]: 1791
% 1.23/0.55  % (18797)Time elapsed: 0.131 s
% 1.23/0.55  % (18797)------------------------------
% 1.23/0.55  % (18797)------------------------------
% 1.23/0.55  % (18785)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.23/0.55  % (18793)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.23/0.55  % (18809)Refutation not found, incomplete strategy% (18809)------------------------------
% 1.23/0.55  % (18809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.55  % (18791)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.23/0.55  % (18809)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.55  
% 1.23/0.55  % (18795)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.23/0.55  % (18809)Memory used [KB]: 6140
% 1.23/0.55  % (18809)Time elapsed: 0.141 s
% 1.23/0.55  % (18809)------------------------------
% 1.23/0.55  % (18809)------------------------------
% 1.23/0.55  % (18795)Refutation not found, incomplete strategy% (18795)------------------------------
% 1.23/0.55  % (18795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.55  % (18795)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.55  
% 1.23/0.55  % (18795)Memory used [KB]: 10618
% 1.23/0.55  % (18795)Time elapsed: 0.148 s
% 1.23/0.55  % (18795)------------------------------
% 1.23/0.55  % (18795)------------------------------
% 1.23/0.55  % (18794)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.23/0.55  % (18784)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.55  % (18812)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.23/0.55  % (18784)Refutation not found, incomplete strategy% (18784)------------------------------
% 1.23/0.55  % (18784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.55  % (18784)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.55  
% 1.23/0.55  % (18784)Memory used [KB]: 1663
% 1.23/0.55  % (18784)Time elapsed: 0.140 s
% 1.23/0.55  % (18784)------------------------------
% 1.23/0.55  % (18784)------------------------------
% 1.23/0.55  % (18812)Refutation not found, incomplete strategy% (18812)------------------------------
% 1.23/0.55  % (18812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.55  % (18812)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.55  
% 1.23/0.55  % (18812)Memory used [KB]: 1663
% 1.23/0.55  % (18812)Time elapsed: 0.002 s
% 1.23/0.55  % (18812)------------------------------
% 1.23/0.55  % (18812)------------------------------
% 1.23/0.55  % (18798)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.23/0.55  % (18796)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.46/0.56  % (18802)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.46/0.56  % (18799)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.46/0.56  % (18788)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.46/0.58  % (18799)Refutation not found, incomplete strategy% (18799)------------------------------
% 1.46/0.58  % (18799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (18799)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.58  
% 1.46/0.58  % (18799)Memory used [KB]: 10618
% 1.46/0.58  % (18799)Time elapsed: 0.175 s
% 1.46/0.58  % (18799)------------------------------
% 1.46/0.58  % (18799)------------------------------
% 1.46/0.62  % (18783)Refutation not found, incomplete strategy% (18783)------------------------------
% 1.46/0.62  % (18783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.62  % (18783)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.62  
% 1.46/0.62  % (18783)Memory used [KB]: 1663
% 1.46/0.62  % (18783)Time elapsed: 0.181 s
% 1.46/0.62  % (18783)------------------------------
% 1.46/0.62  % (18783)------------------------------
% 1.99/0.65  % (18814)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.99/0.66  % (18817)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 1.99/0.67  % (18816)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.22/0.68  % (18786)Refutation not found, incomplete strategy% (18786)------------------------------
% 2.22/0.68  % (18786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.68  % (18786)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.68  
% 2.22/0.68  % (18786)Memory used [KB]: 6140
% 2.22/0.68  % (18786)Time elapsed: 0.247 s
% 2.22/0.68  % (18786)------------------------------
% 2.22/0.68  % (18786)------------------------------
% 2.22/0.68  % (18818)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.22/0.68  % (18791)Refutation not found, incomplete strategy% (18791)------------------------------
% 2.22/0.68  % (18791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.69  % (18815)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.22/0.69  % (18813)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.22/0.69  % (18816)Refutation not found, incomplete strategy% (18816)------------------------------
% 2.22/0.69  % (18816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.69  % (18816)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.69  
% 2.22/0.69  % (18816)Memory used [KB]: 10746
% 2.22/0.69  % (18816)Time elapsed: 0.106 s
% 2.22/0.69  % (18816)------------------------------
% 2.22/0.69  % (18816)------------------------------
% 2.22/0.70  % (18791)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.70  
% 2.22/0.70  % (18791)Memory used [KB]: 6140
% 2.22/0.70  % (18791)Time elapsed: 0.279 s
% 2.22/0.70  % (18791)------------------------------
% 2.22/0.70  % (18791)------------------------------
% 2.22/0.70  % (18798)Refutation not found, incomplete strategy% (18798)------------------------------
% 2.22/0.70  % (18798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.70  % (18798)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.70  
% 2.22/0.70  % (18798)Memory used [KB]: 6140
% 2.22/0.70  % (18798)Time elapsed: 0.274 s
% 2.22/0.70  % (18798)------------------------------
% 2.22/0.70  % (18798)------------------------------
% 2.22/0.71  % (18815)Refutation not found, incomplete strategy% (18815)------------------------------
% 2.22/0.71  % (18815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.71  % (18815)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.71  
% 2.22/0.71  % (18815)Memory used [KB]: 6140
% 2.22/0.71  % (18815)Time elapsed: 0.132 s
% 2.22/0.71  % (18815)------------------------------
% 2.22/0.71  % (18815)------------------------------
% 2.22/0.71  % (18827)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.22/0.73  % (18843)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.74/0.79  % (18871)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.74/0.81  % (18878)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.03/0.82  % (18876)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.03/0.82  % (18876)Refutation not found, incomplete strategy% (18876)------------------------------
% 3.03/0.82  % (18876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.03/0.82  % (18876)Termination reason: Refutation not found, incomplete strategy
% 3.03/0.82  
% 3.03/0.82  % (18876)Memory used [KB]: 10746
% 3.03/0.82  % (18876)Time elapsed: 0.109 s
% 3.03/0.82  % (18876)------------------------------
% 3.03/0.82  % (18876)------------------------------
% 3.03/0.82  % (18785)Time limit reached!
% 3.03/0.82  % (18785)------------------------------
% 3.03/0.82  % (18785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.03/0.82  % (18785)Termination reason: Time limit
% 3.03/0.82  % (18785)Termination phase: Saturation
% 3.03/0.82  
% 3.03/0.82  % (18785)Memory used [KB]: 7291
% 3.03/0.82  % (18785)Time elapsed: 0.400 s
% 3.03/0.82  % (18785)------------------------------
% 3.03/0.82  % (18785)------------------------------
% 3.03/0.83  % (18882)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 3.03/0.85  % (18880)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 3.03/0.85  % (18807)Time limit reached!
% 3.03/0.85  % (18807)------------------------------
% 3.03/0.85  % (18807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.03/0.85  % (18807)Termination reason: Time limit
% 3.03/0.85  % (18807)Termination phase: Saturation
% 3.03/0.85  
% 3.03/0.85  % (18807)Memory used [KB]: 13048
% 3.03/0.85  % (18807)Time elapsed: 0.400 s
% 3.03/0.85  % (18807)------------------------------
% 3.03/0.85  % (18807)------------------------------
% 3.29/0.93  % (18961)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.66/0.94  % (18789)Time limit reached!
% 3.66/0.94  % (18789)------------------------------
% 3.66/0.94  % (18789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.94  % (18789)Termination reason: Time limit
% 3.66/0.94  % (18789)Termination phase: Saturation
% 3.66/0.94  
% 3.66/0.94  % (18789)Memory used [KB]: 16119
% 3.66/0.94  % (18789)Time elapsed: 0.500 s
% 3.66/0.94  % (18789)------------------------------
% 3.66/0.94  % (18789)------------------------------
% 3.66/0.94  % (18957)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 3.66/0.94  % (18957)Refutation not found, incomplete strategy% (18957)------------------------------
% 3.66/0.94  % (18957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.94  % (18957)Termination reason: Refutation not found, incomplete strategy
% 3.66/0.94  
% 3.66/0.94  % (18957)Memory used [KB]: 10746
% 3.66/0.94  % (18957)Time elapsed: 0.083 s
% 3.66/0.94  % (18957)------------------------------
% 3.66/0.94  % (18957)------------------------------
% 3.66/0.98  % (18970)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 3.87/1.02  % (18790)Time limit reached!
% 3.87/1.02  % (18790)------------------------------
% 3.87/1.02  % (18790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/1.02  % (18790)Termination reason: Time limit
% 3.87/1.02  
% 3.87/1.02  % (18790)Memory used [KB]: 7419
% 3.87/1.02  % (18790)Time elapsed: 0.601 s
% 3.87/1.02  % (18790)------------------------------
% 3.87/1.02  % (18790)------------------------------
% 5.44/1.07  % (18993)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 5.44/1.08  % (18995)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 5.44/1.11  % (18970)Refutation not found, incomplete strategy% (18970)------------------------------
% 5.44/1.11  % (18970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.44/1.12  % (18970)Termination reason: Refutation not found, incomplete strategy
% 5.44/1.12  
% 5.44/1.12  % (18970)Memory used [KB]: 6140
% 5.44/1.12  % (18970)Time elapsed: 0.208 s
% 5.44/1.12  % (18970)------------------------------
% 5.44/1.12  % (18970)------------------------------
% 5.94/1.14  % (19012)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 6.27/1.23  % (18827)Time limit reached!
% 6.27/1.23  % (18827)------------------------------
% 6.27/1.23  % (18827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.27/1.24  % (18827)Termination reason: Time limit
% 6.27/1.24  % (18827)Termination phase: Saturation
% 6.27/1.24  
% 6.27/1.24  % (18827)Memory used [KB]: 16119
% 6.27/1.24  % (18827)Time elapsed: 0.600 s
% 6.27/1.24  % (18827)------------------------------
% 6.27/1.24  % (18827)------------------------------
% 6.82/1.26  % (19057)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 7.02/1.28  % (19012)Refutation not found, incomplete strategy% (19012)------------------------------
% 7.02/1.28  % (19012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.02/1.29  % (19012)Termination reason: Refutation not found, incomplete strategy
% 7.02/1.29  
% 7.02/1.29  % (19012)Memory used [KB]: 6140
% 7.02/1.29  % (19012)Time elapsed: 0.223 s
% 7.02/1.29  % (19012)------------------------------
% 7.02/1.29  % (19012)------------------------------
% 7.72/1.37  % (19062)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 7.72/1.38  % (18995)Time limit reached!
% 7.72/1.38  % (18995)------------------------------
% 7.72/1.38  % (18995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.72/1.40  % (18995)Termination reason: Time limit
% 7.72/1.40  
% 7.72/1.40  % (18995)Memory used [KB]: 9594
% 7.72/1.40  % (18995)Time elapsed: 0.403 s
% 7.72/1.40  % (18995)------------------------------
% 7.72/1.40  % (18995)------------------------------
% 7.72/1.42  % (18810)Time limit reached!
% 7.72/1.42  % (18810)------------------------------
% 7.72/1.42  % (18810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.72/1.42  % (18810)Termination reason: Time limit
% 7.72/1.42  
% 7.72/1.42  % (18810)Memory used [KB]: 9466
% 7.72/1.42  % (18810)Time elapsed: 1.012 s
% 7.72/1.42  % (18810)------------------------------
% 7.72/1.42  % (18810)------------------------------
% 8.50/1.53  % (18993)Time limit reached!
% 8.50/1.53  % (18993)------------------------------
% 8.50/1.53  % (18993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.50/1.53  % (18993)Termination reason: Time limit
% 8.50/1.53  
% 8.50/1.53  % (18993)Memory used [KB]: 14456
% 8.50/1.53  % (18993)Time elapsed: 0.543 s
% 8.50/1.53  % (18993)------------------------------
% 8.50/1.53  % (18993)------------------------------
% 9.31/1.59  % (19057)Time limit reached!
% 9.31/1.59  % (19057)------------------------------
% 9.31/1.59  % (19057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.31/1.59  % (19057)Termination reason: Time limit
% 9.31/1.59  
% 9.31/1.59  % (19057)Memory used [KB]: 2942
% 9.31/1.59  % (19057)Time elapsed: 0.420 s
% 9.31/1.59  % (19057)------------------------------
% 9.31/1.59  % (19057)------------------------------
% 10.31/1.68  % (19062)Time limit reached!
% 10.31/1.68  % (19062)------------------------------
% 10.31/1.68  % (19062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.31/1.68  % (19062)Termination reason: Time limit
% 10.31/1.68  % (19062)Termination phase: Saturation
% 10.31/1.68  
% 10.31/1.68  % (19062)Memory used [KB]: 8187
% 10.31/1.68  % (19062)Time elapsed: 0.400 s
% 10.31/1.68  % (19062)------------------------------
% 10.31/1.68  % (19062)------------------------------
% 10.87/1.76  % (18788)Time limit reached!
% 10.87/1.76  % (18788)------------------------------
% 10.87/1.76  % (18788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.87/1.76  % (18788)Termination reason: Time limit
% 10.87/1.76  % (18788)Termination phase: Saturation
% 10.87/1.76  
% 10.87/1.76  % (18788)Memory used [KB]: 10874
% 10.87/1.76  % (18788)Time elapsed: 1.300 s
% 10.87/1.76  % (18788)------------------------------
% 10.87/1.76  % (18788)------------------------------
% 14.88/2.24  % (18803)Time limit reached!
% 14.88/2.24  % (18803)------------------------------
% 14.88/2.24  % (18803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.88/2.24  % (18803)Termination reason: Time limit
% 14.88/2.24  % (18803)Termination phase: Saturation
% 14.88/2.24  
% 14.88/2.24  % (18803)Memory used [KB]: 25458
% 14.88/2.24  % (18803)Time elapsed: 1.800 s
% 14.88/2.24  % (18803)------------------------------
% 14.88/2.24  % (18803)------------------------------
% 16.34/2.45  % (18802)Refutation found. Thanks to Tanya!
% 16.34/2.45  % SZS status Theorem for theBenchmark
% 16.67/2.47  % SZS output start Proof for theBenchmark
% 16.67/2.47  fof(f9905,plain,(
% 16.67/2.47    $false),
% 16.67/2.47    inference(subsumption_resolution,[],[f9895,f91])).
% 16.67/2.47  fof(f91,plain,(
% 16.67/2.47    ~r2_hidden(sK1,k2_tarski(sK0,sK0))),
% 16.67/2.47    inference(unit_resulting_resolution,[],[f30,f82])).
% 16.67/2.47  fof(f82,plain,(
% 16.67/2.47    ( ! [X2,X0] : (~r2_hidden(X2,k2_tarski(X0,X0)) | X0 = X2) )),
% 16.67/2.47    inference(equality_resolution,[],[f75])).
% 16.67/2.47  fof(f75,plain,(
% 16.67/2.47    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_tarski(X0,X0) != X1) )),
% 16.67/2.47    inference(definition_unfolding,[],[f39,f42])).
% 16.67/2.47  fof(f42,plain,(
% 16.67/2.47    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 16.67/2.47    inference(cnf_transformation,[],[f18])).
% 16.67/2.47  fof(f18,axiom,(
% 16.67/2.47    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 16.67/2.47  fof(f39,plain,(
% 16.67/2.47    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 16.67/2.47    inference(cnf_transformation,[],[f11])).
% 16.67/2.47  fof(f11,axiom,(
% 16.67/2.47    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 16.67/2.47  fof(f30,plain,(
% 16.67/2.47    sK0 != sK1),
% 16.67/2.47    inference(cnf_transformation,[],[f27])).
% 16.67/2.47  fof(f27,plain,(
% 16.67/2.47    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 16.67/2.47    inference(ennf_transformation,[],[f26])).
% 16.67/2.47  fof(f26,negated_conjecture,(
% 16.67/2.47    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 16.67/2.47    inference(negated_conjecture,[],[f25])).
% 16.67/2.47  fof(f25,conjecture,(
% 16.67/2.47    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 16.67/2.47  fof(f9895,plain,(
% 16.67/2.47    r2_hidden(sK1,k2_tarski(sK0,sK0))),
% 16.67/2.47    inference(superposition,[],[f5200,f1818])).
% 16.67/2.47  fof(f1818,plain,(
% 16.67/2.47    k2_tarski(sK0,sK0) = k5_enumset1(sK0,sK1,sK1,sK1,sK1,sK1,sK1)),
% 16.67/2.47    inference(superposition,[],[f472,f69])).
% 16.67/2.47  fof(f69,plain,(
% 16.67/2.47    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0)))),
% 16.67/2.47    inference(definition_unfolding,[],[f29,f42,f37,f42,f42])).
% 16.67/2.47  fof(f37,plain,(
% 16.67/2.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 16.67/2.47    inference(cnf_transformation,[],[f9])).
% 16.67/2.47  fof(f9,axiom,(
% 16.67/2.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 16.67/2.47  fof(f29,plain,(
% 16.67/2.47    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 16.67/2.47    inference(cnf_transformation,[],[f27])).
% 16.67/2.47  fof(f472,plain,(
% 16.67/2.47    ( ! [X6,X4,X5] : (k5_enumset1(X6,X4,X4,X4,X4,X4,X5) = k5_xboole_0(k2_tarski(X6,X6),k4_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X6)))) )),
% 16.67/2.47    inference(superposition,[],[f216,f147])).
% 16.67/2.47  fof(f147,plain,(
% 16.67/2.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 16.67/2.47    inference(superposition,[],[f77,f67])).
% 16.67/2.47  fof(f67,plain,(
% 16.67/2.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X0),k2_tarski(X0,X0)))) )),
% 16.67/2.47    inference(definition_unfolding,[],[f55,f61])).
% 16.67/2.47  fof(f61,plain,(
% 16.67/2.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0)))) )),
% 16.67/2.47    inference(definition_unfolding,[],[f36,f37])).
% 16.67/2.47  fof(f36,plain,(
% 16.67/2.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))) )),
% 16.67/2.47    inference(cnf_transformation,[],[f16])).
% 16.67/2.47  fof(f16,axiom,(
% 16.67/2.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 16.67/2.47  fof(f55,plain,(
% 16.67/2.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 16.67/2.47    inference(cnf_transformation,[],[f19])).
% 16.67/2.47  fof(f19,axiom,(
% 16.67/2.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 16.67/2.47  fof(f77,plain,(
% 16.67/2.47    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 16.67/2.47    inference(definition_unfolding,[],[f44,f61,f63])).
% 16.67/2.47  fof(f63,plain,(
% 16.67/2.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 16.67/2.47    inference(definition_unfolding,[],[f43,f62])).
% 16.67/2.47  fof(f62,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 16.67/2.47    inference(definition_unfolding,[],[f45,f46])).
% 16.67/2.47  fof(f46,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 16.67/2.47    inference(cnf_transformation,[],[f23])).
% 16.67/2.47  fof(f23,axiom,(
% 16.67/2.47    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 16.67/2.47  fof(f45,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 16.67/2.47    inference(cnf_transformation,[],[f22])).
% 16.67/2.47  fof(f22,axiom,(
% 16.67/2.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 16.67/2.47  fof(f43,plain,(
% 16.67/2.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 16.67/2.47    inference(cnf_transformation,[],[f21])).
% 16.67/2.47  fof(f21,axiom,(
% 16.67/2.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 16.67/2.47  fof(f44,plain,(
% 16.67/2.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 16.67/2.47    inference(cnf_transformation,[],[f20])).
% 16.67/2.47  fof(f20,axiom,(
% 16.67/2.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 16.67/2.47  fof(f216,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k2_tarski(X0,X0)))) )),
% 16.67/2.47    inference(forward_demodulation,[],[f215,f67])).
% 16.67/2.47  fof(f215,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))),k4_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)))))) )),
% 16.67/2.47    inference(forward_demodulation,[],[f201,f170])).
% 16.67/2.47  fof(f170,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0)))))) )),
% 16.67/2.47    inference(superposition,[],[f68,f77])).
% 16.67/2.47  fof(f68,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) )),
% 16.67/2.47    inference(definition_unfolding,[],[f56,f64])).
% 16.67/2.47  fof(f64,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) )),
% 16.67/2.47    inference(definition_unfolding,[],[f34,f37,f63,f63])).
% 16.67/2.47  fof(f34,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 16.67/2.47    inference(cnf_transformation,[],[f12])).
% 16.67/2.47  fof(f12,axiom,(
% 16.67/2.47    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 16.67/2.47  fof(f56,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 16.67/2.47    inference(cnf_transformation,[],[f24])).
% 16.67/2.47  fof(f24,axiom,(
% 16.67/2.47    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 16.67/2.47  fof(f201,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))),k4_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))))) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0)))))) )),
% 16.67/2.47    inference(superposition,[],[f70,f77])).
% 16.67/2.47  fof(f70,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k4_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0)))))) )),
% 16.67/2.47    inference(definition_unfolding,[],[f32,f65,f37,f61,f46])).
% 16.67/2.47  fof(f65,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) )),
% 16.67/2.47    inference(definition_unfolding,[],[f31,f37,f62,f63])).
% 16.67/2.47  fof(f31,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 16.67/2.47    inference(cnf_transformation,[],[f15])).
% 16.67/2.47  fof(f15,axiom,(
% 16.67/2.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).
% 16.67/2.47  fof(f32,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))) )),
% 16.67/2.47    inference(cnf_transformation,[],[f14])).
% 16.67/2.47  fof(f14,axiom,(
% 16.67/2.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_enumset1)).
% 16.67/2.47  fof(f5200,plain,(
% 16.67/2.47    ( ! [X23,X21,X22] : (r2_hidden(X23,k5_enumset1(X21,X22,X23,X23,X23,X23,X22))) )),
% 16.67/2.47    inference(forward_demodulation,[],[f5150,f3106])).
% 16.67/2.47  fof(f3106,plain,(
% 16.67/2.47    ( ! [X269,X265,X267,X268,X270,X266] : (k5_xboole_0(k2_tarski(X270,X270),k4_xboole_0(k5_enumset1(X265,X266,X267,X267,X267,X268,X269),k2_tarski(X270,X270))) = k5_enumset1(X270,X265,X266,X267,X267,X268,X269)) )),
% 16.67/2.47    inference(backward_demodulation,[],[f1575,f3104])).
% 16.67/2.47  fof(f3104,plain,(
% 16.67/2.47    ( ! [X288,X285,X287,X289,X284,X286] : (k5_xboole_0(k2_tarski(X289,X284),k4_xboole_0(k5_enumset1(X285,X285,X285,X286,X286,X287,X288),k2_tarski(X289,X284))) = k5_enumset1(X289,X284,X285,X286,X286,X287,X288)) )),
% 16.67/2.47    inference(forward_demodulation,[],[f3103,f216])).
% 16.67/2.47  fof(f3103,plain,(
% 16.67/2.47    ( ! [X288,X285,X287,X289,X284,X286] : (k5_xboole_0(k2_tarski(X289,X284),k4_xboole_0(k5_enumset1(X285,X285,X285,X286,X286,X287,X288),k2_tarski(X289,X284))) = k5_xboole_0(k2_tarski(X289,X289),k4_xboole_0(k5_enumset1(X284,X284,X285,X286,X286,X287,X288),k2_tarski(X289,X289)))) )),
% 16.67/2.47    inference(forward_demodulation,[],[f3079,f552])).
% 16.67/2.47  fof(f552,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k5_enumset1(X4,X0,X0,X0,X0,X1,X2),k2_tarski(X3,X3))) = k5_enumset1(X3,X3,X4,X0,X0,X1,X2)) )),
% 16.67/2.47    inference(backward_demodulation,[],[f498,f542])).
% 16.67/2.47  fof(f542,plain,(
% 16.67/2.47    ( ! [X6,X10,X8,X7,X9] : (k5_enumset1(X6,X6,X7,X8,X8,X9,X10) = k5_xboole_0(k2_tarski(X6,X7),k4_xboole_0(k5_xboole_0(k2_tarski(X9,X8),k4_xboole_0(k2_tarski(X10,X8),k2_tarski(X9,X8))),k2_tarski(X6,X7)))) )),
% 16.67/2.47    inference(superposition,[],[f169,f147])).
% 16.67/2.47  fof(f169,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X4,X5),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X3,X3,X4,X5)))) )),
% 16.67/2.47    inference(superposition,[],[f68,f77])).
% 16.67/2.47  fof(f498,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k5_enumset1(X4,X0,X0,X0,X0,X1,X2),k2_tarski(X3,X3))) = k5_xboole_0(k2_tarski(X3,X4),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k2_tarski(X3,X4)))) )),
% 16.67/2.47    inference(superposition,[],[f218,f77])).
% 16.67/2.47  fof(f218,plain,(
% 16.67/2.47    ( ! [X14,X12,X10,X8,X7,X13,X11,X9] : (k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k5_enumset1(X8,X9,X10,X11,X12,X13,X14),k2_tarski(X7,X7))) = k5_xboole_0(k2_tarski(X7,X8),k4_xboole_0(k5_enumset1(X9,X9,X10,X11,X12,X13,X14),k2_tarski(X7,X8)))) )),
% 16.67/2.47    inference(forward_demodulation,[],[f203,f67])).
% 16.67/2.47  fof(f203,plain,(
% 16.67/2.47    ( ! [X14,X12,X10,X8,X7,X13,X11,X9] : (k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k5_enumset1(X8,X9,X10,X11,X12,X13,X14),k2_tarski(X7,X7))) = k5_xboole_0(k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k2_tarski(X8,X7),k2_tarski(X7,X7))),k4_xboole_0(k5_enumset1(X9,X9,X10,X11,X12,X13,X14),k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k2_tarski(X8,X7),k2_tarski(X7,X7)))))) )),
% 16.67/2.47    inference(superposition,[],[f70,f72])).
% 16.67/2.47  fof(f72,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X0,X0)))) )),
% 16.67/2.47    inference(definition_unfolding,[],[f35,f64,f37,f42])).
% 16.67/2.47  fof(f35,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 16.67/2.47    inference(cnf_transformation,[],[f17])).
% 16.67/2.47  fof(f17,axiom,(
% 16.67/2.47    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).
% 16.67/2.47  fof(f3079,plain,(
% 16.67/2.47    ( ! [X288,X285,X287,X289,X284,X286] : (k5_xboole_0(k2_tarski(X289,X284),k4_xboole_0(k5_enumset1(X285,X285,X285,X286,X286,X287,X288),k2_tarski(X289,X284))) = k5_xboole_0(k2_tarski(X289,X289),k4_xboole_0(k5_xboole_0(k2_tarski(X284,X284),k4_xboole_0(k5_enumset1(X285,X286,X286,X286,X286,X287,X288),k2_tarski(X284,X284))),k2_tarski(X289,X289)))) )),
% 16.67/2.47    inference(superposition,[],[f218,f930])).
% 16.67/2.47  fof(f930,plain,(
% 16.67/2.47    ( ! [X6,X10,X8,X7,X9] : (k5_xboole_0(k2_tarski(X6,X6),k4_xboole_0(k5_enumset1(X7,X8,X8,X8,X8,X9,X10),k2_tarski(X6,X6))) = k5_enumset1(X6,X7,X7,X8,X8,X9,X10)) )),
% 16.67/2.47    inference(forward_demodulation,[],[f905,f216])).
% 16.67/2.47  fof(f905,plain,(
% 16.67/2.47    ( ! [X6,X10,X8,X7,X9] : (k5_enumset1(X6,X7,X7,X8,X8,X9,X10) = k5_xboole_0(k2_tarski(X6,X6),k4_xboole_0(k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X9,X10),k2_tarski(X7,X7))),k2_tarski(X6,X6)))) )),
% 16.67/2.47    inference(superposition,[],[f183,f548])).
% 16.67/2.47  fof(f548,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_enumset1(X3,X3,X3,X4,X0,X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X4,X0,X0,X0))) = k5_enumset1(X3,X4,X4,X0,X0,X1,X2)) )),
% 16.67/2.47    inference(backward_demodulation,[],[f187,f547])).
% 16.67/2.47  fof(f547,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k2_tarski(X4,X4),k4_xboole_0(k5_xboole_0(k2_tarski(X3,X5),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k2_tarski(X3,X5))),k2_tarski(X4,X4))) = k5_enumset1(X4,X3,X5,X0,X0,X1,X2)) )),
% 16.67/2.47    inference(backward_demodulation,[],[f523,f541])).
% 16.67/2.47  fof(f541,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k4_xboole_0(k5_xboole_0(k2_tarski(X4,X3),k4_xboole_0(k2_tarski(X5,X3),k2_tarski(X4,X3))),k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0)))))) )),
% 16.67/2.47    inference(superposition,[],[f169,f77])).
% 16.67/2.47  fof(f523,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_tarski(X3,X4),k4_xboole_0(k2_tarski(X5,X4),k2_tarski(X3,X4))),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_xboole_0(k2_tarski(X3,X4),k4_xboole_0(k2_tarski(X5,X4),k2_tarski(X3,X4))))) = k5_xboole_0(k2_tarski(X4,X4),k4_xboole_0(k5_xboole_0(k2_tarski(X3,X5),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k2_tarski(X3,X5))),k2_tarski(X4,X4)))) )),
% 16.67/2.47    inference(superposition,[],[f513,f77])).
% 16.67/2.47  fof(f513,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k4_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k2_tarski(X1,X2))),k2_tarski(X0,X0)))) )),
% 16.67/2.47    inference(backward_demodulation,[],[f70,f502])).
% 16.67/2.47  fof(f502,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X8,X8,X8,X0,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X0,X1,X2,X3))) = k5_xboole_0(k2_tarski(X8,X8),k4_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k5_enumset1(X2,X2,X3,X4,X5,X6,X7),k2_tarski(X0,X1))),k2_tarski(X8,X8)))) )),
% 16.67/2.47    inference(superposition,[],[f90,f218])).
% 16.67/2.47  fof(f90,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k2_tarski(X1,X1))),k2_tarski(X0,X0)))) )),
% 16.67/2.47    inference(backward_demodulation,[],[f71,f72])).
% 16.67/2.47  fof(f71,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X2,X3,X4))),k2_tarski(X0,X0)))) )),
% 16.67/2.47    inference(definition_unfolding,[],[f33,f65,f37,f42,f64])).
% 16.67/2.47  fof(f33,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 16.67/2.47    inference(cnf_transformation,[],[f13])).
% 16.67/2.47  fof(f13,axiom,(
% 16.67/2.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).
% 16.67/2.47  fof(f187,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_enumset1(X3,X3,X3,X4,X0,X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X4,X0,X0,X0))) = k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k5_xboole_0(k2_tarski(X4,X4),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k2_tarski(X4,X4))),k2_tarski(X3,X3)))) )),
% 16.67/2.47    inference(superposition,[],[f90,f77])).
% 16.67/2.47  fof(f183,plain,(
% 16.67/2.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k5_xboole_0(k2_tarski(X4,X4),k4_xboole_0(k5_enumset1(X5,X6,X7,X0,X0,X1,X2),k2_tarski(X4,X4))),k2_tarski(X3,X3))) = k5_xboole_0(k5_enumset1(X3,X3,X3,X4,X5,X6,X7),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X4,X5,X6,X7)))) )),
% 16.67/2.47    inference(superposition,[],[f90,f77])).
% 16.67/2.47  fof(f1575,plain,(
% 16.67/2.47    ( ! [X269,X265,X267,X268,X270,X266] : (k5_xboole_0(k2_tarski(X270,X265),k4_xboole_0(k5_enumset1(X266,X266,X266,X267,X267,X268,X269),k2_tarski(X270,X265))) = k5_xboole_0(k2_tarski(X270,X270),k4_xboole_0(k5_enumset1(X265,X266,X267,X267,X267,X268,X269),k2_tarski(X270,X270)))) )),
% 16.67/2.47    inference(superposition,[],[f218,f572])).
% 16.67/2.47  fof(f572,plain,(
% 16.67/2.47    ( ! [X6,X4,X8,X7,X5] : (k5_enumset1(X4,X5,X5,X6,X6,X7,X8) = k5_enumset1(X4,X5,X6,X6,X6,X7,X8)) )),
% 16.67/2.47    inference(superposition,[],[f549,f548])).
% 16.67/2.47  fof(f549,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k5_xboole_0(k5_enumset1(X3,X3,X3,X4,X5,X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X4,X5,X0,X0)))) )),
% 16.67/2.47    inference(backward_demodulation,[],[f531,f547])).
% 16.67/2.47  fof(f531,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X3,X3,X3,X4,X5,X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X4,X5,X0,X0))) = k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k5_xboole_0(k2_tarski(X4,X5),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k2_tarski(X4,X5))),k2_tarski(X3,X3)))) )),
% 16.67/2.47    inference(backward_demodulation,[],[f205,f523])).
% 16.67/2.47  fof(f205,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X3,X3,X3,X4,X5,X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_enumset1(X3,X3,X3,X4,X5,X0,X0))) = k5_xboole_0(k5_xboole_0(k2_tarski(X4,X3),k4_xboole_0(k2_tarski(X5,X3),k2_tarski(X4,X3))),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k5_xboole_0(k2_tarski(X4,X3),k4_xboole_0(k2_tarski(X5,X3),k2_tarski(X4,X3)))))) )),
% 16.67/2.47    inference(superposition,[],[f70,f77])).
% 16.67/2.47  fof(f5150,plain,(
% 16.67/2.47    ( ! [X23,X21,X22] : (r2_hidden(X23,k5_xboole_0(k2_tarski(X21,X21),k4_xboole_0(k5_enumset1(X22,X23,X23,X23,X23,X23,X22),k2_tarski(X21,X21))))) )),
% 16.67/2.47    inference(superposition,[],[f133,f499])).
% 16.67/2.47  fof(f499,plain,(
% 16.67/2.47    ( ! [X6,X8,X7,X5] : (k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k5_enumset1(X8,X5,X5,X5,X5,X5,X6),k2_tarski(X7,X7))) = k5_xboole_0(k2_tarski(X7,X8),k4_xboole_0(k2_tarski(X5,X6),k2_tarski(X7,X8)))) )),
% 16.67/2.47    inference(superposition,[],[f218,f147])).
% 16.67/2.47  fof(f133,plain,(
% 16.67/2.47    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X2))))) )),
% 16.67/2.47    inference(unit_resulting_resolution,[],[f87,f86])).
% 16.67/2.47  fof(f86,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0)))) | ~sP4(X4,X2,X1,X0)) )),
% 16.67/2.47    inference(equality_resolution,[],[f81])).
% 16.67/2.47  fof(f81,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X3,X1] : (~sP4(X4,X2,X1,X0) | r2_hidden(X4,X3) | k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) != X3) )),
% 16.67/2.47    inference(definition_unfolding,[],[f51,f61])).
% 16.67/2.47  fof(f51,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X3,X1] : (~sP4(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 16.67/2.47    inference(cnf_transformation,[],[f28])).
% 16.67/2.47  fof(f28,plain,(
% 16.67/2.47    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 16.67/2.47    inference(ennf_transformation,[],[f10])).
% 16.67/2.47  fof(f10,axiom,(
% 16.67/2.47    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 16.67/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 16.67/2.47  fof(f87,plain,(
% 16.67/2.47    ( ! [X4,X0,X1] : (sP4(X4,X4,X1,X0)) )),
% 16.67/2.47    inference(equality_resolution,[],[f49])).
% 16.67/2.47  fof(f49,plain,(
% 16.67/2.47    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP4(X4,X2,X1,X0)) )),
% 16.67/2.47    inference(cnf_transformation,[],[f28])).
% 16.67/2.47  % SZS output end Proof for theBenchmark
% 16.67/2.47  % (18802)------------------------------
% 16.67/2.47  % (18802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.67/2.47  % (18802)Termination reason: Refutation
% 16.67/2.47  
% 16.67/2.47  % (18802)Memory used [KB]: 27760
% 16.67/2.47  % (18802)Time elapsed: 2.042 s
% 16.67/2.47  % (18802)------------------------------
% 16.67/2.47  % (18802)------------------------------
% 16.67/2.47  % (18782)Success in time 2.113 s
%------------------------------------------------------------------------------
