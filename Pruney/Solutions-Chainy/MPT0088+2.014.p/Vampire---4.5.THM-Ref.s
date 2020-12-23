%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 669 expanded)
%              Number of leaves         :   11 ( 224 expanded)
%              Depth                    :   21
%              Number of atoms          :  109 ( 695 expanded)
%              Number of equality atoms :   87 ( 658 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2678,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2677])).

fof(f2677,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f2666,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f28,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f2666,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f36,f2641])).

fof(f2641,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f310,f2579])).

fof(f2579,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f303,f2413])).

fof(f2413,plain,(
    ! [X31,X32] : k4_xboole_0(k2_xboole_0(X32,X31),k4_xboole_0(X31,X32)) = X32 ),
    inference(forward_demodulation,[],[f2368,f307])).

fof(f307,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(backward_demodulation,[],[f282,f306])).

fof(f306,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5 ),
    inference(forward_demodulation,[],[f305,f19])).

fof(f305,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k1_xboole_0) ),
    inference(forward_demodulation,[],[f263,f34])).

fof(f263,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k4_xboole_0(X6,X6)) ),
    inference(superposition,[],[f33,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f27,f21])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f282,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f248,f19])).

fof(f248,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f33,f34])).

fof(f2368,plain,(
    ! [X31,X32] : k4_xboole_0(X32,k4_xboole_0(X31,X32)) = k4_xboole_0(k2_xboole_0(X32,X31),k4_xboole_0(X31,X32)) ),
    inference(superposition,[],[f1910,f1912])).

fof(f1912,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k2_xboole_0(k4_xboole_0(X15,X14),X14) ),
    inference(backward_demodulation,[],[f1418,f1910])).

fof(f1418,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X14,X15),X14),X14) ),
    inference(forward_demodulation,[],[f1341,f19])).

fof(f1341,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X14,X15),X14),k4_xboole_0(X14,k1_xboole_0)) ),
    inference(superposition,[],[f311,f181])).

fof(f181,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f41,f180])).

fof(f180,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(backward_demodulation,[],[f55,f178])).

fof(f178,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = X2 ),
    inference(forward_demodulation,[],[f171,f170])).

fof(f170,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f158,f19])).

fof(f158,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(superposition,[],[f30,f34])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f171,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = k2_xboole_0(X2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f63,f170])).

fof(f63,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(X2,k1_xboole_0),X2) = k2_xboole_0(k2_xboole_0(X2,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f22,f54])).

fof(f54,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f51,f35])).

fof(f35,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f22,f34])).

fof(f51,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f45,f22])).

fof(f45,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f26,f34])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f55,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(X3,X3)) ),
    inference(superposition,[],[f51,f35])).

fof(f41,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f26,f34])).

fof(f311,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = X3 ),
    inference(backward_demodulation,[],[f283,f307])).

fof(f283,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = k4_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(backward_demodulation,[],[f72,f282])).

fof(f72,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) ),
    inference(superposition,[],[f22,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f21,f21])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1910,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),X6) = k4_xboole_0(X7,X6) ),
    inference(forward_demodulation,[],[f1909,f396])).

fof(f396,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) ),
    inference(forward_demodulation,[],[f385,f19])).

fof(f385,plain,(
    ! [X6,X5] : k4_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f29,f168])).

fof(f168,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f51,f30])).

fof(f1909,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),X6) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,X6))) ),
    inference(forward_demodulation,[],[f1908,f274])).

fof(f274,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k4_xboole_0(k2_xboole_0(X11,X10),X12)) = k4_xboole_0(X10,k4_xboole_0(X10,X12)) ),
    inference(forward_demodulation,[],[f243,f139])).

fof(f139,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f138,f19])).

fof(f138,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f137,f34])).

fof(f137,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f136,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f26,f19])).

fof(f136,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) ),
    inference(forward_demodulation,[],[f129,f19])).

fof(f129,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[],[f29,f109])).

fof(f109,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X3),X3) ),
    inference(superposition,[],[f40,f34])).

fof(f243,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k4_xboole_0(k2_xboole_0(X11,X10),X12)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X10,k4_xboole_0(X10,X12))) ),
    inference(superposition,[],[f33,f51])).

fof(f1908,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),X6) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k2_xboole_0(X6,X7),X6))) ),
    inference(forward_demodulation,[],[f1868,f19])).

fof(f1868,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k2_xboole_0(X6,X7),X6))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X6,X7),X6),k1_xboole_0) ),
    inference(superposition,[],[f29,f1807])).

fof(f1807,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X7,X6),X7),X6) ),
    inference(superposition,[],[f51,f1748])).

fof(f1748,plain,(
    ! [X15,X16] : k2_xboole_0(X16,k4_xboole_0(k2_xboole_0(X15,X16),X15)) = X16 ),
    inference(forward_demodulation,[],[f1708,f170])).

fof(f1708,plain,(
    ! [X15,X16] : k2_xboole_0(X16,k1_xboole_0) = k2_xboole_0(X16,k4_xboole_0(k2_xboole_0(X15,X16),X15)) ),
    inference(superposition,[],[f47,f34])).

fof(f47,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f22,f26])).

fof(f303,plain,(
    ! [X12] : k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X12) ),
    inference(forward_demodulation,[],[f261,f170])).

fof(f261,plain,(
    ! [X12] : k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X12),k1_xboole_0) ),
    inference(superposition,[],[f33,f37])).

fof(f37,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f32,f16])).

fof(f16,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f310,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k4_xboole_0(X12,k2_xboole_0(X11,X10))) = X10 ),
    inference(backward_demodulation,[],[f287,f307])).

fof(f287,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k4_xboole_0(X12,k2_xboole_0(X11,X10))) = k4_xboole_0(X10,k4_xboole_0(X12,X10)) ),
    inference(forward_demodulation,[],[f286,f282])).

fof(f286,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k4_xboole_0(X12,k2_xboole_0(X11,X10))) = k2_xboole_0(k4_xboole_0(X10,X12),X10) ),
    inference(forward_demodulation,[],[f252,f19])).

fof(f252,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k4_xboole_0(X12,k2_xboole_0(X11,X10))) = k2_xboole_0(k4_xboole_0(X10,X12),k4_xboole_0(X10,k1_xboole_0)) ),
    inference(superposition,[],[f33,f51])).

fof(f36,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f31,f17])).

fof(f17,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f25,f21])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:18:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (27359)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (27363)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (27362)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (27371)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (27358)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (27359)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f2678,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f2677])).
% 0.22/0.47  fof(f2677,plain,(
% 0.22/0.47    k1_xboole_0 != k1_xboole_0),
% 0.22/0.47    inference(superposition,[],[f2666,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.47    inference(backward_demodulation,[],[f28,f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f18,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.47  fof(f2666,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(sK1,sK1)),
% 0.22/0.47    inference(backward_demodulation,[],[f36,f2641])).
% 0.22/0.47  fof(f2641,plain,(
% 0.22/0.47    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.47    inference(superposition,[],[f310,f2579])).
% 0.22/0.47  fof(f2579,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))),
% 0.22/0.47    inference(superposition,[],[f303,f2413])).
% 0.22/0.47  fof(f2413,plain,(
% 0.22/0.47    ( ! [X31,X32] : (k4_xboole_0(k2_xboole_0(X32,X31),k4_xboole_0(X31,X32)) = X32) )),
% 0.22/0.47    inference(forward_demodulation,[],[f2368,f307])).
% 0.22/0.47  fof(f307,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 0.22/0.47    inference(backward_demodulation,[],[f282,f306])).
% 0.22/0.47  fof(f306,plain,(
% 0.22/0.47    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5) )),
% 0.22/0.47    inference(forward_demodulation,[],[f305,f19])).
% 0.22/0.47  fof(f305,plain,(
% 0.22/0.47    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k1_xboole_0)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f263,f34])).
% 0.22/0.47  fof(f263,plain,(
% 0.22/0.47    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k4_xboole_0(X6,X6))) )),
% 0.22/0.47    inference(superposition,[],[f33,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f27,f21])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.22/0.47  fof(f282,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f248,f19])).
% 0.22/0.47  fof(f248,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.47    inference(superposition,[],[f33,f34])).
% 0.22/0.47  fof(f2368,plain,(
% 0.22/0.47    ( ! [X31,X32] : (k4_xboole_0(X32,k4_xboole_0(X31,X32)) = k4_xboole_0(k2_xboole_0(X32,X31),k4_xboole_0(X31,X32))) )),
% 0.22/0.47    inference(superposition,[],[f1910,f1912])).
% 0.22/0.47  fof(f1912,plain,(
% 0.22/0.47    ( ! [X14,X15] : (k2_xboole_0(X14,X15) = k2_xboole_0(k4_xboole_0(X15,X14),X14)) )),
% 0.22/0.47    inference(backward_demodulation,[],[f1418,f1910])).
% 0.22/0.47  fof(f1418,plain,(
% 0.22/0.47    ( ! [X14,X15] : (k2_xboole_0(X14,X15) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X14,X15),X14),X14)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f1341,f19])).
% 0.22/0.47  fof(f1341,plain,(
% 0.22/0.47    ( ! [X14,X15] : (k2_xboole_0(X14,X15) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X14,X15),X14),k4_xboole_0(X14,k1_xboole_0))) )),
% 0.22/0.47    inference(superposition,[],[f311,f181])).
% 0.22/0.47  fof(f181,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.22/0.47    inference(backward_demodulation,[],[f41,f180])).
% 0.22/0.47  fof(f180,plain,(
% 0.22/0.47    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.22/0.47    inference(backward_demodulation,[],[f55,f178])).
% 0.22/0.47  fof(f178,plain,(
% 0.22/0.47    ( ! [X2] : (k2_xboole_0(X2,X2) = X2) )),
% 0.22/0.47    inference(forward_demodulation,[],[f171,f170])).
% 0.22/0.47  fof(f170,plain,(
% 0.22/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.47    inference(forward_demodulation,[],[f158,f19])).
% 0.22/0.47  fof(f158,plain,(
% 0.22/0.47    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) )),
% 0.22/0.47    inference(superposition,[],[f30,f34])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.47    inference(definition_unfolding,[],[f23,f21])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.47  fof(f171,plain,(
% 0.22/0.47    ( ! [X2] : (k2_xboole_0(X2,X2) = k2_xboole_0(X2,k1_xboole_0)) )),
% 0.22/0.47    inference(backward_demodulation,[],[f63,f170])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    ( ! [X2] : (k2_xboole_0(k2_xboole_0(X2,k1_xboole_0),X2) = k2_xboole_0(k2_xboole_0(X2,k1_xboole_0),k1_xboole_0)) )),
% 0.22/0.47    inference(superposition,[],[f22,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,k1_xboole_0))) )),
% 0.22/0.47    inference(superposition,[],[f51,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)) )),
% 0.22/0.47    inference(superposition,[],[f22,f34])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f45,f22])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 0.22/0.47    inference(superposition,[],[f26,f34])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(X3,X3))) )),
% 0.22/0.47    inference(superposition,[],[f51,f35])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.22/0.47    inference(superposition,[],[f26,f34])).
% 0.22/0.47  fof(f311,plain,(
% 0.22/0.47    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = X3) )),
% 0.22/0.47    inference(backward_demodulation,[],[f283,f307])).
% 0.22/0.47  fof(f283,plain,(
% 0.22/0.47    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = k4_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 0.22/0.47    inference(backward_demodulation,[],[f72,f282])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3)))) )),
% 0.22/0.47    inference(superposition,[],[f22,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f20,f21,f21])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.47  fof(f1910,plain,(
% 0.22/0.47    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),X6) = k4_xboole_0(X7,X6)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f1909,f396])).
% 0.22/0.47  fof(f396,plain,(
% 0.22/0.47    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6)))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f385,f19])).
% 0.22/0.47  fof(f385,plain,(
% 0.22/0.47    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6)))) )),
% 0.22/0.47    inference(superposition,[],[f29,f168])).
% 0.22/0.47  fof(f168,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.47    inference(superposition,[],[f51,f30])).
% 0.22/0.47  fof(f1909,plain,(
% 0.22/0.47    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),X6) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,X6)))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f1908,f274])).
% 0.22/0.47  fof(f274,plain,(
% 0.22/0.47    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k4_xboole_0(k2_xboole_0(X11,X10),X12)) = k4_xboole_0(X10,k4_xboole_0(X10,X12))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f243,f139])).
% 0.22/0.47  fof(f139,plain,(
% 0.22/0.47    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.47    inference(forward_demodulation,[],[f138,f19])).
% 0.22/0.47  fof(f138,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f137,f34])).
% 0.22/0.47  fof(f137,plain,(
% 0.22/0.47    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f136,f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 0.22/0.47    inference(superposition,[],[f26,f19])).
% 0.22/0.47  fof(f136,plain,(
% 0.22/0.47    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0)))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f129,f19])).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0)) )),
% 0.22/0.47    inference(superposition,[],[f29,f109])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X3),X3)) )),
% 0.22/0.47    inference(superposition,[],[f40,f34])).
% 0.22/0.47  fof(f243,plain,(
% 0.22/0.47    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k4_xboole_0(k2_xboole_0(X11,X10),X12)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X10,k4_xboole_0(X10,X12)))) )),
% 0.22/0.47    inference(superposition,[],[f33,f51])).
% 0.22/0.47  fof(f1908,plain,(
% 0.22/0.47    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),X6) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k2_xboole_0(X6,X7),X6)))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f1868,f19])).
% 0.22/0.47  fof(f1868,plain,(
% 0.22/0.47    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k2_xboole_0(X6,X7),X6))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X6,X7),X6),k1_xboole_0)) )),
% 0.22/0.47    inference(superposition,[],[f29,f1807])).
% 0.22/0.47  fof(f1807,plain,(
% 0.22/0.47    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X7,X6),X7),X6)) )),
% 0.22/0.47    inference(superposition,[],[f51,f1748])).
% 0.22/0.47  fof(f1748,plain,(
% 0.22/0.47    ( ! [X15,X16] : (k2_xboole_0(X16,k4_xboole_0(k2_xboole_0(X15,X16),X15)) = X16) )),
% 0.22/0.47    inference(forward_demodulation,[],[f1708,f170])).
% 0.22/0.47  fof(f1708,plain,(
% 0.22/0.47    ( ! [X15,X16] : (k2_xboole_0(X16,k1_xboole_0) = k2_xboole_0(X16,k4_xboole_0(k2_xboole_0(X15,X16),X15))) )),
% 0.22/0.47    inference(superposition,[],[f47,f34])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 0.22/0.47    inference(superposition,[],[f22,f26])).
% 0.22/0.47  fof(f303,plain,(
% 0.22/0.47    ( ! [X12] : (k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X12)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f261,f170])).
% 0.22/0.47  fof(f261,plain,(
% 0.22/0.47    ( ! [X12] : (k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X12),k1_xboole_0)) )),
% 0.22/0.47    inference(superposition,[],[f33,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.47    inference(resolution,[],[f32,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.22/0.47    inference(negated_conjecture,[],[f10])).
% 0.22/0.47  fof(f10,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f24,f21])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.48  fof(f310,plain,(
% 0.22/0.48    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X12,k2_xboole_0(X11,X10))) = X10) )),
% 0.22/0.48    inference(backward_demodulation,[],[f287,f307])).
% 0.22/0.48  fof(f287,plain,(
% 0.22/0.48    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X12,k2_xboole_0(X11,X10))) = k4_xboole_0(X10,k4_xboole_0(X12,X10))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f286,f282])).
% 0.22/0.48  fof(f286,plain,(
% 0.22/0.48    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X12,k2_xboole_0(X11,X10))) = k2_xboole_0(k4_xboole_0(X10,X12),X10)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f252,f19])).
% 0.22/0.48  fof(f252,plain,(
% 0.22/0.48    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X12,k2_xboole_0(X11,X10))) = k2_xboole_0(k4_xboole_0(X10,X12),k4_xboole_0(X10,k1_xboole_0))) )),
% 0.22/0.48    inference(superposition,[],[f33,f51])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 0.22/0.48    inference(resolution,[],[f31,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f25,f21])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (27359)------------------------------
% 0.22/0.48  % (27359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27359)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (27359)Memory used [KB]: 3454
% 0.22/0.48  % (27359)Time elapsed: 0.061 s
% 0.22/0.48  % (27359)------------------------------
% 0.22/0.48  % (27359)------------------------------
% 0.22/0.48  % (27372)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (27357)Success in time 0.114 s
%------------------------------------------------------------------------------
