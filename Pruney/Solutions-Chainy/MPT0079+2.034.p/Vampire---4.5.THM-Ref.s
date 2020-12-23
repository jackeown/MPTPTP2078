%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:56 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 594 expanded)
%              Number of leaves         :   13 ( 184 expanded)
%              Depth                    :   30
%              Number of atoms          :  118 ( 774 expanded)
%              Number of equality atoms :   97 ( 642 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1904,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1903,f21])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f1903,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f1902,f44])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f25,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1902,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f1897,f1699])).

fof(f1699,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f1677,f147])).

fof(f147,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f146,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f35,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f146,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f28,f143])).

fof(f143,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f142,f18])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f142,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f141,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f141,plain,(
    k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)) ),
    inference(superposition,[],[f27,f127])).

fof(f127,plain,(
    k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f58,f18])).

fof(f58,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1677,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f33,f1616])).

fof(f1616,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f81,f1553])).

fof(f1553,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(superposition,[],[f36,f487])).

fof(f487,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(X13,X12),X12) ),
    inference(forward_demodulation,[],[f449,f24])).

fof(f449,plain,(
    ! [X12,X13] : k2_xboole_0(k4_xboole_0(X13,X12),X12) = k2_xboole_0(k2_xboole_0(X12,X13),k1_xboole_0) ),
    inference(superposition,[],[f368,f27])).

fof(f368,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f331,f169])).

fof(f169,plain,(
    ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f168,f69])).

fof(f69,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f65,f27])).

fof(f65,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f27,f28])).

fof(f168,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X5)) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f154,f25])).

fof(f154,plain,(
    ! [X6,X5] : k2_xboole_0(k2_xboole_0(X6,X5),X5) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f69,f69])).

fof(f331,plain,(
    ! [X4,X3] : k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f27,f259])).

fof(f259,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) ),
    inference(backward_demodulation,[],[f166,f236])).

fof(f236,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f234,f25])).

fof(f234,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f232,f39])).

fof(f232,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f28,f140])).

fof(f140,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f130,f27])).

fof(f130,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f27,f58])).

fof(f166,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f28,f69])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f81,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(forward_demodulation,[],[f80,f24])).

fof(f80,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[],[f27,f78])).

fof(f78,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f37,f19])).

fof(f19,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1897,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK2,sK1),sK1) ),
    inference(superposition,[],[f36,f1886])).

fof(f1886,plain,(
    sK1 = k4_xboole_0(sK2,sK3) ),
    inference(backward_demodulation,[],[f61,f1885])).

fof(f1885,plain,(
    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(forward_demodulation,[],[f1852,f1615])).

fof(f1615,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(backward_demodulation,[],[f87,f1553])).

fof(f87,plain,(
    k4_xboole_0(sK1,sK3) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(forward_demodulation,[],[f86,f24])).

fof(f86,plain,(
    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(superposition,[],[f27,f77])).

fof(f77,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f37,f41])).

fof(f41,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f30,f20])).

fof(f20,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1852,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f58,f1818])).

fof(f1818,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f1817,f25])).

fof(f1817,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f1816,f69])).

fof(f1816,plain,(
    k2_xboole_0(sK3,sK1) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1815,f368])).

fof(f1815,plain,(
    k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1814,f175])).

fof(f175,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f159,f73])).

fof(f73,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f72,f18])).

fof(f72,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f71,f25])).

fof(f71,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f70,f27])).

fof(f70,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f27,f61])).

fof(f159,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f69,f18])).

fof(f1814,plain,(
    k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(sK1,k2_xboole_0(sK3,sK2)) ),
    inference(forward_demodulation,[],[f1809,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1809,plain,(
    k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(superposition,[],[f27,f1714])).

fof(f1714,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f1692,f147])).

fof(f1692,plain,(
    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f1677,f1091])).

fof(f1091,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f34,f89])).

fof(f89,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(forward_demodulation,[],[f88,f24])).

fof(f88,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f27,f75])).

fof(f75,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f74,f39])).

fof(f74,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f28,f73])).

fof(f61,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f28,f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:58:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (16321)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (16340)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (16324)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (16320)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (16332)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (16323)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (16326)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (16331)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (16328)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (16341)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (16333)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (16333)Refutation not found, incomplete strategy% (16333)------------------------------
% 0.22/0.54  % (16333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16333)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (16333)Memory used [KB]: 6140
% 0.22/0.54  % (16333)Time elapsed: 0.004 s
% 0.22/0.54  % (16333)------------------------------
% 0.22/0.54  % (16333)------------------------------
% 0.22/0.54  % (16325)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (16344)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (16319)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (16346)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (16335)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (16322)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (16338)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (16343)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.55  % (16330)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (16334)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.56  % (16347)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.56  % (16336)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.56  % (16339)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.56  % (16327)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.56  % (16348)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.56  % (16335)Refutation not found, incomplete strategy% (16335)------------------------------
% 1.42/0.56  % (16335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (16335)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (16335)Memory used [KB]: 10618
% 1.42/0.56  % (16335)Time elapsed: 0.124 s
% 1.42/0.56  % (16335)------------------------------
% 1.42/0.56  % (16335)------------------------------
% 1.42/0.56  % (16318)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.42/0.56  % (16342)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.55/0.58  % (16337)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.55/0.58  % (16329)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.55/0.60  % (16324)Refutation found. Thanks to Tanya!
% 1.55/0.60  % SZS status Theorem for theBenchmark
% 1.55/0.60  % SZS output start Proof for theBenchmark
% 1.55/0.60  fof(f1904,plain,(
% 1.55/0.60    $false),
% 1.55/0.60    inference(subsumption_resolution,[],[f1903,f21])).
% 1.55/0.60  fof(f21,plain,(
% 1.55/0.60    sK1 != sK2),
% 1.55/0.60    inference(cnf_transformation,[],[f16])).
% 1.55/0.60  fof(f16,plain,(
% 1.55/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.55/0.60    inference(flattening,[],[f15])).
% 1.55/0.60  fof(f15,plain,(
% 1.55/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.55/0.60    inference(ennf_transformation,[],[f14])).
% 1.55/0.60  fof(f14,negated_conjecture,(
% 1.55/0.60    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.55/0.60    inference(negated_conjecture,[],[f13])).
% 1.55/0.60  fof(f13,conjecture,(
% 1.55/0.60    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.55/0.60  fof(f1903,plain,(
% 1.55/0.60    sK1 = sK2),
% 1.55/0.60    inference(forward_demodulation,[],[f1902,f44])).
% 1.55/0.60  fof(f44,plain,(
% 1.55/0.60    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.55/0.60    inference(superposition,[],[f25,f24])).
% 1.55/0.60  fof(f24,plain,(
% 1.55/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.55/0.60    inference(cnf_transformation,[],[f4])).
% 1.55/0.60  fof(f4,axiom,(
% 1.55/0.60    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.55/0.60  fof(f25,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f1])).
% 1.55/0.60  fof(f1,axiom,(
% 1.55/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.55/0.60  fof(f1902,plain,(
% 1.55/0.60    sK2 = k2_xboole_0(k1_xboole_0,sK1)),
% 1.55/0.60    inference(forward_demodulation,[],[f1897,f1699])).
% 1.55/0.60  fof(f1699,plain,(
% 1.55/0.60    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.55/0.60    inference(superposition,[],[f1677,f147])).
% 1.55/0.60  fof(f147,plain,(
% 1.55/0.60    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.55/0.60    inference(forward_demodulation,[],[f146,f39])).
% 1.55/0.60  fof(f39,plain,(
% 1.55/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.55/0.60    inference(backward_demodulation,[],[f35,f23])).
% 1.55/0.60  fof(f23,plain,(
% 1.55/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.55/0.60    inference(cnf_transformation,[],[f7])).
% 1.55/0.60  fof(f7,axiom,(
% 1.55/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.55/0.60  fof(f35,plain,(
% 1.55/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.55/0.60    inference(definition_unfolding,[],[f22,f26])).
% 1.55/0.60  fof(f26,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f10])).
% 1.55/0.60  fof(f10,axiom,(
% 1.55/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.55/0.60  fof(f22,plain,(
% 1.55/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f5])).
% 1.55/0.60  fof(f5,axiom,(
% 1.55/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.55/0.60  fof(f146,plain,(
% 1.55/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.55/0.60    inference(superposition,[],[f28,f143])).
% 1.55/0.60  fof(f143,plain,(
% 1.55/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.55/0.60    inference(forward_demodulation,[],[f142,f18])).
% 1.55/0.60  fof(f18,plain,(
% 1.55/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.55/0.60    inference(cnf_transformation,[],[f16])).
% 1.55/0.60  fof(f142,plain,(
% 1.55/0.60    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.55/0.60    inference(forward_demodulation,[],[f141,f27])).
% 1.55/0.60  fof(f27,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f6])).
% 1.55/0.60  fof(f6,axiom,(
% 1.55/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.55/0.60  fof(f141,plain,(
% 1.55/0.60    k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),
% 1.55/0.60    inference(superposition,[],[f27,f127])).
% 1.55/0.60  fof(f127,plain,(
% 1.55/0.60    k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 1.55/0.60    inference(superposition,[],[f58,f18])).
% 1.55/0.60  fof(f58,plain,(
% 1.55/0.60    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 1.55/0.60    inference(superposition,[],[f28,f25])).
% 1.55/0.60  fof(f28,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f8])).
% 1.55/0.60  fof(f8,axiom,(
% 1.55/0.60    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.55/0.60  fof(f1677,plain,(
% 1.55/0.60    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 1.55/0.60    inference(superposition,[],[f33,f1616])).
% 1.55/0.60  fof(f1616,plain,(
% 1.55/0.60    sK2 = k4_xboole_0(sK2,sK0)),
% 1.55/0.60    inference(backward_demodulation,[],[f81,f1553])).
% 1.55/0.60  fof(f1553,plain,(
% 1.55/0.60    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 1.55/0.60    inference(superposition,[],[f36,f487])).
% 1.55/0.60  fof(f487,plain,(
% 1.55/0.60    ( ! [X12,X13] : (k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(X13,X12),X12)) )),
% 1.55/0.60    inference(forward_demodulation,[],[f449,f24])).
% 1.55/0.60  fof(f449,plain,(
% 1.55/0.60    ( ! [X12,X13] : (k2_xboole_0(k4_xboole_0(X13,X12),X12) = k2_xboole_0(k2_xboole_0(X12,X13),k1_xboole_0)) )),
% 1.55/0.60    inference(superposition,[],[f368,f27])).
% 1.55/0.60  fof(f368,plain,(
% 1.55/0.60    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0)) )),
% 1.55/0.60    inference(forward_demodulation,[],[f331,f169])).
% 1.55/0.60  fof(f169,plain,(
% 1.55/0.60    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))) )),
% 1.55/0.60    inference(forward_demodulation,[],[f168,f69])).
% 1.55/0.60  fof(f69,plain,(
% 1.55/0.60    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X2,k2_xboole_0(X1,X2))) )),
% 1.55/0.60    inference(forward_demodulation,[],[f65,f27])).
% 1.55/0.60  fof(f65,plain,(
% 1.55/0.60    ( ! [X2,X1] : (k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2))) )),
% 1.55/0.60    inference(superposition,[],[f27,f28])).
% 1.55/0.60  fof(f168,plain,(
% 1.55/0.60    ( ! [X6,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X5)) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))) )),
% 1.55/0.60    inference(forward_demodulation,[],[f154,f25])).
% 1.55/0.60  fof(f154,plain,(
% 1.55/0.60    ( ! [X6,X5] : (k2_xboole_0(k2_xboole_0(X6,X5),X5) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))) )),
% 1.55/0.60    inference(superposition,[],[f69,f69])).
% 1.55/0.60  fof(f331,plain,(
% 1.55/0.60    ( ! [X4,X3] : (k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4))) )),
% 1.55/0.60    inference(superposition,[],[f27,f259])).
% 1.55/0.60  fof(f259,plain,(
% 1.55/0.60    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2))) )),
% 1.55/0.60    inference(backward_demodulation,[],[f166,f236])).
% 1.55/0.60  fof(f236,plain,(
% 1.55/0.60    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 1.55/0.60    inference(superposition,[],[f234,f25])).
% 1.55/0.60  fof(f234,plain,(
% 1.55/0.60    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 1.55/0.60    inference(forward_demodulation,[],[f232,f39])).
% 1.55/0.60  fof(f232,plain,(
% 1.55/0.60    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 1.55/0.60    inference(superposition,[],[f28,f140])).
% 1.55/0.60  fof(f140,plain,(
% 1.55/0.60    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 1.55/0.60    inference(forward_demodulation,[],[f130,f27])).
% 1.55/0.60  fof(f130,plain,(
% 1.55/0.60    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 1.55/0.60    inference(superposition,[],[f27,f58])).
% 1.55/0.60  fof(f166,plain,(
% 1.55/0.60    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2))) )),
% 1.55/0.60    inference(superposition,[],[f28,f69])).
% 1.55/0.60  fof(f36,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.55/0.60    inference(definition_unfolding,[],[f29,f26])).
% 1.55/0.60  fof(f29,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.55/0.60    inference(cnf_transformation,[],[f12])).
% 1.55/0.60  fof(f12,axiom,(
% 1.55/0.60    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.55/0.60  fof(f81,plain,(
% 1.55/0.60    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2)),
% 1.55/0.60    inference(forward_demodulation,[],[f80,f24])).
% 1.55/0.60  fof(f80,plain,(
% 1.55/0.60    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0)),
% 1.55/0.60    inference(superposition,[],[f27,f78])).
% 1.55/0.60  fof(f78,plain,(
% 1.55/0.60    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.55/0.60    inference(resolution,[],[f37,f19])).
% 1.55/0.60  fof(f19,plain,(
% 1.55/0.60    r1_xboole_0(sK2,sK0)),
% 1.55/0.60    inference(cnf_transformation,[],[f16])).
% 1.55/0.60  fof(f37,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.55/0.60    inference(definition_unfolding,[],[f32,f26])).
% 1.55/0.60  fof(f32,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f2])).
% 1.55/0.60  fof(f2,axiom,(
% 1.55/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.55/0.60  fof(f33,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f9])).
% 1.55/0.60  fof(f9,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.55/0.60  fof(f1897,plain,(
% 1.55/0.60    sK2 = k2_xboole_0(k4_xboole_0(sK2,sK1),sK1)),
% 1.55/0.60    inference(superposition,[],[f36,f1886])).
% 1.55/0.60  fof(f1886,plain,(
% 1.55/0.60    sK1 = k4_xboole_0(sK2,sK3)),
% 1.55/0.60    inference(backward_demodulation,[],[f61,f1885])).
% 1.55/0.60  fof(f1885,plain,(
% 1.55/0.60    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.55/0.60    inference(forward_demodulation,[],[f1852,f1615])).
% 1.55/0.60  fof(f1615,plain,(
% 1.55/0.60    sK1 = k4_xboole_0(sK1,sK3)),
% 1.55/0.60    inference(backward_demodulation,[],[f87,f1553])).
% 1.55/0.60  fof(f87,plain,(
% 1.55/0.60    k4_xboole_0(sK1,sK3) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1)),
% 1.55/0.60    inference(forward_demodulation,[],[f86,f24])).
% 1.55/0.60  fof(f86,plain,(
% 1.55/0.60    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)),
% 1.55/0.60    inference(superposition,[],[f27,f77])).
% 1.55/0.60  fof(f77,plain,(
% 1.55/0.60    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.55/0.60    inference(resolution,[],[f37,f41])).
% 1.55/0.60  fof(f41,plain,(
% 1.55/0.60    r1_xboole_0(sK1,sK3)),
% 1.55/0.60    inference(resolution,[],[f30,f20])).
% 1.55/0.60  fof(f20,plain,(
% 1.55/0.60    r1_xboole_0(sK3,sK1)),
% 1.55/0.60    inference(cnf_transformation,[],[f16])).
% 1.55/0.60  fof(f30,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f17])).
% 1.55/0.60  fof(f17,plain,(
% 1.55/0.60    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.55/0.60    inference(ennf_transformation,[],[f3])).
% 1.55/0.60  fof(f3,axiom,(
% 1.55/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.55/0.60  fof(f1852,plain,(
% 1.55/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3)),
% 1.55/0.60    inference(superposition,[],[f58,f1818])).
% 1.55/0.60  fof(f1818,plain,(
% 1.55/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK1)),
% 1.55/0.60    inference(forward_demodulation,[],[f1817,f25])).
% 1.55/0.60  fof(f1817,plain,(
% 1.55/0.60    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK3,sK1)),
% 1.55/0.60    inference(forward_demodulation,[],[f1816,f69])).
% 1.55/0.60  fof(f1816,plain,(
% 1.55/0.60    k2_xboole_0(sK3,sK1) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 1.55/0.60    inference(forward_demodulation,[],[f1815,f368])).
% 1.55/0.60  fof(f1815,plain,(
% 1.55/0.60    k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0)),
% 1.55/0.60    inference(forward_demodulation,[],[f1814,f175])).
% 1.55/0.60  fof(f175,plain,(
% 1.55/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 1.55/0.60    inference(forward_demodulation,[],[f159,f73])).
% 1.55/0.60  fof(f73,plain,(
% 1.55/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.55/0.60    inference(forward_demodulation,[],[f72,f18])).
% 1.55/0.60  fof(f72,plain,(
% 1.55/0.60    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.55/0.60    inference(forward_demodulation,[],[f71,f25])).
% 1.55/0.60  fof(f71,plain,(
% 1.55/0.60    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.55/0.60    inference(forward_demodulation,[],[f70,f27])).
% 1.55/0.60  fof(f70,plain,(
% 1.55/0.60    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 1.55/0.60    inference(superposition,[],[f27,f61])).
% 1.55/0.60  fof(f159,plain,(
% 1.55/0.60    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.55/0.60    inference(superposition,[],[f69,f18])).
% 1.55/0.60  fof(f1814,plain,(
% 1.55/0.60    k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(sK1,k2_xboole_0(sK3,sK2))),
% 1.55/0.60    inference(forward_demodulation,[],[f1809,f34])).
% 1.55/0.60  fof(f34,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f11])).
% 1.55/0.60  fof(f11,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.55/0.60  fof(f1809,plain,(
% 1.55/0.60    k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 1.55/0.60    inference(superposition,[],[f27,f1714])).
% 1.55/0.60  fof(f1714,plain,(
% 1.55/0.60    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK1,sK3))),
% 1.55/0.60    inference(forward_demodulation,[],[f1692,f147])).
% 1.55/0.60  fof(f1692,plain,(
% 1.55/0.60    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK3))),
% 1.55/0.60    inference(superposition,[],[f1677,f1091])).
% 1.55/0.60  fof(f1091,plain,(
% 1.55/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 1.55/0.60    inference(superposition,[],[f34,f89])).
% 1.55/0.60  fof(f89,plain,(
% 1.55/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.55/0.60    inference(forward_demodulation,[],[f88,f24])).
% 1.55/0.60  fof(f88,plain,(
% 1.55/0.60    k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.55/0.60    inference(superposition,[],[f27,f75])).
% 1.55/0.60  fof(f75,plain,(
% 1.55/0.60    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.55/0.60    inference(forward_demodulation,[],[f74,f39])).
% 1.55/0.60  fof(f74,plain,(
% 1.55/0.60    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.55/0.60    inference(superposition,[],[f28,f73])).
% 1.55/0.60  fof(f61,plain,(
% 1.55/0.60    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.55/0.60    inference(superposition,[],[f28,f18])).
% 1.55/0.60  % SZS output end Proof for theBenchmark
% 1.55/0.60  % (16324)------------------------------
% 1.55/0.60  % (16324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  % (16324)Termination reason: Refutation
% 1.55/0.60  
% 1.55/0.60  % (16324)Memory used [KB]: 7291
% 1.55/0.60  % (16324)Time elapsed: 0.191 s
% 1.55/0.60  % (16324)------------------------------
% 1.55/0.60  % (16324)------------------------------
% 1.55/0.61  % (16317)Success in time 0.237 s
%------------------------------------------------------------------------------
