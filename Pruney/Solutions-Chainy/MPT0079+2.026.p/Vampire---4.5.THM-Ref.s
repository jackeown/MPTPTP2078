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
% DateTime   : Thu Dec  3 12:30:55 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :  120 (3151 expanded)
%              Number of leaves         :   14 ( 892 expanded)
%              Depth                    :   37
%              Number of atoms          :  146 (5579 expanded)
%              Number of equality atoms :  112 (2870 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1584,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1583,f24])).

fof(f24,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f1583,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f1582,f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1582,plain,(
    sK2 = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1576,f528])).

fof(f528,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f489,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f489,plain,(
    sK2 = k2_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f485,f26])).

fof(f485,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f32,f476])).

fof(f476,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f475,f113])).

fof(f113,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f112,f65])).

fof(f65,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f51,f60])).

fof(f60,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f55,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f55,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f40,f51])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f51,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f45,f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f45,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f44,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f30,f30])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f44,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f22,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f22,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f112,plain,(
    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f33,f110])).

fof(f110,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f54,f60])).

fof(f54,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f41,f51])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f34,f30])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f475,plain,(
    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f466,f166])).

fof(f166,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f102,f29])).

fof(f102,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f37,f98])).

fof(f98,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f52,f94])).

fof(f94,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f89,f25])).

fof(f89,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f40,f52])).

fof(f52,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f47,f27])).

fof(f47,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f46,f39])).

fof(f46,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) ),
    inference(resolution,[],[f23,f43])).

fof(f23,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f466,plain,(
    k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f255,f21])).

fof(f21,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f255,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f99,f29])).

fof(f99,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[],[f37,f94])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1576,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f32,f1570])).

fof(f1570,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f1569,f65])).

fof(f1569,plain,(
    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f1566,f204])).

fof(f204,plain,(
    ! [X4] : k4_xboole_0(sK0,k4_xboole_0(X4,sK2)) = k4_xboole_0(sK0,X4) ),
    inference(forward_demodulation,[],[f194,f66])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f37,f60])).

fof(f194,plain,(
    ! [X4] : k4_xboole_0(sK0,k4_xboole_0(X4,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK2,X4)) ),
    inference(superposition,[],[f66,f32])).

fof(f1566,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f39,f1544])).

fof(f1544,plain,(
    sK1 = k4_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f1437,f1493])).

fof(f1493,plain,(
    sK0 = sK3 ),
    inference(superposition,[],[f1489,f25])).

fof(f1489,plain,(
    sK0 = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1488,f934])).

fof(f934,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f933,f122])).

fof(f122,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f121,f98])).

fof(f121,plain,(
    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f33,f119])).

fof(f119,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f88,f94])).

fof(f88,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f41,f52])).

fof(f933,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f923,f114])).

fof(f114,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f37,f113])).

fof(f923,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f229,f86])).

fof(f86,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f85,f21])).

fof(f85,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f84,f29])).

fof(f84,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f79,f32])).

fof(f79,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f32,f49])).

fof(f49,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f33,f21])).

fof(f229,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[],[f37,f223])).

fof(f223,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK3) ),
    inference(forward_demodulation,[],[f219,f200])).

fof(f200,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f199,f122])).

fof(f199,plain,(
    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f188,f69])).

fof(f69,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f37,f65])).

fof(f188,plain,(
    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f66,f21])).

fof(f219,plain,(
    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[],[f33,f214])).

fof(f214,plain,(
    sK3 = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f213,f26])).

fof(f213,plain,(
    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f210,f29])).

fof(f210,plain,(
    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f32,f200])).

fof(f1488,plain,(
    sK0 = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1487,f487])).

fof(f487,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f482,f25])).

fof(f482,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f204,f476])).

fof(f1487,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1478,f33])).

fof(f1478,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f39,f1446])).

fof(f1446,plain,(
    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(backward_demodulation,[],[f49,f1437])).

fof(f1437,plain,(
    sK1 = k4_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f1436,f94])).

fof(f1436,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f1435,f33])).

fof(f1435,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) ),
    inference(forward_demodulation,[],[f1429,f234])).

fof(f234,plain,(
    sK3 = k2_xboole_0(sK3,sK3) ),
    inference(forward_demodulation,[],[f231,f26])).

fof(f231,plain,(
    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK3) ),
    inference(superposition,[],[f32,f223])).

fof(f1429,plain,(
    k4_xboole_0(sK2,k2_xboole_0(sK3,sK3)) = k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK3,sK3)) ),
    inference(superposition,[],[f128,f743])).

fof(f743,plain,(
    ! [X0] : k2_xboole_0(X0,sK3) = k2_xboole_0(sK0,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f218,f29])).

fof(f218,plain,(
    ! [X0] : k2_xboole_0(sK3,X0) = k2_xboole_0(sK0,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[],[f38,f214])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f128,plain,(
    ! [X2] : k4_xboole_0(sK2,k2_xboole_0(sK3,X2)) = k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,X2)),k2_xboole_0(sK3,X2)) ),
    inference(superposition,[],[f33,f50])).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f48,f38])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[],[f38,f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.21/0.35  % WCLimit    : 600
% 0.21/0.35  % DateTime   : Tue Dec  1 15:57:42 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.50  % (19913)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (19921)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (19908)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.57  % (19928)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.58  % (19920)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.59  % (19899)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.64/0.60  % (19905)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.64/0.60  % (19923)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.64/0.60  % (19919)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.64/0.60  % (19907)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.64/0.60  % (19917)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.64/0.60  % (19927)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.85/0.60  % (19926)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.85/0.61  % (19900)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.85/0.61  % (19925)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.85/0.61  % (19906)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.85/0.61  % (19914)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.85/0.61  % (19914)Refutation not found, incomplete strategy% (19914)------------------------------
% 1.85/0.61  % (19914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.61  % (19914)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.61  
% 1.85/0.61  % (19914)Memory used [KB]: 6140
% 1.85/0.61  % (19914)Time elapsed: 0.001 s
% 1.85/0.61  % (19914)------------------------------
% 1.85/0.61  % (19914)------------------------------
% 1.85/0.61  % (19904)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.85/0.61  % (19903)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.85/0.61  % (19915)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.85/0.62  % (19910)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.85/0.62  % (19912)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.85/0.62  % (19911)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.85/0.62  % (19922)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.85/0.62  % (19918)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.85/0.62  % (19909)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.85/0.63  % (19916)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.85/0.63  % (19902)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.85/0.63  % (19920)Refutation found. Thanks to Tanya!
% 1.85/0.63  % SZS status Theorem for theBenchmark
% 1.85/0.63  % SZS output start Proof for theBenchmark
% 1.85/0.63  fof(f1584,plain,(
% 1.85/0.63    $false),
% 1.85/0.63    inference(subsumption_resolution,[],[f1583,f24])).
% 1.85/0.63  fof(f24,plain,(
% 1.85/0.63    sK1 != sK2),
% 1.85/0.63    inference(cnf_transformation,[],[f18])).
% 1.85/0.63  fof(f18,plain,(
% 1.85/0.63    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.85/0.63    inference(flattening,[],[f17])).
% 1.85/0.63  fof(f17,plain,(
% 1.85/0.63    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.85/0.63    inference(ennf_transformation,[],[f15])).
% 1.85/0.63  fof(f15,negated_conjecture,(
% 1.85/0.63    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.85/0.63    inference(negated_conjecture,[],[f14])).
% 1.85/0.63  fof(f14,conjecture,(
% 1.85/0.63    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.85/0.63  fof(f1583,plain,(
% 1.85/0.63    sK1 = sK2),
% 1.85/0.63    inference(forward_demodulation,[],[f1582,f26])).
% 1.85/0.63  fof(f26,plain,(
% 1.85/0.63    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.85/0.63    inference(cnf_transformation,[],[f5])).
% 1.85/0.63  fof(f5,axiom,(
% 1.85/0.63    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.85/0.63  fof(f1582,plain,(
% 1.85/0.63    sK2 = k2_xboole_0(sK1,k1_xboole_0)),
% 1.85/0.63    inference(forward_demodulation,[],[f1576,f528])).
% 1.85/0.63  fof(f528,plain,(
% 1.85/0.63    sK2 = k2_xboole_0(sK1,sK2)),
% 1.85/0.63    inference(superposition,[],[f489,f29])).
% 1.85/0.63  fof(f29,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f1])).
% 1.85/0.63  fof(f1,axiom,(
% 1.85/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.85/0.63  fof(f489,plain,(
% 1.85/0.63    sK2 = k2_xboole_0(sK2,sK1)),
% 1.85/0.63    inference(forward_demodulation,[],[f485,f26])).
% 1.85/0.63  fof(f485,plain,(
% 1.85/0.63    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)),
% 1.85/0.63    inference(superposition,[],[f32,f476])).
% 1.85/0.63  fof(f476,plain,(
% 1.85/0.63    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.85/0.63    inference(forward_demodulation,[],[f475,f113])).
% 1.85/0.63  fof(f113,plain,(
% 1.85/0.63    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)),
% 1.85/0.63    inference(forward_demodulation,[],[f112,f65])).
% 1.85/0.63  fof(f65,plain,(
% 1.85/0.63    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 1.85/0.63    inference(backward_demodulation,[],[f51,f60])).
% 1.85/0.63  fof(f60,plain,(
% 1.85/0.63    sK0 = k4_xboole_0(sK0,sK2)),
% 1.85/0.63    inference(forward_demodulation,[],[f55,f25])).
% 1.85/0.63  fof(f25,plain,(
% 1.85/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.85/0.63    inference(cnf_transformation,[],[f7])).
% 1.85/0.63  fof(f7,axiom,(
% 1.85/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.85/0.63  fof(f55,plain,(
% 1.85/0.63    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.85/0.63    inference(superposition,[],[f40,f51])).
% 1.85/0.63  fof(f40,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.85/0.63    inference(definition_unfolding,[],[f31,f30])).
% 1.85/0.63  fof(f30,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.85/0.63    inference(cnf_transformation,[],[f11])).
% 1.85/0.63  fof(f11,axiom,(
% 1.85/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.85/0.63  fof(f31,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.85/0.63    inference(cnf_transformation,[],[f10])).
% 1.85/0.63  fof(f10,axiom,(
% 1.85/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.85/0.63  fof(f51,plain,(
% 1.85/0.63    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.85/0.63    inference(resolution,[],[f45,f27])).
% 1.85/0.63  fof(f27,plain,(
% 1.85/0.63    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.85/0.63    inference(cnf_transformation,[],[f19])).
% 1.85/0.63  fof(f19,plain,(
% 1.85/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.85/0.63    inference(ennf_transformation,[],[f4])).
% 1.85/0.63  fof(f4,axiom,(
% 1.85/0.63    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.85/0.63  fof(f45,plain,(
% 1.85/0.63    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) )),
% 1.85/0.63    inference(forward_demodulation,[],[f44,f39])).
% 1.85/0.63  fof(f39,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.85/0.63    inference(definition_unfolding,[],[f28,f30,f30])).
% 1.85/0.63  fof(f28,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f2])).
% 1.85/0.63  fof(f2,axiom,(
% 1.85/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.85/0.63  fof(f44,plain,(
% 1.85/0.63    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))) )),
% 1.85/0.63    inference(resolution,[],[f22,f43])).
% 1.85/0.63  fof(f43,plain,(
% 1.85/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.85/0.63    inference(definition_unfolding,[],[f35,f30])).
% 1.85/0.63  fof(f35,plain,(
% 1.85/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f20])).
% 1.85/0.63  fof(f20,plain,(
% 1.85/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.85/0.63    inference(ennf_transformation,[],[f16])).
% 1.85/0.63  fof(f16,plain,(
% 1.85/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.85/0.63    inference(rectify,[],[f3])).
% 1.85/0.63  fof(f3,axiom,(
% 1.85/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.85/0.63  fof(f22,plain,(
% 1.85/0.63    r1_xboole_0(sK2,sK0)),
% 1.85/0.63    inference(cnf_transformation,[],[f18])).
% 1.85/0.63  fof(f112,plain,(
% 1.85/0.63    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK0,sK0)),
% 1.85/0.63    inference(superposition,[],[f33,f110])).
% 1.85/0.63  fof(f110,plain,(
% 1.85/0.63    sK0 = k2_xboole_0(k1_xboole_0,sK0)),
% 1.85/0.63    inference(forward_demodulation,[],[f54,f60])).
% 1.85/0.63  fof(f54,plain,(
% 1.85/0.63    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))),
% 1.85/0.63    inference(superposition,[],[f41,f51])).
% 1.85/0.63  fof(f41,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.85/0.63    inference(definition_unfolding,[],[f34,f30])).
% 1.85/0.63  fof(f34,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.85/0.63    inference(cnf_transformation,[],[f13])).
% 1.85/0.63  fof(f13,axiom,(
% 1.85/0.63    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.85/0.63  fof(f33,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f8])).
% 1.85/0.63  fof(f8,axiom,(
% 1.85/0.63    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.85/0.63  fof(f475,plain,(
% 1.85/0.63    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK1,sK2)),
% 1.85/0.63    inference(forward_demodulation,[],[f466,f166])).
% 1.85/0.63  fof(f166,plain,(
% 1.85/0.63    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK1))) )),
% 1.85/0.63    inference(superposition,[],[f102,f29])).
% 1.85/0.63  fof(f102,plain,(
% 1.85/0.63    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(sK1,X0))) )),
% 1.85/0.63    inference(superposition,[],[f37,f98])).
% 1.85/0.63  fof(f98,plain,(
% 1.85/0.63    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 1.85/0.63    inference(backward_demodulation,[],[f52,f94])).
% 1.85/0.63  fof(f94,plain,(
% 1.85/0.63    sK1 = k4_xboole_0(sK1,sK3)),
% 1.85/0.63    inference(forward_demodulation,[],[f89,f25])).
% 1.85/0.63  fof(f89,plain,(
% 1.85/0.63    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.85/0.63    inference(superposition,[],[f40,f52])).
% 1.85/0.63  fof(f52,plain,(
% 1.85/0.63    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.85/0.63    inference(resolution,[],[f47,f27])).
% 1.85/0.63  fof(f47,plain,(
% 1.85/0.63    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))) )),
% 1.85/0.63    inference(forward_demodulation,[],[f46,f39])).
% 1.85/0.63  fof(f46,plain,(
% 1.85/0.63    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) )),
% 1.85/0.63    inference(resolution,[],[f23,f43])).
% 1.85/0.63  fof(f23,plain,(
% 1.85/0.63    r1_xboole_0(sK3,sK1)),
% 1.85/0.63    inference(cnf_transformation,[],[f18])).
% 1.85/0.63  fof(f37,plain,(
% 1.85/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.85/0.63    inference(cnf_transformation,[],[f9])).
% 1.85/0.63  fof(f9,axiom,(
% 1.85/0.63    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.85/0.63  fof(f466,plain,(
% 1.85/0.63    k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2)),
% 1.85/0.63    inference(superposition,[],[f255,f21])).
% 1.85/0.63  fof(f21,plain,(
% 1.85/0.63    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.85/0.63    inference(cnf_transformation,[],[f18])).
% 1.85/0.63  fof(f255,plain,(
% 1.85/0.63    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK3))) )),
% 1.85/0.63    inference(superposition,[],[f99,f29])).
% 1.85/0.63  fof(f99,plain,(
% 1.85/0.63    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0)) )),
% 1.85/0.63    inference(superposition,[],[f37,f94])).
% 1.85/0.63  fof(f32,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.85/0.63    inference(cnf_transformation,[],[f6])).
% 1.85/0.63  fof(f6,axiom,(
% 1.85/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.85/0.63  fof(f1576,plain,(
% 1.85/0.63    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2)),
% 1.85/0.63    inference(superposition,[],[f32,f1570])).
% 1.85/0.63  fof(f1570,plain,(
% 1.85/0.63    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.85/0.63    inference(forward_demodulation,[],[f1569,f65])).
% 1.85/0.63  fof(f1569,plain,(
% 1.85/0.63    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK2,sK1)),
% 1.85/0.63    inference(forward_demodulation,[],[f1566,f204])).
% 1.85/0.63  fof(f204,plain,(
% 1.85/0.63    ( ! [X4] : (k4_xboole_0(sK0,k4_xboole_0(X4,sK2)) = k4_xboole_0(sK0,X4)) )),
% 1.85/0.63    inference(forward_demodulation,[],[f194,f66])).
% 1.85/0.63  fof(f66,plain,(
% 1.85/0.63    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) )),
% 1.85/0.63    inference(superposition,[],[f37,f60])).
% 1.85/0.63  fof(f194,plain,(
% 1.85/0.63    ( ! [X4] : (k4_xboole_0(sK0,k4_xboole_0(X4,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK2,X4))) )),
% 1.85/0.63    inference(superposition,[],[f66,f32])).
% 1.85/0.63  fof(f1566,plain,(
% 1.85/0.63    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,sK1)),
% 1.85/0.63    inference(superposition,[],[f39,f1544])).
% 1.85/0.63  fof(f1544,plain,(
% 1.85/0.63    sK1 = k4_xboole_0(sK2,sK0)),
% 1.85/0.63    inference(backward_demodulation,[],[f1437,f1493])).
% 1.85/0.63  fof(f1493,plain,(
% 1.85/0.63    sK0 = sK3),
% 1.85/0.63    inference(superposition,[],[f1489,f25])).
% 1.85/0.63  fof(f1489,plain,(
% 1.85/0.63    sK0 = k4_xboole_0(sK3,k1_xboole_0)),
% 1.85/0.63    inference(forward_demodulation,[],[f1488,f934])).
% 1.85/0.63  fof(f934,plain,(
% 1.85/0.63    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.85/0.63    inference(forward_demodulation,[],[f933,f122])).
% 1.85/0.63  fof(f122,plain,(
% 1.85/0.63    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 1.85/0.63    inference(forward_demodulation,[],[f121,f98])).
% 1.85/0.63  fof(f121,plain,(
% 1.85/0.63    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,sK1)),
% 1.85/0.63    inference(superposition,[],[f33,f119])).
% 1.85/0.63  fof(f119,plain,(
% 1.85/0.63    sK1 = k2_xboole_0(k1_xboole_0,sK1)),
% 1.85/0.63    inference(forward_demodulation,[],[f88,f94])).
% 1.85/0.63  fof(f88,plain,(
% 1.85/0.63    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 1.85/0.63    inference(superposition,[],[f41,f52])).
% 1.85/0.63  fof(f933,plain,(
% 1.85/0.63    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK1)),
% 1.85/0.63    inference(forward_demodulation,[],[f923,f114])).
% 1.85/0.63  fof(f114,plain,(
% 1.85/0.63    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0))) )),
% 1.85/0.63    inference(superposition,[],[f37,f113])).
% 1.85/0.63  fof(f923,plain,(
% 1.85/0.63    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))),
% 1.85/0.63    inference(superposition,[],[f229,f86])).
% 1.85/0.63  fof(f86,plain,(
% 1.85/0.63    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.85/0.63    inference(forward_demodulation,[],[f85,f21])).
% 1.85/0.63  fof(f85,plain,(
% 1.85/0.63    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.85/0.63    inference(forward_demodulation,[],[f84,f29])).
% 1.85/0.63  fof(f84,plain,(
% 1.85/0.63    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.85/0.63    inference(forward_demodulation,[],[f79,f32])).
% 1.85/0.63  fof(f79,plain,(
% 1.85/0.63    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 1.85/0.63    inference(superposition,[],[f32,f49])).
% 1.85/0.63  fof(f49,plain,(
% 1.85/0.63    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.85/0.63    inference(superposition,[],[f33,f21])).
% 1.85/0.63  fof(f229,plain,(
% 1.85/0.63    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(sK3,X0))) )),
% 1.85/0.63    inference(superposition,[],[f37,f223])).
% 1.85/0.63  fof(f223,plain,(
% 1.85/0.63    k1_xboole_0 = k4_xboole_0(sK3,sK3)),
% 1.85/0.63    inference(forward_demodulation,[],[f219,f200])).
% 1.85/0.63  fof(f200,plain,(
% 1.85/0.63    k1_xboole_0 = k4_xboole_0(sK0,sK3)),
% 1.85/0.63    inference(forward_demodulation,[],[f199,f122])).
% 1.85/0.63  fof(f199,plain,(
% 1.85/0.63    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK0,sK3)),
% 1.85/0.63    inference(forward_demodulation,[],[f188,f69])).
% 1.85/0.63  fof(f69,plain,(
% 1.85/0.63    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0))) )),
% 1.85/0.63    inference(superposition,[],[f37,f65])).
% 1.85/0.63  fof(f188,plain,(
% 1.85/0.63    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 1.85/0.63    inference(superposition,[],[f66,f21])).
% 1.85/0.63  fof(f219,plain,(
% 1.85/0.63    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK3,sK3)),
% 1.85/0.63    inference(superposition,[],[f33,f214])).
% 1.85/0.63  fof(f214,plain,(
% 1.85/0.63    sK3 = k2_xboole_0(sK0,sK3)),
% 1.85/0.63    inference(forward_demodulation,[],[f213,f26])).
% 1.85/0.63  fof(f213,plain,(
% 1.85/0.63    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK0,sK3)),
% 1.85/0.63    inference(forward_demodulation,[],[f210,f29])).
% 1.85/0.63  fof(f210,plain,(
% 1.85/0.63    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK0)),
% 1.85/0.63    inference(superposition,[],[f32,f200])).
% 1.85/0.63  fof(f1488,plain,(
% 1.85/0.63    sK0 = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)))),
% 1.85/0.63    inference(forward_demodulation,[],[f1487,f487])).
% 1.85/0.63  fof(f487,plain,(
% 1.85/0.63    sK0 = k4_xboole_0(sK0,sK1)),
% 1.85/0.63    inference(forward_demodulation,[],[f482,f25])).
% 1.85/0.63  fof(f482,plain,(
% 1.85/0.63    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK1)),
% 1.85/0.63    inference(superposition,[],[f204,f476])).
% 1.85/0.63  fof(f1487,plain,(
% 1.85/0.63    k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1)),
% 1.85/0.63    inference(forward_demodulation,[],[f1478,f33])).
% 1.85/0.63  fof(f1478,plain,(
% 1.85/0.63    k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 1.85/0.63    inference(superposition,[],[f39,f1446])).
% 1.85/0.63  fof(f1446,plain,(
% 1.85/0.63    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.85/0.63    inference(backward_demodulation,[],[f49,f1437])).
% 1.85/0.63  fof(f1437,plain,(
% 1.85/0.63    sK1 = k4_xboole_0(sK2,sK3)),
% 1.85/0.63    inference(forward_demodulation,[],[f1436,f94])).
% 1.85/0.63  fof(f1436,plain,(
% 1.85/0.63    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK2,sK3)),
% 1.85/0.63    inference(forward_demodulation,[],[f1435,f33])).
% 1.85/0.63  fof(f1435,plain,(
% 1.85/0.63    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK3)),
% 1.85/0.63    inference(forward_demodulation,[],[f1429,f234])).
% 1.85/0.63  fof(f234,plain,(
% 1.85/0.63    sK3 = k2_xboole_0(sK3,sK3)),
% 1.85/0.63    inference(forward_demodulation,[],[f231,f26])).
% 1.85/0.63  fof(f231,plain,(
% 1.85/0.63    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK3)),
% 1.85/0.63    inference(superposition,[],[f32,f223])).
% 1.85/0.63  fof(f1429,plain,(
% 1.85/0.63    k4_xboole_0(sK2,k2_xboole_0(sK3,sK3)) = k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK3,sK3))),
% 1.85/0.63    inference(superposition,[],[f128,f743])).
% 1.85/0.63  fof(f743,plain,(
% 1.85/0.63    ( ! [X0] : (k2_xboole_0(X0,sK3) = k2_xboole_0(sK0,k2_xboole_0(X0,sK3))) )),
% 1.85/0.63    inference(superposition,[],[f218,f29])).
% 1.85/0.63  fof(f218,plain,(
% 1.85/0.63    ( ! [X0] : (k2_xboole_0(sK3,X0) = k2_xboole_0(sK0,k2_xboole_0(sK3,X0))) )),
% 1.85/0.63    inference(superposition,[],[f38,f214])).
% 1.85/0.63  fof(f38,plain,(
% 1.85/0.63    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.85/0.63    inference(cnf_transformation,[],[f12])).
% 1.85/0.63  fof(f12,axiom,(
% 1.85/0.63    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.85/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.85/0.63  fof(f128,plain,(
% 1.85/0.63    ( ! [X2] : (k4_xboole_0(sK2,k2_xboole_0(sK3,X2)) = k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,X2)),k2_xboole_0(sK3,X2))) )),
% 1.85/0.63    inference(superposition,[],[f33,f50])).
% 1.85/0.63  fof(f50,plain,(
% 1.85/0.63    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0))) )),
% 1.85/0.63    inference(forward_demodulation,[],[f48,f38])).
% 1.85/0.63  fof(f48,plain,(
% 1.85/0.63    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0)) )),
% 1.85/0.63    inference(superposition,[],[f38,f21])).
% 1.85/0.63  % SZS output end Proof for theBenchmark
% 1.85/0.63  % (19920)------------------------------
% 1.85/0.63  % (19920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.63  % (19920)Termination reason: Refutation
% 1.85/0.63  
% 1.85/0.63  % (19920)Memory used [KB]: 2430
% 1.85/0.63  % (19920)Time elapsed: 0.185 s
% 1.85/0.63  % (19920)------------------------------
% 1.85/0.63  % (19920)------------------------------
% 1.85/0.63  % (19916)Refutation not found, incomplete strategy% (19916)------------------------------
% 1.85/0.63  % (19916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.63  % (19916)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.63  
% 1.85/0.63  % (19916)Memory used [KB]: 10618
% 1.85/0.63  % (19916)Time elapsed: 0.163 s
% 1.85/0.63  % (19916)------------------------------
% 1.85/0.63  % (19916)------------------------------
% 1.85/0.63  % (19898)Success in time 0.253 s
%------------------------------------------------------------------------------
