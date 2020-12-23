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
% DateTime   : Thu Dec  3 12:30:52 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  101 (1483 expanded)
%              Number of leaves         :   12 ( 416 expanded)
%              Depth                    :   29
%              Number of atoms          :  123 (2598 expanded)
%              Number of equality atoms :   93 (1649 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1119,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1118,f30])).

fof(f30,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f1118,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f1117,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1117,plain,(
    sK2 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f213,f1115])).

fof(f1115,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f1104,f479])).

fof(f479,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f405,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f405,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK1,X0)) ),
    inference(backward_demodulation,[],[f195,f401])).

fof(f401,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f400,f112])).

fof(f112,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    inference(backward_demodulation,[],[f62,f111])).

fof(f111,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f103,f32])).

fof(f103,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f53,f62])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f62,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f28,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f28,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f400,plain,(
    ! [X4] : k4_xboole_0(sK2,sK2) = k4_xboole_0(k1_xboole_0,X4) ),
    inference(backward_demodulation,[],[f283,f399])).

fof(f399,plain,(
    ! [X0] : sK2 = k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f398,f229])).

fof(f229,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f44,f225])).

fof(f225,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f217,f112])).

fof(f217,plain,(
    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f53,f147])).

fof(f147,plain,(
    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(backward_demodulation,[],[f97,f140])).

fof(f140,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f44,f111])).

fof(f97,plain,(
    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f86,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f86,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f34,f27])).

fof(f27,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f398,plain,(
    ! [X0] : sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f393,f140])).

fof(f393,plain,(
    ! [X0] : sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X0)))) ),
    inference(resolution,[],[f377,f54])).

fof(f377,plain,(
    ! [X1] : r1_tarski(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X1))) ),
    inference(superposition,[],[f34,f96])).

fof(f96,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f88,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f88,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[],[f45,f27])).

fof(f283,plain,(
    ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,X4))) ),
    inference(superposition,[],[f53,f113])).

fof(f113,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) ),
    inference(forward_demodulation,[],[f106,f111])).

fof(f106,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f44,f62])).

fof(f195,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f188,f193])).

fof(f193,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f187,f32])).

fof(f187,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f53,f84])).

fof(f84,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f71,f55])).

fof(f71,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f29,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f188,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) ),
    inference(superposition,[],[f44,f84])).

fof(f1104,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f847,f932])).

fof(f932,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f833,f36])).

fof(f833,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f27,f823])).

fof(f823,plain,(
    sK0 = sK3 ),
    inference(superposition,[],[f820,f32])).

fof(f820,plain,(
    sK0 = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f819,f32])).

fof(f819,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f812,f683])).

fof(f683,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f671,f404])).

fof(f404,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) ),
    inference(backward_demodulation,[],[f172,f401])).

fof(f172,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f165,f170])).

fof(f170,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f164,f32])).

fof(f164,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f53,f78])).

fof(f78,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f63,f55])).

fof(f63,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f28,f41])).

fof(f165,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) ),
    inference(superposition,[],[f44,f78])).

fof(f671,plain,(
    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f178,f27])).

fof(f178,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f44,f170])).

fof(f812,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK3)) ),
    inference(superposition,[],[f52,f800])).

fof(f800,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f362,f509])).

fof(f509,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f410,f27])).

fof(f410,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(X0,sK3)) ),
    inference(backward_demodulation,[],[f300,f401])).

fof(f300,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f134,f36])).

fof(f134,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) ),
    inference(forward_demodulation,[],[f127,f132])).

fof(f132,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f124,f32])).

fof(f124,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f53,f70])).

fof(f70,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f29,f55])).

fof(f127,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) ),
    inference(superposition,[],[f44,f70])).

fof(f362,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f151,f36])).

fof(f151,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f44,f132])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f35,f38,f38])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f847,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
    inference(backward_demodulation,[],[f206,f823])).

fof(f206,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[],[f44,f193])).

fof(f213,plain,(
    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f147,f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:48:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (2321)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.48  % (2314)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (2335)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (2327)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.50  % (2322)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (2309)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (2328)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (2324)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (2313)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (2320)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (2332)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (2315)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (2318)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (2319)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (2329)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (2336)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (2316)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (2334)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (2326)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (2330)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (2311)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (2312)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (2331)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (2310)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (2317)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (2338)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (2333)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (2325)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (2325)Refutation not found, incomplete strategy% (2325)------------------------------
% 0.21/0.55  % (2325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (2337)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.50/0.55  % (2325)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (2325)Memory used [KB]: 10618
% 1.50/0.55  % (2325)Time elapsed: 0.142 s
% 1.50/0.55  % (2325)------------------------------
% 1.50/0.55  % (2325)------------------------------
% 1.50/0.55  % (2323)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.66/0.61  % (2326)Refutation found. Thanks to Tanya!
% 1.66/0.61  % SZS status Theorem for theBenchmark
% 1.66/0.61  % SZS output start Proof for theBenchmark
% 1.66/0.61  fof(f1119,plain,(
% 1.66/0.61    $false),
% 1.66/0.61    inference(subsumption_resolution,[],[f1118,f30])).
% 1.66/0.61  fof(f30,plain,(
% 1.66/0.61    sK1 != sK2),
% 1.66/0.61    inference(cnf_transformation,[],[f21])).
% 1.66/0.61  fof(f21,plain,(
% 1.66/0.61    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.66/0.61    inference(flattening,[],[f20])).
% 1.66/0.61  fof(f20,plain,(
% 1.66/0.61    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.66/0.61    inference(ennf_transformation,[],[f19])).
% 1.66/0.61  fof(f19,negated_conjecture,(
% 1.66/0.61    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.66/0.61    inference(negated_conjecture,[],[f18])).
% 1.66/0.61  fof(f18,conjecture,(
% 1.66/0.61    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.66/0.61  fof(f1118,plain,(
% 1.66/0.61    sK1 = sK2),
% 1.66/0.61    inference(forward_demodulation,[],[f1117,f32])).
% 1.66/0.61  fof(f32,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.66/0.61    inference(cnf_transformation,[],[f9])).
% 1.66/0.61  fof(f9,axiom,(
% 1.66/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.66/0.61  fof(f1117,plain,(
% 1.66/0.61    sK2 = k4_xboole_0(sK1,k1_xboole_0)),
% 1.66/0.61    inference(backward_demodulation,[],[f213,f1115])).
% 1.66/0.61  fof(f1115,plain,(
% 1.66/0.61    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.66/0.61    inference(forward_demodulation,[],[f1104,f479])).
% 1.66/0.61  fof(f479,plain,(
% 1.66/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X0,sK1))) )),
% 1.66/0.61    inference(superposition,[],[f405,f36])).
% 1.66/0.61  fof(f36,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f1])).
% 1.66/0.61  fof(f1,axiom,(
% 1.66/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.66/0.61  fof(f405,plain,(
% 1.66/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK1,X0))) )),
% 1.66/0.61    inference(backward_demodulation,[],[f195,f401])).
% 1.66/0.61  fof(f401,plain,(
% 1.66/0.61    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f400,f112])).
% 1.66/0.61  fof(f112,plain,(
% 1.66/0.61    k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 1.66/0.61    inference(backward_demodulation,[],[f62,f111])).
% 1.66/0.61  fof(f111,plain,(
% 1.66/0.61    sK2 = k4_xboole_0(sK2,sK0)),
% 1.66/0.61    inference(forward_demodulation,[],[f103,f32])).
% 1.66/0.61  fof(f103,plain,(
% 1.66/0.61    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.66/0.61    inference(superposition,[],[f53,f62])).
% 1.66/0.61  fof(f53,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.66/0.61    inference(definition_unfolding,[],[f37,f38])).
% 1.66/0.61  fof(f38,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f12])).
% 1.66/0.61  fof(f12,axiom,(
% 1.66/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.66/0.61  fof(f37,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f11])).
% 1.66/0.61  fof(f11,axiom,(
% 1.66/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.66/0.61  fof(f62,plain,(
% 1.66/0.61    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.66/0.61    inference(resolution,[],[f28,f55])).
% 1.66/0.61  fof(f55,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.66/0.61    inference(definition_unfolding,[],[f43,f38])).
% 1.66/0.61  fof(f43,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f3])).
% 1.66/0.61  fof(f3,axiom,(
% 1.66/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.66/0.61  fof(f28,plain,(
% 1.66/0.61    r1_xboole_0(sK2,sK0)),
% 1.66/0.61    inference(cnf_transformation,[],[f21])).
% 1.66/0.61  fof(f400,plain,(
% 1.66/0.61    ( ! [X4] : (k4_xboole_0(sK2,sK2) = k4_xboole_0(k1_xboole_0,X4)) )),
% 1.66/0.61    inference(backward_demodulation,[],[f283,f399])).
% 1.66/0.61  fof(f399,plain,(
% 1.66/0.61    ( ! [X0] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f398,f229])).
% 1.66/0.61  fof(f229,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK1,X0))) )),
% 1.66/0.61    inference(superposition,[],[f44,f225])).
% 1.66/0.61  fof(f225,plain,(
% 1.66/0.61    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.66/0.61    inference(forward_demodulation,[],[f217,f112])).
% 1.66/0.61  fof(f217,plain,(
% 1.66/0.61    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK1)),
% 1.66/0.61    inference(superposition,[],[f53,f147])).
% 1.66/0.61  fof(f147,plain,(
% 1.66/0.61    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 1.66/0.61    inference(backward_demodulation,[],[f97,f140])).
% 1.66/0.61  fof(f140,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 1.66/0.61    inference(superposition,[],[f44,f111])).
% 1.66/0.61  fof(f97,plain,(
% 1.66/0.61    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)))),
% 1.66/0.61    inference(resolution,[],[f86,f54])).
% 1.66/0.61  fof(f54,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.66/0.61    inference(definition_unfolding,[],[f40,f38])).
% 1.66/0.61  fof(f40,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.66/0.61    inference(cnf_transformation,[],[f22])).
% 1.66/0.61  fof(f22,plain,(
% 1.66/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.66/0.61    inference(ennf_transformation,[],[f7])).
% 1.66/0.61  fof(f7,axiom,(
% 1.66/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.66/0.61  fof(f86,plain,(
% 1.66/0.61    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 1.66/0.61    inference(superposition,[],[f34,f27])).
% 1.66/0.61  fof(f27,plain,(
% 1.66/0.61    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.66/0.61    inference(cnf_transformation,[],[f21])).
% 1.66/0.61  fof(f34,plain,(
% 1.66/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f17])).
% 1.66/0.61  fof(f17,axiom,(
% 1.66/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.66/0.61  fof(f44,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f10])).
% 1.66/0.61  fof(f10,axiom,(
% 1.66/0.61    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.66/0.61  fof(f398,plain,(
% 1.66/0.61    ( ! [X0] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK1,X0)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f393,f140])).
% 1.66/0.61  fof(f393,plain,(
% 1.66/0.61    ( ! [X0] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X0))))) )),
% 1.66/0.61    inference(resolution,[],[f377,f54])).
% 1.66/0.61  fof(f377,plain,(
% 1.66/0.61    ( ! [X1] : (r1_tarski(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X1)))) )),
% 1.66/0.61    inference(superposition,[],[f34,f96])).
% 1.66/0.61  fof(f96,plain,(
% 1.66/0.61    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f88,f45])).
% 1.66/0.61  fof(f45,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f13])).
% 1.66/0.61  fof(f13,axiom,(
% 1.66/0.61    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.66/0.61  fof(f88,plain,(
% 1.66/0.61    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0)) )),
% 1.66/0.61    inference(superposition,[],[f45,f27])).
% 1.66/0.61  fof(f283,plain,(
% 1.66/0.61    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,X4)))) )),
% 1.66/0.61    inference(superposition,[],[f53,f113])).
% 1.66/0.61  fof(f113,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK2,X0))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f106,f111])).
% 1.66/0.61  fof(f106,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.66/0.61    inference(superposition,[],[f44,f62])).
% 1.66/0.61  fof(f195,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(sK1,X0))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f188,f193])).
% 1.66/0.61  fof(f193,plain,(
% 1.66/0.61    sK1 = k4_xboole_0(sK1,sK3)),
% 1.66/0.61    inference(forward_demodulation,[],[f187,f32])).
% 1.66/0.61  fof(f187,plain,(
% 1.66/0.61    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.66/0.61    inference(superposition,[],[f53,f84])).
% 1.66/0.61  fof(f84,plain,(
% 1.66/0.61    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.66/0.61    inference(resolution,[],[f71,f55])).
% 1.66/0.61  fof(f71,plain,(
% 1.66/0.61    r1_xboole_0(sK1,sK3)),
% 1.66/0.61    inference(resolution,[],[f29,f41])).
% 1.66/0.61  fof(f41,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f23])).
% 1.66/0.61  fof(f23,plain,(
% 1.66/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.66/0.61    inference(ennf_transformation,[],[f4])).
% 1.66/0.61  fof(f4,axiom,(
% 1.66/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.66/0.61  fof(f29,plain,(
% 1.66/0.61    r1_xboole_0(sK3,sK1)),
% 1.66/0.61    inference(cnf_transformation,[],[f21])).
% 1.66/0.61  fof(f188,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0))) )),
% 1.66/0.61    inference(superposition,[],[f44,f84])).
% 1.66/0.61  fof(f1104,plain,(
% 1.66/0.61    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 1.66/0.61    inference(superposition,[],[f847,f932])).
% 1.66/0.61  fof(f932,plain,(
% 1.66/0.61    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2)),
% 1.66/0.61    inference(superposition,[],[f833,f36])).
% 1.66/0.61  fof(f833,plain,(
% 1.66/0.61    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0)),
% 1.66/0.61    inference(backward_demodulation,[],[f27,f823])).
% 1.66/0.61  fof(f823,plain,(
% 1.66/0.61    sK0 = sK3),
% 1.66/0.61    inference(superposition,[],[f820,f32])).
% 1.66/0.61  fof(f820,plain,(
% 1.66/0.61    sK0 = k4_xboole_0(sK3,k1_xboole_0)),
% 1.66/0.61    inference(forward_demodulation,[],[f819,f32])).
% 1.66/0.61  fof(f819,plain,(
% 1.66/0.61    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.66/0.61    inference(forward_demodulation,[],[f812,f683])).
% 1.66/0.61  fof(f683,plain,(
% 1.66/0.61    k1_xboole_0 = k4_xboole_0(sK0,sK3)),
% 1.66/0.61    inference(forward_demodulation,[],[f671,f404])).
% 1.66/0.61  fof(f404,plain,(
% 1.66/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,X0))) )),
% 1.66/0.61    inference(backward_demodulation,[],[f172,f401])).
% 1.66/0.61  fof(f172,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f165,f170])).
% 1.66/0.61  fof(f170,plain,(
% 1.66/0.61    sK0 = k4_xboole_0(sK0,sK2)),
% 1.66/0.61    inference(forward_demodulation,[],[f164,f32])).
% 1.66/0.61  fof(f164,plain,(
% 1.66/0.61    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.66/0.61    inference(superposition,[],[f53,f78])).
% 1.66/0.61  fof(f78,plain,(
% 1.66/0.61    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.66/0.61    inference(resolution,[],[f63,f55])).
% 1.66/0.61  fof(f63,plain,(
% 1.66/0.61    r1_xboole_0(sK0,sK2)),
% 1.66/0.61    inference(resolution,[],[f28,f41])).
% 1.66/0.61  fof(f165,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0))) )),
% 1.66/0.61    inference(superposition,[],[f44,f78])).
% 1.66/0.61  fof(f671,plain,(
% 1.66/0.61    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 1.66/0.61    inference(superposition,[],[f178,f27])).
% 1.66/0.61  fof(f178,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) )),
% 1.66/0.61    inference(superposition,[],[f44,f170])).
% 1.66/0.61  fof(f812,plain,(
% 1.66/0.61    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK3))),
% 1.66/0.61    inference(superposition,[],[f52,f800])).
% 1.66/0.61  fof(f800,plain,(
% 1.66/0.61    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 1.66/0.61    inference(superposition,[],[f362,f509])).
% 1.66/0.61  fof(f509,plain,(
% 1.66/0.61    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.66/0.61    inference(superposition,[],[f410,f27])).
% 1.66/0.61  fof(f410,plain,(
% 1.66/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(X0,sK3))) )),
% 1.66/0.61    inference(backward_demodulation,[],[f300,f401])).
% 1.66/0.61  fof(f300,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK3))) )),
% 1.66/0.61    inference(superposition,[],[f134,f36])).
% 1.66/0.61  fof(f134,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(sK3,X0))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f127,f132])).
% 1.66/0.61  fof(f132,plain,(
% 1.66/0.61    sK3 = k4_xboole_0(sK3,sK1)),
% 1.66/0.61    inference(forward_demodulation,[],[f124,f32])).
% 1.66/0.61  fof(f124,plain,(
% 1.66/0.61    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 1.66/0.61    inference(superposition,[],[f53,f70])).
% 1.66/0.61  fof(f70,plain,(
% 1.66/0.61    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.66/0.61    inference(resolution,[],[f29,f55])).
% 1.66/0.61  fof(f127,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0))) )),
% 1.66/0.61    inference(superposition,[],[f44,f70])).
% 1.66/0.61  fof(f362,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1))) )),
% 1.66/0.61    inference(superposition,[],[f151,f36])).
% 1.66/0.61  fof(f151,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(sK1,X0))) )),
% 1.66/0.61    inference(superposition,[],[f44,f132])).
% 1.66/0.61  fof(f52,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.66/0.61    inference(definition_unfolding,[],[f35,f38,f38])).
% 1.66/0.61  fof(f35,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f2])).
% 1.66/0.61  fof(f2,axiom,(
% 1.66/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.66/0.61  fof(f847,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK0,X0))) )),
% 1.66/0.61    inference(backward_demodulation,[],[f206,f823])).
% 1.66/0.61  fof(f206,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0)) )),
% 1.66/0.61    inference(superposition,[],[f44,f193])).
% 1.66/0.61  fof(f213,plain,(
% 1.66/0.61    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.66/0.61    inference(superposition,[],[f147,f52])).
% 1.66/0.61  % SZS output end Proof for theBenchmark
% 1.66/0.61  % (2326)------------------------------
% 1.66/0.61  % (2326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (2326)Termination reason: Refutation
% 1.66/0.61  
% 1.66/0.61  % (2326)Memory used [KB]: 2302
% 1.66/0.61  % (2326)Time elapsed: 0.192 s
% 1.66/0.61  % (2326)------------------------------
% 1.66/0.61  % (2326)------------------------------
% 1.66/0.61  % (2308)Success in time 0.25 s
%------------------------------------------------------------------------------
