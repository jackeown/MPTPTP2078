%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:57 EST 2020

% Result     : Theorem 5.11s
% Output     : Refutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :  324 (1323881 expanded)
%              Number of leaves         :   14 (402129 expanded)
%              Depth                    :   81
%              Number of atoms          :  351 (2386712 expanded)
%              Number of equality atoms :  330 (1640784 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9599,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9598,f23])).

fof(f23,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

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

fof(f9598,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f9588,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f9588,plain,(
    sK2 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f7924,f9572])).

fof(f9572,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f8519,f9474])).

fof(f9474,plain,(
    sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f7933,f9247])).

fof(f9247,plain,(
    sK0 = sK3 ),
    inference(forward_demodulation,[],[f9222,f25])).

fof(f9222,plain,(
    sK3 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f6388,f9202])).

fof(f9202,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f7806,f9201])).

fof(f9201,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f9193,f7853])).

fof(f7853,plain,(
    sK2 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f7852,f25])).

fof(f7852,plain,(
    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f7843,f7606])).

fof(f7606,plain,(
    k4_xboole_0(sK1,sK0) = k3_xboole_0(sK2,k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f6049,f7515])).

fof(f7515,plain,(
    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f6482,f7496])).

fof(f7496,plain,(
    sK0 = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f7488,f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f7488,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f29,f7467])).

fof(f7467,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(forward_demodulation,[],[f7454,f5879])).

fof(f5879,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK3) ),
    inference(backward_demodulation,[],[f2481,f5876])).

fof(f5876,plain,(
    sK3 = k4_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f4696,f5875])).

fof(f5875,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f5862,f4746])).

fof(f4746,plain,(
    sK3 = k3_xboole_0(sK3,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4739,f25])).

fof(f4739,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f28,f4712])).

fof(f4712,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4705,f38])).

fof(f38,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f22,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f22,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f4705,plain,(
    k3_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f28,f4696])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f5862,plain,(
    k4_xboole_0(sK3,sK1) = k3_xboole_0(sK3,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f2719,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f2719,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k3_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK0,sK1),X0)) ),
    inference(superposition,[],[f34,f2686])).

fof(f2686,plain,(
    sK3 = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2683,f25])).

fof(f2683,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f779,f2681])).

fof(f2681,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2679,f266])).

fof(f266,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f264,f25])).

fof(f264,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f28,f255])).

fof(f255,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f254,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f254,plain,(
    k4_xboole_0(k1_xboole_0,sK1) = k3_xboole_0(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f247,f24])).

fof(f247,plain,(
    k4_xboole_0(k1_xboole_0,sK1) = k3_xboole_0(sK3,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f65,f25])).

fof(f65,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X0)) = k3_xboole_0(sK3,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f40,f28])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(sK3,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f34,f38])).

fof(f2679,plain,(
    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f53,f2678])).

fof(f2678,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k2_xboole_0(sK0,X2),k2_xboole_0(sK0,X2)) ),
    inference(forward_demodulation,[],[f2675,f2015])).

fof(f2015,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f129,f2010])).

fof(f2010,plain,(
    ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k3_xboole_0(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f2007,f1066])).

fof(f1066,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,X2) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),k4_xboole_0(k1_xboole_0,X2)) ),
    inference(backward_demodulation,[],[f852,f1059])).

fof(f1059,plain,(
    ! [X5] : k3_xboole_0(k1_xboole_0,X5) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X5)) ),
    inference(forward_demodulation,[],[f1055,f28])).

fof(f1055,plain,(
    ! [X5] : k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X5)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5)) ),
    inference(superposition,[],[f28,f1027])).

fof(f1027,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
    inference(backward_demodulation,[],[f992,f1026])).

fof(f1026,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(forward_demodulation,[],[f1023,f34])).

fof(f1023,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k4_xboole_0(k3_xboole_0(sK0,sK0),X0)) ),
    inference(superposition,[],[f34,f1008])).

fof(f1008,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK0)) ),
    inference(forward_demodulation,[],[f993,f125])).

fof(f125,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f124,f24])).

fof(f124,plain,(
    k4_xboole_0(k1_xboole_0,sK0) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f119,f24])).

fof(f119,plain,(
    k3_xboole_0(sK2,k3_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[],[f57,f25])).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0)) = k3_xboole_0(sK2,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f39,f28])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(sK2,k4_xboole_0(sK0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f34,f37])).

fof(f37,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f21,f32])).

fof(f21,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f993,plain,(
    k4_xboole_0(k1_xboole_0,sK0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f150,f144])).

fof(f144,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,sK0)) ),
    inference(forward_demodulation,[],[f138,f129])).

fof(f138,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,sK0)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X3)) ),
    inference(superposition,[],[f129,f29])).

fof(f150,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f132,f28])).

fof(f132,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f34,f131])).

fof(f131,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f130,f25])).

fof(f130,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[],[f28,f125])).

fof(f992,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[],[f150,f28])).

fof(f852,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)) = k2_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)),k4_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f846,f26])).

fof(f846,plain,(
    ! [X2] : k2_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)),k1_xboole_0) = k2_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)),k4_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f29,f156])).

fof(f156,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X3))) ),
    inference(backward_demodulation,[],[f133,f155])).

fof(f155,plain,(
    ! [X0] : k3_xboole_0(sK2,k3_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
    inference(backward_demodulation,[],[f57,f150])).

fof(f133,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k3_xboole_0(sK0,X3))) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(backward_demodulation,[],[f123,f132])).

fof(f123,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X3)) = k4_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k3_xboole_0(sK0,X3))) ),
    inference(superposition,[],[f28,f57])).

fof(f2007,plain,(
    ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X4),k4_xboole_0(k1_xboole_0,X4)) ),
    inference(backward_demodulation,[],[f1924,f1995])).

fof(f1995,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f35,f1981])).

fof(f1981,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f1977,f125])).

fof(f1977,plain,(
    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f31,f1968])).

fof(f1968,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f1967,f25])).

fof(f1967,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f1953,f29])).

fof(f1953,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f1694,f24])).

fof(f1694,plain,(
    ! [X1] : k4_xboole_0(sK0,X1) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k4_xboole_0(sK0,X1)) ),
    inference(superposition,[],[f1063,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1063,plain,(
    ! [X2] : k4_xboole_0(sK0,X2) = k2_xboole_0(k4_xboole_0(sK0,X2),k3_xboole_0(k1_xboole_0,X2)) ),
    inference(backward_demodulation,[],[f157,f1059])).

fof(f157,plain,(
    ! [X2] : k4_xboole_0(sK0,X2) = k2_xboole_0(k4_xboole_0(sK0,X2),k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2))) ),
    inference(backward_demodulation,[],[f128,f155])).

fof(f128,plain,(
    ! [X2] : k4_xboole_0(sK0,X2) = k2_xboole_0(k4_xboole_0(sK0,X2),k3_xboole_0(sK2,k3_xboole_0(sK0,X2))) ),
    inference(forward_demodulation,[],[f122,f26])).

fof(f122,plain,(
    ! [X2] : k2_xboole_0(k4_xboole_0(sK0,X2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,X2),k3_xboole_0(sK2,k3_xboole_0(sK0,X2))) ),
    inference(superposition,[],[f29,f57])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1924,plain,(
    ! [X4] : k4_xboole_0(sK0,k2_xboole_0(sK0,X4)) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X4),k4_xboole_0(sK0,k2_xboole_0(sK0,X4))) ),
    inference(superposition,[],[f1694,f148])).

fof(f148,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X3)) = k3_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f141,f28])).

fof(f141,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X3)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) ),
    inference(superposition,[],[f28,f129])).

fof(f129,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f35,f125])).

fof(f2675,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X2)) = k4_xboole_0(k2_xboole_0(sK0,X2),k2_xboole_0(sK0,X2)) ),
    inference(superposition,[],[f31,f1976])).

fof(f1976,plain,(
    ! [X0] : k2_xboole_0(sK0,X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f36,f1968])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f53,plain,(
    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f31,f43])).

fof(f43,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f30,f20])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f779,plain,(
    k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK3,k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f28,f76])).

fof(f76,plain,(
    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f73,f53])).

fof(f73,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f31,f51])).

fof(f51,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f50,f20])).

fof(f50,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f49,f27])).

fof(f49,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f46,f29])).

fof(f46,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f29,f42])).

fof(f42,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f31,f20])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f4696,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f4687,f31])).

fof(f4687,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f31,f4670])).

fof(f4670,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f4663,f2313])).

fof(f2313,plain,(
    ! [X3] : k2_xboole_0(X3,X3) = X3 ),
    inference(superposition,[],[f30,f2280])).

fof(f2280,plain,(
    ! [X6] : k2_xboole_0(X6,k3_xboole_0(k1_xboole_0,X6)) = X6 ),
    inference(forward_demodulation,[],[f2237,f26])).

fof(f2237,plain,(
    ! [X6] : k2_xboole_0(X6,k1_xboole_0) = k2_xboole_0(X6,k3_xboole_0(k1_xboole_0,X6)) ),
    inference(superposition,[],[f29,f2010])).

fof(f4663,plain,(
    k2_xboole_0(sK3,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f4472,f44])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f41,f36])).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[],[f36,f20])).

fof(f4472,plain,(
    ! [X1] : k2_xboole_0(X1,sK1) = k2_xboole_0(sK2,k2_xboole_0(X1,sK1)) ),
    inference(superposition,[],[f4138,f27])).

fof(f4138,plain,(
    ! [X5] : k2_xboole_0(sK1,X5) = k2_xboole_0(sK2,k2_xboole_0(sK1,X5)) ),
    inference(forward_demodulation,[],[f4137,f2030])).

fof(f2030,plain,(
    ! [X2] : k2_xboole_0(sK1,X2) = k2_xboole_0(k2_xboole_0(sK1,X2),k3_xboole_0(k1_xboole_0,X2)) ),
    inference(backward_demodulation,[],[f296,f2010])).

fof(f296,plain,(
    ! [X2] : k2_xboole_0(sK1,X2) = k2_xboole_0(k2_xboole_0(sK1,X2),k4_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f288,f26])).

fof(f288,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(sK1,X2),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK1,X2),k4_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f29,f263])).

fof(f263,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f35,f255])).

fof(f4137,plain,(
    ! [X5] : k2_xboole_0(k2_xboole_0(sK1,X5),k3_xboole_0(k1_xboole_0,X5)) = k2_xboole_0(sK2,k2_xboole_0(sK1,X5)) ),
    inference(forward_demodulation,[],[f4123,f27])).

fof(f4123,plain,(
    ! [X5] : k2_xboole_0(k2_xboole_0(sK1,X5),k3_xboole_0(k1_xboole_0,X5)) = k2_xboole_0(k2_xboole_0(sK1,X5),sK2) ),
    inference(superposition,[],[f29,f4072])).

fof(f4072,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f4065,f2010])).

fof(f4065,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f35,f4048])).

fof(f4048,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f4047,f266])).

fof(f4047,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f4035,f2011])).

fof(f2011,plain,(
    ! [X0] : k3_xboole_0(sK2,k4_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f39,f2010])).

fof(f4035,plain,(
    k4_xboole_0(sK2,sK1) = k3_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f2713,f31])).

fof(f2713,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k3_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK0,sK1),X0)) ),
    inference(superposition,[],[f34,f2699])).

fof(f2699,plain,(
    sK2 = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2693,f25])).

fof(f2693,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f28,f2681])).

fof(f2481,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2480,f266])).

fof(f2480,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2478,f1060])).

fof(f1060,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f150,f1059])).

fof(f2478,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f31,f1950])).

fof(f1950,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f1694,f266])).

fof(f7454,plain,(
    k4_xboole_0(sK3,sK0) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[],[f7243,f5876])).

fof(f7243,plain,(
    ! [X8] : k4_xboole_0(sK3,X8) = k4_xboole_0(sK3,k4_xboole_0(X8,sK1)) ),
    inference(forward_demodulation,[],[f7200,f5912])).

fof(f5912,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f35,f5875])).

fof(f7200,plain,(
    ! [X8] : k4_xboole_0(sK3,k4_xboole_0(X8,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK1,X8)) ),
    inference(superposition,[],[f5912,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f6482,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK3)) ),
    inference(backward_demodulation,[],[f4899,f6463])).

fof(f6463,plain,(
    ! [X2] : k4_xboole_0(sK2,k2_xboole_0(X2,sK3)) = k4_xboole_0(sK2,X2) ),
    inference(superposition,[],[f6043,f27])).

fof(f6043,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f35,f5993])).

fof(f5993,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(backward_demodulation,[],[f4302,f5991])).

fof(f5991,plain,(
    sK2 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f5986,f25])).

fof(f5986,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,sK3) ),
    inference(backward_demodulation,[],[f4366,f5982])).

fof(f5982,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f5966,f266])).

fof(f5966,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k3_xboole_0(sK2,sK3) ),
    inference(superposition,[],[f2011,f5876])).

fof(f4366,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK2,k3_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f4365,f4302])).

fof(f4365,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k3_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f4359,f4101])).

fof(f4101,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k3_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f34,f4079])).

fof(f4079,plain,(
    sK2 = k3_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f4067,f25])).

fof(f4067,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f28,f4048])).

fof(f4359,plain,(
    k3_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK2,k3_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f28,f4319])).

fof(f4319,plain,(
    k3_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f28,f4302])).

fof(f4302,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(backward_demodulation,[],[f42,f4282])).

fof(f4282,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f31,f4261])).

fof(f4261,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f4260,f2346])).

fof(f2346,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f2338,f20])).

fof(f2338,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f84,f2313])).

fof(f84,plain,(
    ! [X0] : k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f44,f27])).

fof(f4260,plain,(
    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f4259,f26])).

fof(f4259,plain,(
    k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) = k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f4245,f27])).

fof(f4245,plain,(
    k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK1,sK3),sK0) ),
    inference(superposition,[],[f29,f4196])).

fof(f4196,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(backward_demodulation,[],[f3206,f4193])).

fof(f4193,plain,(
    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK3)) ),
    inference(backward_demodulation,[],[f3055,f4174])).

fof(f4174,plain,(
    k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f4088,f20])).

fof(f4088,plain,(
    ! [X0] : k2_xboole_0(sK1,X0) = k2_xboole_0(sK1,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f36,f4073])).

fof(f4073,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f4066,f26])).

fof(f4066,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f29,f4048])).

fof(f3055,plain,(
    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3054,f266])).

fof(f3054,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3053,f339])).

fof(f339,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,X3) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X3,sK1)) ),
    inference(forward_demodulation,[],[f333,f28])).

fof(f333,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X3,sK1)) ),
    inference(superposition,[],[f28,f279])).

fof(f279,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f263,f27])).

fof(f3053,plain,(
    k3_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f799,f3052])).

fof(f3052,plain,(
    ! [X6,X7] : k3_xboole_0(k1_xboole_0,k2_xboole_0(X6,X7)) = k4_xboole_0(sK0,k2_xboole_0(X6,k2_xboole_0(sK0,X7))) ),
    inference(forward_demodulation,[],[f3051,f36])).

fof(f3051,plain,(
    ! [X6,X7] : k3_xboole_0(k1_xboole_0,k2_xboole_0(X6,X7)) = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X6,sK0),X7)) ),
    inference(forward_demodulation,[],[f3050,f2251])).

fof(f2251,plain,(
    ! [X4,X5] : k3_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f2250,f2010])).

fof(f2250,plain,(
    ! [X4,X5] : k4_xboole_0(k1_xboole_0,k2_xboole_0(X4,X5)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f2236,f34])).

% (5892)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
fof(f2236,plain,(
    ! [X4,X5] : k4_xboole_0(k1_xboole_0,k2_xboole_0(X4,X5)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X4),X5) ),
    inference(superposition,[],[f35,f2010])).

fof(f3050,plain,(
    ! [X6,X7] : k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X6,sK0),X7)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f3039,f34])).

fof(f3039,plain,(
    ! [X6,X7] : k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X6,sK0),X7)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X6),X7) ),
    inference(superposition,[],[f35,f2838])).

fof(f2838,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK0)) ),
    inference(superposition,[],[f2154,f27])).

fof(f2154,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) ),
    inference(backward_demodulation,[],[f1995,f2010])).

fof(f799,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f31,f92])).

fof(f92,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f83,f43])).

fof(f83,plain,(
    k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f44,f51])).

fof(f3206,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK3)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f31,f2346])).

fof(f4899,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK1,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f4326,f27])).

fof(f4326,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) ),
    inference(forward_demodulation,[],[f4317,f35])).

fof(f4317,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(k4_xboole_0(sK1,sK3),X0) ),
    inference(superposition,[],[f35,f4302])).

fof(f6049,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k3_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(backward_demodulation,[],[f4327,f6047])).

fof(f6047,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) ),
    inference(backward_demodulation,[],[f4326,f6043])).

fof(f4327,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k3_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK3,X0))) ),
    inference(backward_demodulation,[],[f4036,f4326])).

fof(f4036,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k3_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,X0))) ),
    inference(superposition,[],[f2713,f48])).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(forward_demodulation,[],[f45,f35])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X0)) = k4_xboole_0(k4_xboole_0(sK2,sK3),X0) ),
    inference(superposition,[],[f35,f42])).

fof(f7843,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f28,f7621])).

fof(f7621,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f7615,f37])).

fof(f7615,plain,(
    k3_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f28,f7515])).

fof(f9193,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f9191,f34])).

fof(f9191,plain,(
    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f9183,f1981])).

fof(f9183,plain,(
    k4_xboole_0(sK0,sK0) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f31,f9141])).

fof(f9141,plain,(
    sK0 = k2_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f30,f9102])).

fof(f9102,plain,(
    sK0 = k2_xboole_0(k3_xboole_0(sK0,sK1),sK3) ),
    inference(backward_demodulation,[],[f6437,f9101])).

fof(f9101,plain,(
    sK0 = k2_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f9075,f2313])).

fof(f9075,plain,(
    k2_xboole_0(sK0,sK0) = k2_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f7517,f7503])).

fof(f7503,plain,(
    sK0 = k2_xboole_0(sK3,k3_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f6387,f7496])).

fof(f6387,plain,(
    k2_xboole_0(sK0,sK3) = k2_xboole_0(sK3,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f6372,f27])).

fof(f6372,plain,(
    k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f29,f5978])).

fof(f5978,plain,(
    k4_xboole_0(sK0,sK3) = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f28,f5876])).

fof(f7517,plain,(
    ! [X0] : k2_xboole_0(sK0,X0) = k2_xboole_0(sK0,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[],[f36,f7496])).

fof(f6437,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k2_xboole_0(k3_xboole_0(sK0,sK1),sK3) ),
    inference(forward_demodulation,[],[f6429,f27])).

fof(f6429,plain,(
    k2_xboole_0(k3_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f29,f6388])).

fof(f7806,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f7793,f5978])).

fof(f7793,plain,(
    k4_xboole_0(sK0,sK3) = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f28,f7770])).

fof(f7770,plain,(
    sK3 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f7760,f7220])).

fof(f7220,plain,(
    sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f4344,f7219])).

fof(f7219,plain,(
    sK3 = k4_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f7194,f5875])).

fof(f7194,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f5912,f4073])).

fof(f4344,plain,(
    k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f31,f4333])).

fof(f4333,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f4332,f4261])).

fof(f4332,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f4331,f27])).

fof(f4331,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f4318,f29])).

fof(f4318,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f29,f4302])).

fof(f7760,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f31,f7523])).

fof(f7523,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f7514,f3120])).

fof(f3120,plain,(
    ! [X1] : k2_xboole_0(sK0,X1) = k2_xboole_0(sK0,k2_xboole_0(X1,sK0)) ),
    inference(superposition,[],[f2875,f36])).

fof(f2875,plain,(
    ! [X7] : k2_xboole_0(sK0,X7) = k2_xboole_0(k2_xboole_0(sK0,X7),sK0) ),
    inference(forward_demodulation,[],[f2852,f2019])).

fof(f2019,plain,(
    ! [X2] : k2_xboole_0(sK0,X2) = k2_xboole_0(k2_xboole_0(sK0,X2),k3_xboole_0(k1_xboole_0,X2)) ),
    inference(backward_demodulation,[],[f147,f2010])).

fof(f147,plain,(
    ! [X2] : k2_xboole_0(sK0,X2) = k2_xboole_0(k2_xboole_0(sK0,X2),k4_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f140,f26])).

fof(f140,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(sK0,X2),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK0,X2),k4_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f29,f129])).

fof(f2852,plain,(
    ! [X7] : k2_xboole_0(k2_xboole_0(sK0,X7),sK0) = k2_xboole_0(k2_xboole_0(sK0,X7),k3_xboole_0(k1_xboole_0,X7)) ),
    inference(superposition,[],[f29,f2154])).

fof(f7514,plain,(
    k2_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f5420,f7496])).

fof(f5420,plain,(
    ! [X5] : k2_xboole_0(sK0,k2_xboole_0(sK1,X5)) = k2_xboole_0(k2_xboole_0(X5,sK3),sK2) ),
    inference(forward_demodulation,[],[f5419,f4299])).

fof(f4299,plain,(
    ! [X2] : k2_xboole_0(sK0,k2_xboole_0(sK1,X2)) = k2_xboole_0(sK1,k2_xboole_0(X2,sK3)) ),
    inference(backward_demodulation,[],[f4176,f4295])).

fof(f4295,plain,(
    ! [X1] : k2_xboole_0(sK0,k2_xboole_0(sK1,X1)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK1,X1))) ),
    inference(backward_demodulation,[],[f4175,f4292])).

fof(f4292,plain,(
    ! [X0] : k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,k2_xboole_0(sK3,X0)) ),
    inference(forward_demodulation,[],[f4281,f36])).

fof(f4281,plain,(
    ! [X0] : k2_xboole_0(k2_xboole_0(sK0,sK1),X0) = k2_xboole_0(sK1,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[],[f36,f4261])).

fof(f4175,plain,(
    ! [X1] : k2_xboole_0(sK1,k2_xboole_0(sK3,X1)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK1,X1))) ),
    inference(superposition,[],[f4088,f44])).

fof(f4176,plain,(
    ! [X2] : k2_xboole_0(sK1,k2_xboole_0(X2,sK3)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK1,X2))) ),
    inference(superposition,[],[f4088,f84])).

fof(f5419,plain,(
    ! [X5] : k2_xboole_0(k2_xboole_0(X5,sK3),sK2) = k2_xboole_0(sK1,k2_xboole_0(X5,sK3)) ),
    inference(forward_demodulation,[],[f5418,f27])).

fof(f5418,plain,(
    ! [X5] : k2_xboole_0(k2_xboole_0(X5,sK3),sK2) = k2_xboole_0(k2_xboole_0(X5,sK3),sK1) ),
    inference(forward_demodulation,[],[f5411,f29])).

fof(f5411,plain,(
    ! [X5] : k2_xboole_0(k2_xboole_0(X5,sK3),sK2) = k2_xboole_0(k2_xboole_0(X5,sK3),k4_xboole_0(sK1,k2_xboole_0(X5,sK3))) ),
    inference(superposition,[],[f29,f4899])).

fof(f6388,plain,(
    sK3 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f6373,f5971])).

fof(f5971,plain,(
    sK3 = k3_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f2199,f5876])).

fof(f2199,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k3_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f34,f2184])).

fof(f2184,plain,(
    sK0 = k3_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f1997,f25])).

fof(f1997,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f28,f1981])).

fof(f6373,plain,(
    k3_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f28,f5978])).

fof(f7933,plain,(
    sK3 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f7217,f7912])).

fof(f7912,plain,(
    k3_xboole_0(sK1,sK0) = k3_xboole_0(sK1,sK3) ),
    inference(backward_demodulation,[],[f6076,f7902])).

fof(f7902,plain,(
    k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f28,f7853])).

fof(f6076,plain,(
    k4_xboole_0(sK1,sK2) = k3_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f28,f5991])).

fof(f7217,plain,(
    sK3 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f7192,f5875])).

fof(f7192,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f5912,f6194])).

fof(f6194,plain,(
    sK1 = k2_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f6181,f2313])).

fof(f6181,plain,(
    k2_xboole_0(sK1,sK1) = k2_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f4203,f6076])).

fof(f4203,plain,(
    ! [X6] : k2_xboole_0(sK1,X6) = k2_xboole_0(sK1,k4_xboole_0(X6,sK2)) ),
    inference(forward_demodulation,[],[f4181,f4088])).

fof(f4181,plain,(
    ! [X6] : k2_xboole_0(sK1,k2_xboole_0(sK2,X6)) = k2_xboole_0(sK1,k4_xboole_0(X6,sK2)) ),
    inference(superposition,[],[f4088,f29])).

fof(f8519,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,k3_xboole_0(sK1,sK0))) ),
    inference(superposition,[],[f7915,f34])).

fof(f7915,plain,(
    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f6091,f7912])).

fof(f6091,plain,(
    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3)) ),
    inference(backward_demodulation,[],[f5737,f6076])).

fof(f5737,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f5736,f300])).

fof(f300,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f299,f25])).

fof(f299,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f28,f283])).

fof(f283,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f263,f257])).

fof(f257,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f142,f255])).

fof(f142,plain,(
    k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f134,f129])).

fof(f134,plain,(
    k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f129,f108])).

fof(f108,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f102,f43])).

fof(f102,plain,(
    k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f84,f20])).

fof(f5736,plain,(
    k3_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f5734,f1142])).

fof(f1142,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f311,f1141])).

fof(f1141,plain,(
    ! [X14] : k3_xboole_0(k1_xboole_0,X14) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X14)) ),
    inference(forward_demodulation,[],[f1140,f28])).

fof(f1140,plain,(
    ! [X14] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X14)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X14)) ),
    inference(forward_demodulation,[],[f1104,f311])).

fof(f1104,plain,(
    ! [X14] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X14)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X14)) ),
    inference(superposition,[],[f1062,f268])).

fof(f268,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f34,f266])).

fof(f1062,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) ),
    inference(backward_demodulation,[],[f156,f1059])).

fof(f311,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f268,f28])).

fof(f5734,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f31,f5635])).

fof(f5635,plain,(
    k4_xboole_0(sK1,sK2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f1740,f300])).

fof(f1740,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k4_xboole_0(sK1,X1)) ),
    inference(superposition,[],[f1145,f27])).

fof(f1145,plain,(
    ! [X2] : k4_xboole_0(sK1,X2) = k2_xboole_0(k4_xboole_0(sK1,X2),k3_xboole_0(k1_xboole_0,X2)) ),
    inference(backward_demodulation,[],[f320,f1141])).

fof(f320,plain,(
    ! [X2] : k4_xboole_0(sK1,X2) = k2_xboole_0(k4_xboole_0(sK1,X2),k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X2))) ),
    inference(backward_demodulation,[],[f262,f318])).

fof(f318,plain,(
    ! [X0] : k3_xboole_0(sK3,k3_xboole_0(sK1,X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X0)) ),
    inference(backward_demodulation,[],[f65,f311])).

fof(f262,plain,(
    ! [X2] : k4_xboole_0(sK1,X2) = k2_xboole_0(k4_xboole_0(sK1,X2),k3_xboole_0(sK3,k3_xboole_0(sK1,X2))) ),
    inference(forward_demodulation,[],[f252,f26])).

fof(f252,plain,(
    ! [X2] : k2_xboole_0(k4_xboole_0(sK1,X2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,X2),k3_xboole_0(sK3,k3_xboole_0(sK1,X2))) ),
    inference(superposition,[],[f29,f65])).

fof(f7924,plain,(
    sK2 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f6203,f7912])).

fof(f6203,plain,(
    sK2 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f6187,f6068])).

fof(f6068,plain,(
    sK2 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f4535,f5991])).

fof(f4535,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f34,f4529])).

fof(f4529,plain,(
    sK1 = k3_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f4518,f25])).

fof(f4518,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f28,f4505])).

fof(f4505,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f4498,f4048])).

fof(f4498,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f31,f4468])).

fof(f4468,plain,(
    sK1 = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f4138,f4073])).

fof(f6187,plain,(
    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f28,f6076])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.51  % (5848)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  % (5839)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.53  % (5832)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.53  % (5828)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.54  % (5830)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.52/0.56  % (5834)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.52/0.56  % (5849)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.52/0.56  % (5829)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.52/0.56  % (5841)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.52/0.56  % (5852)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.52/0.56  % (5831)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.52/0.57  % (5836)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.52/0.57  % (5842)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.52/0.57  % (5833)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.52/0.57  % (5842)Refutation not found, incomplete strategy% (5842)------------------------------
% 1.52/0.57  % (5842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (5842)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (5842)Memory used [KB]: 6140
% 1.52/0.57  % (5842)Time elapsed: 0.002 s
% 1.52/0.57  % (5842)------------------------------
% 1.52/0.57  % (5842)------------------------------
% 1.52/0.57  % (5851)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.52/0.57  % (5846)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.52/0.57  % (5827)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.52/0.57  % (5844)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.52/0.57  % (5835)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.52/0.57  % (5850)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.52/0.57  % (5844)Refutation not found, incomplete strategy% (5844)------------------------------
% 1.52/0.57  % (5844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (5844)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (5844)Memory used [KB]: 10618
% 1.52/0.57  % (5844)Time elapsed: 0.155 s
% 1.52/0.57  % (5844)------------------------------
% 1.52/0.57  % (5844)------------------------------
% 1.52/0.57  % (5854)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.52/0.58  % (5843)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.52/0.58  % (5856)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.59  % (5853)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.52/0.59  % (5837)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.52/0.60  % (5845)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.52/0.60  % (5855)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.52/0.60  % (5840)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.52/0.61  % (5838)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.52/0.62  % (5847)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.59/0.72  % (5883)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.59/0.74  % (5884)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.96/0.81  % (5832)Time limit reached!
% 2.96/0.81  % (5832)------------------------------
% 2.96/0.81  % (5832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.96/0.81  % (5832)Termination reason: Time limit
% 2.96/0.81  
% 2.96/0.81  % (5832)Memory used [KB]: 9338
% 2.96/0.81  % (5832)Time elapsed: 0.402 s
% 2.96/0.81  % (5832)------------------------------
% 2.96/0.81  % (5832)------------------------------
% 4.05/0.92  % (5827)Time limit reached!
% 4.05/0.92  % (5827)------------------------------
% 4.05/0.92  % (5827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.92  % (5827)Termination reason: Time limit
% 4.05/0.92  
% 4.05/0.92  % (5827)Memory used [KB]: 3709
% 4.05/0.92  % (5827)Time elapsed: 0.503 s
% 4.05/0.92  % (5827)------------------------------
% 4.05/0.92  % (5827)------------------------------
% 4.05/0.92  % (5837)Time limit reached!
% 4.05/0.92  % (5837)------------------------------
% 4.05/0.92  % (5837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.92  % (5837)Termination reason: Time limit
% 4.05/0.92  % (5837)Termination phase: Saturation
% 4.05/0.92  
% 4.05/0.92  % (5837)Memory used [KB]: 14711
% 4.05/0.92  % (5837)Time elapsed: 0.500 s
% 4.05/0.92  % (5837)------------------------------
% 4.05/0.92  % (5837)------------------------------
% 4.05/0.94  % (5839)Time limit reached!
% 4.05/0.94  % (5839)------------------------------
% 4.05/0.94  % (5839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.94  % (5839)Termination reason: Time limit
% 4.05/0.94  % (5839)Termination phase: Saturation
% 4.05/0.94  
% 4.05/0.94  % (5839)Memory used [KB]: 11513
% 4.05/0.94  % (5839)Time elapsed: 0.500 s
% 4.05/0.94  % (5839)------------------------------
% 4.05/0.94  % (5839)------------------------------
% 4.05/0.95  % (5828)Time limit reached!
% 4.05/0.95  % (5828)------------------------------
% 4.05/0.95  % (5828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.95  % (5828)Termination reason: Time limit
% 4.05/0.95  
% 4.05/0.95  % (5828)Memory used [KB]: 9083
% 4.05/0.95  % (5828)Time elapsed: 0.518 s
% 4.05/0.95  % (5828)------------------------------
% 4.05/0.95  % (5828)------------------------------
% 4.50/0.97  % (5888)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.50/1.02  % (5843)Time limit reached!
% 4.50/1.02  % (5843)------------------------------
% 4.50/1.02  % (5843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.02  % (5843)Termination reason: Time limit
% 4.50/1.02  
% 4.50/1.02  % (5843)Memory used [KB]: 16375
% 4.50/1.02  % (5843)Time elapsed: 0.608 s
% 4.50/1.02  % (5843)------------------------------
% 4.50/1.02  % (5843)------------------------------
% 4.50/1.02  % (5855)Time limit reached!
% 4.50/1.02  % (5855)------------------------------
% 4.50/1.02  % (5855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.02  % (5855)Termination reason: Time limit
% 4.50/1.02  % (5855)Termination phase: Saturation
% 4.50/1.02  
% 4.50/1.02  % (5855)Memory used [KB]: 8827
% 4.50/1.02  % (5855)Time elapsed: 0.600 s
% 4.50/1.02  % (5855)------------------------------
% 4.50/1.02  % (5855)------------------------------
% 4.50/1.02  % (5834)Time limit reached!
% 4.50/1.02  % (5834)------------------------------
% 4.50/1.02  % (5834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.04  % (5834)Termination reason: Time limit
% 4.50/1.04  % (5834)Termination phase: Saturation
% 4.50/1.04  
% 4.50/1.04  % (5834)Memory used [KB]: 10362
% 4.50/1.04  % (5834)Time elapsed: 0.600 s
% 4.50/1.04  % (5834)------------------------------
% 4.50/1.04  % (5834)------------------------------
% 5.11/1.06  % (5890)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.11/1.06  % (5850)Refutation found. Thanks to Tanya!
% 5.11/1.06  % SZS status Theorem for theBenchmark
% 5.11/1.06  % (5891)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.11/1.06  % SZS output start Proof for theBenchmark
% 5.11/1.06  fof(f9599,plain,(
% 5.11/1.06    $false),
% 5.11/1.06    inference(subsumption_resolution,[],[f9598,f23])).
% 5.11/1.06  fof(f23,plain,(
% 5.11/1.06    sK1 != sK2),
% 5.11/1.06    inference(cnf_transformation,[],[f18])).
% 5.11/1.06  fof(f18,plain,(
% 5.11/1.06    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 5.11/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).
% 5.11/1.06  fof(f17,plain,(
% 5.11/1.06    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 5.11/1.06    introduced(choice_axiom,[])).
% 5.11/1.06  fof(f16,plain,(
% 5.11/1.06    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 5.11/1.06    inference(flattening,[],[f15])).
% 5.11/1.06  fof(f15,plain,(
% 5.11/1.06    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 5.11/1.06    inference(ennf_transformation,[],[f14])).
% 5.11/1.06  fof(f14,negated_conjecture,(
% 5.11/1.06    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 5.11/1.06    inference(negated_conjecture,[],[f13])).
% 5.11/1.06  fof(f13,conjecture,(
% 5.11/1.06    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 5.11/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 5.11/1.06  fof(f9598,plain,(
% 5.11/1.06    sK1 = sK2),
% 5.11/1.06    inference(forward_demodulation,[],[f9588,f25])).
% 5.11/1.06  fof(f25,plain,(
% 5.11/1.06    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.11/1.06    inference(cnf_transformation,[],[f6])).
% 5.11/1.06  fof(f6,axiom,(
% 5.11/1.06    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.11/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 5.11/1.06  fof(f9588,plain,(
% 5.11/1.06    sK2 = k4_xboole_0(sK1,k1_xboole_0)),
% 5.11/1.06    inference(backward_demodulation,[],[f7924,f9572])).
% 5.11/1.06  fof(f9572,plain,(
% 5.11/1.06    k1_xboole_0 = k3_xboole_0(sK1,sK0)),
% 5.11/1.06    inference(backward_demodulation,[],[f8519,f9474])).
% 5.11/1.06  fof(f9474,plain,(
% 5.11/1.06    sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK0))),
% 5.11/1.06    inference(backward_demodulation,[],[f7933,f9247])).
% 5.11/1.06  fof(f9247,plain,(
% 5.11/1.06    sK0 = sK3),
% 5.11/1.06    inference(forward_demodulation,[],[f9222,f25])).
% 5.11/1.06  fof(f9222,plain,(
% 5.11/1.06    sK3 = k4_xboole_0(sK0,k1_xboole_0)),
% 5.11/1.06    inference(backward_demodulation,[],[f6388,f9202])).
% 5.11/1.06  fof(f9202,plain,(
% 5.11/1.06    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 5.11/1.06    inference(backward_demodulation,[],[f7806,f9201])).
% 5.11/1.06  fof(f9201,plain,(
% 5.11/1.06    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 5.11/1.06    inference(forward_demodulation,[],[f9193,f7853])).
% 5.11/1.06  fof(f7853,plain,(
% 5.11/1.06    sK2 = k4_xboole_0(sK1,sK0)),
% 5.11/1.06    inference(forward_demodulation,[],[f7852,f25])).
% 5.11/1.06  fof(f7852,plain,(
% 5.11/1.06    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 5.11/1.06    inference(forward_demodulation,[],[f7843,f7606])).
% 5.11/1.06  fof(f7606,plain,(
% 5.11/1.06    k4_xboole_0(sK1,sK0) = k3_xboole_0(sK2,k4_xboole_0(sK1,sK0))),
% 5.11/1.06    inference(superposition,[],[f6049,f7515])).
% 5.11/1.06  fof(f7515,plain,(
% 5.11/1.06    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK2,sK0)),
% 5.11/1.06    inference(superposition,[],[f6482,f7496])).
% 5.11/1.06  fof(f7496,plain,(
% 5.11/1.06    sK0 = k2_xboole_0(sK0,sK3)),
% 5.11/1.06    inference(forward_demodulation,[],[f7488,f26])).
% 5.11/1.06  fof(f26,plain,(
% 5.11/1.06    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.11/1.06    inference(cnf_transformation,[],[f3])).
% 5.11/1.06  fof(f3,axiom,(
% 5.11/1.06    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 5.11/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 5.11/1.06  fof(f7488,plain,(
% 5.11/1.06    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3)),
% 5.11/1.06    inference(superposition,[],[f29,f7467])).
% 5.11/1.06  fof(f7467,plain,(
% 5.11/1.06    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 5.11/1.06    inference(forward_demodulation,[],[f7454,f5879])).
% 5.11/1.06  fof(f5879,plain,(
% 5.11/1.06    k1_xboole_0 = k4_xboole_0(sK3,sK3)),
% 5.11/1.06    inference(backward_demodulation,[],[f2481,f5876])).
% 5.11/1.06  fof(f5876,plain,(
% 5.11/1.06    sK3 = k4_xboole_0(sK0,sK1)),
% 5.11/1.06    inference(backward_demodulation,[],[f4696,f5875])).
% 5.11/1.06  fof(f5875,plain,(
% 5.11/1.06    sK3 = k4_xboole_0(sK3,sK1)),
% 5.11/1.06    inference(forward_demodulation,[],[f5862,f4746])).
% 5.11/1.06  fof(f4746,plain,(
% 5.11/1.06    sK3 = k3_xboole_0(sK3,k4_xboole_0(sK0,sK1))),
% 5.11/1.06    inference(forward_demodulation,[],[f4739,f25])).
% 5.11/1.06  fof(f4739,plain,(
% 5.11/1.06    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,k4_xboole_0(sK0,sK1))),
% 5.11/1.06    inference(superposition,[],[f28,f4712])).
% 5.11/1.06  fof(f4712,plain,(
% 5.11/1.06    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK0,sK1))),
% 5.11/1.06    inference(forward_demodulation,[],[f4705,f38])).
% 5.11/1.06  fof(f38,plain,(
% 5.11/1.06    k1_xboole_0 = k3_xboole_0(sK3,sK1)),
% 5.11/1.06    inference(resolution,[],[f22,f32])).
% 5.11/1.06  fof(f32,plain,(
% 5.11/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 5.11/1.06    inference(cnf_transformation,[],[f19])).
% 5.11/1.06  fof(f19,plain,(
% 5.11/1.06    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 5.11/1.06    inference(nnf_transformation,[],[f2])).
% 5.11/1.06  fof(f2,axiom,(
% 5.11/1.06    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 5.11/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 5.11/1.06  fof(f22,plain,(
% 5.11/1.06    r1_xboole_0(sK3,sK1)),
% 5.11/1.06    inference(cnf_transformation,[],[f18])).
% 5.11/1.06  fof(f4705,plain,(
% 5.11/1.06    k3_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k4_xboole_0(sK0,sK1))),
% 5.11/1.06    inference(superposition,[],[f28,f4696])).
% 5.11/1.06  fof(f28,plain,(
% 5.11/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.11/1.06    inference(cnf_transformation,[],[f9])).
% 5.11/1.06  fof(f9,axiom,(
% 5.11/1.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.11/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.11/1.06  fof(f5862,plain,(
% 5.11/1.06    k4_xboole_0(sK3,sK1) = k3_xboole_0(sK3,k4_xboole_0(sK0,sK1))),
% 5.11/1.06    inference(superposition,[],[f2719,f31])).
% 5.11/1.06  fof(f31,plain,(
% 5.11/1.06    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 5.11/1.06    inference(cnf_transformation,[],[f7])).
% 5.11/1.06  fof(f7,axiom,(
% 5.11/1.06    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 5.11/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 5.11/1.06  fof(f2719,plain,(
% 5.11/1.06    ( ! [X0] : (k4_xboole_0(sK3,X0) = k3_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK0,sK1),X0))) )),
% 5.11/1.06    inference(superposition,[],[f34,f2686])).
% 5.11/1.06  fof(f2686,plain,(
% 5.11/1.06    sK3 = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 5.11/1.06    inference(forward_demodulation,[],[f2683,f25])).
% 5.11/1.07  fof(f2683,plain,(
% 5.11/1.07    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(backward_demodulation,[],[f779,f2681])).
% 5.11/1.07  fof(f2681,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(forward_demodulation,[],[f2679,f266])).
% 5.11/1.07  fof(f266,plain,(
% 5.11/1.07    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 5.11/1.07    inference(forward_demodulation,[],[f264,f25])).
% 5.11/1.07  fof(f264,plain,(
% 5.11/1.07    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK1)),
% 5.11/1.07    inference(superposition,[],[f28,f255])).
% 5.11/1.07  fof(f255,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 5.11/1.07    inference(forward_demodulation,[],[f254,f24])).
% 5.11/1.07  fof(f24,plain,(
% 5.11/1.07    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 5.11/1.07    inference(cnf_transformation,[],[f4])).
% 5.11/1.07  fof(f4,axiom,(
% 5.11/1.07    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 5.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 5.11/1.07  fof(f254,plain,(
% 5.11/1.07    k4_xboole_0(k1_xboole_0,sK1) = k3_xboole_0(sK3,k1_xboole_0)),
% 5.11/1.07    inference(forward_demodulation,[],[f247,f24])).
% 5.11/1.07  fof(f247,plain,(
% 5.11/1.07    k4_xboole_0(k1_xboole_0,sK1) = k3_xboole_0(sK3,k3_xboole_0(sK1,k1_xboole_0))),
% 5.11/1.07    inference(superposition,[],[f65,f25])).
% 5.11/1.07  fof(f65,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X0)) = k3_xboole_0(sK3,k3_xboole_0(sK1,X0))) )),
% 5.11/1.07    inference(superposition,[],[f40,f28])).
% 5.11/1.07  fof(f40,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(sK3,k4_xboole_0(sK1,X0))) )),
% 5.11/1.07    inference(superposition,[],[f34,f38])).
% 5.11/1.07  fof(f2679,plain,(
% 5.11/1.07    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k3_xboole_0(k1_xboole_0,sK1)),
% 5.11/1.07    inference(backward_demodulation,[],[f53,f2678])).
% 5.11/1.07  fof(f2678,plain,(
% 5.11/1.07    ( ! [X2] : (k3_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k2_xboole_0(sK0,X2),k2_xboole_0(sK0,X2))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f2675,f2015])).
% 5.11/1.07  fof(f2015,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,X0)) )),
% 5.11/1.07    inference(backward_demodulation,[],[f129,f2010])).
% 5.11/1.07  fof(f2010,plain,(
% 5.11/1.07    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k3_xboole_0(k1_xboole_0,X4)) )),
% 5.11/1.07    inference(forward_demodulation,[],[f2007,f1066])).
% 5.11/1.07  fof(f1066,plain,(
% 5.11/1.07    ( ! [X2] : (k3_xboole_0(k1_xboole_0,X2) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),k4_xboole_0(k1_xboole_0,X2))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f852,f1059])).
% 5.11/1.07  fof(f1059,plain,(
% 5.11/1.07    ( ! [X5] : (k3_xboole_0(k1_xboole_0,X5) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X5))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f1055,f28])).
% 5.11/1.07  fof(f1055,plain,(
% 5.11/1.07    ( ! [X5] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X5)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5))) )),
% 5.11/1.07    inference(superposition,[],[f28,f1027])).
% 5.11/1.07  fof(f1027,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f992,f1026])).
% 5.11/1.07  fof(f1026,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK0,X0)))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f1023,f34])).
% 5.11/1.07  fof(f1023,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k4_xboole_0(k3_xboole_0(sK0,sK0),X0))) )),
% 5.11/1.07    inference(superposition,[],[f34,f1008])).
% 5.11/1.07  fof(f1008,plain,(
% 5.11/1.07    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK0))),
% 5.11/1.07    inference(forward_demodulation,[],[f993,f125])).
% 5.11/1.07  fof(f125,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)),
% 5.11/1.07    inference(forward_demodulation,[],[f124,f24])).
% 5.11/1.07  fof(f124,plain,(
% 5.11/1.07    k4_xboole_0(k1_xboole_0,sK0) = k3_xboole_0(sK2,k1_xboole_0)),
% 5.11/1.07    inference(forward_demodulation,[],[f119,f24])).
% 5.11/1.07  fof(f119,plain,(
% 5.11/1.07    k3_xboole_0(sK2,k3_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,sK0)),
% 5.11/1.07    inference(superposition,[],[f57,f25])).
% 5.11/1.07  fof(f57,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0)) = k3_xboole_0(sK2,k3_xboole_0(sK0,X0))) )),
% 5.11/1.07    inference(superposition,[],[f39,f28])).
% 5.11/1.07  fof(f39,plain,(
% 5.11/1.07    ( ! [X0] : (k3_xboole_0(sK2,k4_xboole_0(sK0,X0)) = k4_xboole_0(k1_xboole_0,X0)) )),
% 5.11/1.07    inference(superposition,[],[f34,f37])).
% 5.11/1.07  fof(f37,plain,(
% 5.11/1.07    k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 5.11/1.07    inference(resolution,[],[f21,f32])).
% 5.11/1.07  fof(f21,plain,(
% 5.11/1.07    r1_xboole_0(sK2,sK0)),
% 5.11/1.07    inference(cnf_transformation,[],[f18])).
% 5.11/1.07  fof(f993,plain,(
% 5.11/1.07    k4_xboole_0(k1_xboole_0,sK0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK0))),
% 5.11/1.07    inference(superposition,[],[f150,f144])).
% 5.11/1.07  fof(f144,plain,(
% 5.11/1.07    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,sK0))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f138,f129])).
% 5.11/1.07  fof(f138,plain,(
% 5.11/1.07    ( ! [X3] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,sK0)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X3))) )),
% 5.11/1.07    inference(superposition,[],[f129,f29])).
% 5.11/1.07  fof(f150,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) )),
% 5.11/1.07    inference(superposition,[],[f132,f28])).
% 5.11/1.07  fof(f132,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0))) )),
% 5.11/1.07    inference(superposition,[],[f34,f131])).
% 5.11/1.07  fof(f131,plain,(
% 5.11/1.07    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)),
% 5.11/1.07    inference(forward_demodulation,[],[f130,f25])).
% 5.11/1.07  fof(f130,plain,(
% 5.11/1.07    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK0)),
% 5.11/1.07    inference(superposition,[],[f28,f125])).
% 5.11/1.07  fof(f992,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k4_xboole_0(sK0,X0)))) )),
% 5.11/1.07    inference(superposition,[],[f150,f28])).
% 5.11/1.07  fof(f852,plain,(
% 5.11/1.07    ( ! [X2] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)) = k2_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)),k4_xboole_0(k1_xboole_0,X2))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f846,f26])).
% 5.11/1.07  fof(f846,plain,(
% 5.11/1.07    ( ! [X2] : (k2_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)),k1_xboole_0) = k2_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)),k4_xboole_0(k1_xboole_0,X2))) )),
% 5.11/1.07    inference(superposition,[],[f29,f156])).
% 5.11/1.07  fof(f156,plain,(
% 5.11/1.07    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X3)))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f133,f155])).
% 5.11/1.07  fof(f155,plain,(
% 5.11/1.07    ( ! [X0] : (k3_xboole_0(sK2,k3_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f57,f150])).
% 5.11/1.07  fof(f133,plain,(
% 5.11/1.07    ( ! [X3] : (k4_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k3_xboole_0(sK0,X3))) = k4_xboole_0(k1_xboole_0,X3)) )),
% 5.11/1.07    inference(backward_demodulation,[],[f123,f132])).
% 5.11/1.07  fof(f123,plain,(
% 5.11/1.07    ( ! [X3] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X3)) = k4_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k3_xboole_0(sK0,X3)))) )),
% 5.11/1.07    inference(superposition,[],[f28,f57])).
% 5.11/1.07  fof(f2007,plain,(
% 5.11/1.07    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X4),k4_xboole_0(k1_xboole_0,X4))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f1924,f1995])).
% 5.11/1.07  fof(f1995,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0))) )),
% 5.11/1.07    inference(superposition,[],[f35,f1981])).
% 5.11/1.07  fof(f1981,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 5.11/1.07    inference(forward_demodulation,[],[f1977,f125])).
% 5.11/1.07  fof(f1977,plain,(
% 5.11/1.07    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK0,sK0)),
% 5.11/1.07    inference(superposition,[],[f31,f1968])).
% 5.11/1.07  fof(f1968,plain,(
% 5.11/1.07    sK0 = k2_xboole_0(k1_xboole_0,sK0)),
% 5.11/1.07    inference(forward_demodulation,[],[f1967,f25])).
% 5.11/1.07  fof(f1967,plain,(
% 5.11/1.07    k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,sK0)),
% 5.11/1.07    inference(forward_demodulation,[],[f1953,f29])).
% 5.11/1.07  fof(f1953,plain,(
% 5.11/1.07    k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))),
% 5.11/1.07    inference(superposition,[],[f1694,f24])).
% 5.11/1.07  fof(f1694,plain,(
% 5.11/1.07    ( ! [X1] : (k4_xboole_0(sK0,X1) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k4_xboole_0(sK0,X1))) )),
% 5.11/1.07    inference(superposition,[],[f1063,f27])).
% 5.11/1.07  fof(f27,plain,(
% 5.11/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.11/1.07    inference(cnf_transformation,[],[f1])).
% 5.11/1.07  fof(f1,axiom,(
% 5.11/1.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.11/1.07  fof(f1063,plain,(
% 5.11/1.07    ( ! [X2] : (k4_xboole_0(sK0,X2) = k2_xboole_0(k4_xboole_0(sK0,X2),k3_xboole_0(k1_xboole_0,X2))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f157,f1059])).
% 5.11/1.07  fof(f157,plain,(
% 5.11/1.07    ( ! [X2] : (k4_xboole_0(sK0,X2) = k2_xboole_0(k4_xboole_0(sK0,X2),k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f128,f155])).
% 5.11/1.07  fof(f128,plain,(
% 5.11/1.07    ( ! [X2] : (k4_xboole_0(sK0,X2) = k2_xboole_0(k4_xboole_0(sK0,X2),k3_xboole_0(sK2,k3_xboole_0(sK0,X2)))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f122,f26])).
% 5.11/1.07  fof(f122,plain,(
% 5.11/1.07    ( ! [X2] : (k2_xboole_0(k4_xboole_0(sK0,X2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,X2),k3_xboole_0(sK2,k3_xboole_0(sK0,X2)))) )),
% 5.11/1.07    inference(superposition,[],[f29,f57])).
% 5.11/1.07  fof(f35,plain,(
% 5.11/1.07    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.11/1.07    inference(cnf_transformation,[],[f8])).
% 5.11/1.07  fof(f8,axiom,(
% 5.11/1.07    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 5.11/1.07  fof(f1924,plain,(
% 5.11/1.07    ( ! [X4] : (k4_xboole_0(sK0,k2_xboole_0(sK0,X4)) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X4),k4_xboole_0(sK0,k2_xboole_0(sK0,X4)))) )),
% 5.11/1.07    inference(superposition,[],[f1694,f148])).
% 5.11/1.07  fof(f148,plain,(
% 5.11/1.07    ( ! [X3] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X3)) = k3_xboole_0(k1_xboole_0,X3)) )),
% 5.11/1.07    inference(forward_demodulation,[],[f141,f28])).
% 5.11/1.07  fof(f141,plain,(
% 5.11/1.07    ( ! [X3] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X3)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) )),
% 5.11/1.07    inference(superposition,[],[f28,f129])).
% 5.11/1.07  fof(f129,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0))) )),
% 5.11/1.07    inference(superposition,[],[f35,f125])).
% 5.11/1.07  fof(f2675,plain,(
% 5.11/1.07    ( ! [X2] : (k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X2)) = k4_xboole_0(k2_xboole_0(sK0,X2),k2_xboole_0(sK0,X2))) )),
% 5.11/1.07    inference(superposition,[],[f31,f1976])).
% 5.11/1.07  fof(f1976,plain,(
% 5.11/1.07    ( ! [X0] : (k2_xboole_0(sK0,X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0))) )),
% 5.11/1.07    inference(superposition,[],[f36,f1968])).
% 5.11/1.07  fof(f36,plain,(
% 5.11/1.07    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.11/1.07    inference(cnf_transformation,[],[f11])).
% 5.11/1.07  fof(f11,axiom,(
% 5.11/1.07    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 5.11/1.07  fof(f53,plain,(
% 5.11/1.07    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(superposition,[],[f31,f43])).
% 5.11/1.07  fof(f43,plain,(
% 5.11/1.07    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(superposition,[],[f30,f20])).
% 5.11/1.07  fof(f20,plain,(
% 5.11/1.07    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 5.11/1.07    inference(cnf_transformation,[],[f18])).
% 5.11/1.07  fof(f30,plain,(
% 5.11/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 5.11/1.07    inference(cnf_transformation,[],[f12])).
% 5.11/1.07  fof(f12,axiom,(
% 5.11/1.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 5.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 5.11/1.07  fof(f779,plain,(
% 5.11/1.07    k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK3,k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)))),
% 5.11/1.07    inference(superposition,[],[f28,f76])).
% 5.11/1.07  fof(f76,plain,(
% 5.11/1.07    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(forward_demodulation,[],[f73,f53])).
% 5.11/1.07  fof(f73,plain,(
% 5.11/1.07    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(superposition,[],[f31,f51])).
% 5.11/1.07  fof(f51,plain,(
% 5.11/1.07    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(forward_demodulation,[],[f50,f20])).
% 5.11/1.07  fof(f50,plain,(
% 5.11/1.07    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(forward_demodulation,[],[f49,f27])).
% 5.11/1.07  fof(f49,plain,(
% 5.11/1.07    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(forward_demodulation,[],[f46,f29])).
% 5.11/1.07  fof(f46,plain,(
% 5.11/1.07    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 5.11/1.07    inference(superposition,[],[f29,f42])).
% 5.11/1.07  fof(f42,plain,(
% 5.11/1.07    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 5.11/1.07    inference(superposition,[],[f31,f20])).
% 5.11/1.07  fof(f34,plain,(
% 5.11/1.07    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 5.11/1.07    inference(cnf_transformation,[],[f10])).
% 5.11/1.07  fof(f10,axiom,(
% 5.11/1.07    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 5.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 5.11/1.07  fof(f4696,plain,(
% 5.11/1.07    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK3,sK1)),
% 5.11/1.07    inference(forward_demodulation,[],[f4687,f31])).
% 5.11/1.07  fof(f4687,plain,(
% 5.11/1.07    k4_xboole_0(sK3,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 5.11/1.07    inference(superposition,[],[f31,f4670])).
% 5.11/1.07  fof(f4670,plain,(
% 5.11/1.07    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK1)),
% 5.11/1.07    inference(forward_demodulation,[],[f4663,f2313])).
% 5.11/1.07  fof(f2313,plain,(
% 5.11/1.07    ( ! [X3] : (k2_xboole_0(X3,X3) = X3) )),
% 5.11/1.07    inference(superposition,[],[f30,f2280])).
% 5.11/1.07  fof(f2280,plain,(
% 5.11/1.07    ( ! [X6] : (k2_xboole_0(X6,k3_xboole_0(k1_xboole_0,X6)) = X6) )),
% 5.11/1.07    inference(forward_demodulation,[],[f2237,f26])).
% 5.11/1.07  fof(f2237,plain,(
% 5.11/1.07    ( ! [X6] : (k2_xboole_0(X6,k1_xboole_0) = k2_xboole_0(X6,k3_xboole_0(k1_xboole_0,X6))) )),
% 5.11/1.07    inference(superposition,[],[f29,f2010])).
% 5.11/1.07  fof(f4663,plain,(
% 5.11/1.07    k2_xboole_0(sK3,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK1))),
% 5.11/1.07    inference(superposition,[],[f4472,f44])).
% 5.11/1.07  fof(f44,plain,(
% 5.11/1.07    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f41,f36])).
% 5.11/1.07  fof(f41,plain,(
% 5.11/1.07    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0)) )),
% 5.11/1.07    inference(superposition,[],[f36,f20])).
% 5.11/1.07  fof(f4472,plain,(
% 5.11/1.07    ( ! [X1] : (k2_xboole_0(X1,sK1) = k2_xboole_0(sK2,k2_xboole_0(X1,sK1))) )),
% 5.11/1.07    inference(superposition,[],[f4138,f27])).
% 5.11/1.07  fof(f4138,plain,(
% 5.11/1.07    ( ! [X5] : (k2_xboole_0(sK1,X5) = k2_xboole_0(sK2,k2_xboole_0(sK1,X5))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f4137,f2030])).
% 5.11/1.07  fof(f2030,plain,(
% 5.11/1.07    ( ! [X2] : (k2_xboole_0(sK1,X2) = k2_xboole_0(k2_xboole_0(sK1,X2),k3_xboole_0(k1_xboole_0,X2))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f296,f2010])).
% 5.11/1.07  fof(f296,plain,(
% 5.11/1.07    ( ! [X2] : (k2_xboole_0(sK1,X2) = k2_xboole_0(k2_xboole_0(sK1,X2),k4_xboole_0(k1_xboole_0,X2))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f288,f26])).
% 5.11/1.07  fof(f288,plain,(
% 5.11/1.07    ( ! [X2] : (k2_xboole_0(k2_xboole_0(sK1,X2),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK1,X2),k4_xboole_0(k1_xboole_0,X2))) )),
% 5.11/1.07    inference(superposition,[],[f29,f263])).
% 5.11/1.07  fof(f263,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,X0))) )),
% 5.11/1.07    inference(superposition,[],[f35,f255])).
% 5.11/1.07  fof(f4137,plain,(
% 5.11/1.07    ( ! [X5] : (k2_xboole_0(k2_xboole_0(sK1,X5),k3_xboole_0(k1_xboole_0,X5)) = k2_xboole_0(sK2,k2_xboole_0(sK1,X5))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f4123,f27])).
% 5.11/1.07  fof(f4123,plain,(
% 5.11/1.07    ( ! [X5] : (k2_xboole_0(k2_xboole_0(sK1,X5),k3_xboole_0(k1_xboole_0,X5)) = k2_xboole_0(k2_xboole_0(sK1,X5),sK2)) )),
% 5.11/1.07    inference(superposition,[],[f29,f4072])).
% 5.11/1.07  fof(f4072,plain,(
% 5.11/1.07    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK1,X0))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f4065,f2010])).
% 5.11/1.07  fof(f4065,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK1,X0))) )),
% 5.11/1.07    inference(superposition,[],[f35,f4048])).
% 5.11/1.07  fof(f4048,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 5.11/1.07    inference(forward_demodulation,[],[f4047,f266])).
% 5.11/1.07  fof(f4047,plain,(
% 5.11/1.07    k3_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK2,sK1)),
% 5.11/1.07    inference(forward_demodulation,[],[f4035,f2011])).
% 5.11/1.07  fof(f2011,plain,(
% 5.11/1.07    ( ! [X0] : (k3_xboole_0(sK2,k4_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,X0)) )),
% 5.11/1.07    inference(backward_demodulation,[],[f39,f2010])).
% 5.11/1.07  fof(f4035,plain,(
% 5.11/1.07    k4_xboole_0(sK2,sK1) = k3_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(superposition,[],[f2713,f31])).
% 5.11/1.07  fof(f2713,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK2,X0) = k3_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK0,sK1),X0))) )),
% 5.11/1.07    inference(superposition,[],[f34,f2699])).
% 5.11/1.07  fof(f2699,plain,(
% 5.11/1.07    sK2 = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(forward_demodulation,[],[f2693,f25])).
% 5.11/1.07  fof(f2693,plain,(
% 5.11/1.07    k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(superposition,[],[f28,f2681])).
% 5.11/1.07  fof(f2481,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(forward_demodulation,[],[f2480,f266])).
% 5.11/1.07  fof(f2480,plain,(
% 5.11/1.07    k3_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(forward_demodulation,[],[f2478,f1060])).
% 5.11/1.07  fof(f1060,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0)) = k3_xboole_0(k1_xboole_0,X0)) )),
% 5.11/1.07    inference(backward_demodulation,[],[f150,f1059])).
% 5.11/1.07  fof(f2478,plain,(
% 5.11/1.07    k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(superposition,[],[f31,f1950])).
% 5.11/1.07  fof(f1950,plain,(
% 5.11/1.07    k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(superposition,[],[f1694,f266])).
% 5.11/1.07  fof(f7454,plain,(
% 5.11/1.07    k4_xboole_0(sK3,sK0) = k4_xboole_0(sK3,sK3)),
% 5.11/1.07    inference(superposition,[],[f7243,f5876])).
% 5.11/1.07  fof(f7243,plain,(
% 5.11/1.07    ( ! [X8] : (k4_xboole_0(sK3,X8) = k4_xboole_0(sK3,k4_xboole_0(X8,sK1))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f7200,f5912])).
% 5.11/1.07  fof(f5912,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(sK1,X0))) )),
% 5.11/1.07    inference(superposition,[],[f35,f5875])).
% 5.11/1.07  fof(f7200,plain,(
% 5.11/1.07    ( ! [X8] : (k4_xboole_0(sK3,k4_xboole_0(X8,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK1,X8))) )),
% 5.11/1.07    inference(superposition,[],[f5912,f29])).
% 5.11/1.07  fof(f29,plain,(
% 5.11/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.11/1.07    inference(cnf_transformation,[],[f5])).
% 5.11/1.07  fof(f5,axiom,(
% 5.11/1.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 5.11/1.07  fof(f6482,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK3))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f4899,f6463])).
% 5.11/1.07  fof(f6463,plain,(
% 5.11/1.07    ( ! [X2] : (k4_xboole_0(sK2,k2_xboole_0(X2,sK3)) = k4_xboole_0(sK2,X2)) )),
% 5.11/1.07    inference(superposition,[],[f6043,f27])).
% 5.11/1.07  fof(f6043,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,X0)) )),
% 5.11/1.07    inference(superposition,[],[f35,f5993])).
% 5.11/1.07  fof(f5993,plain,(
% 5.11/1.07    sK2 = k4_xboole_0(sK2,sK3)),
% 5.11/1.07    inference(backward_demodulation,[],[f4302,f5991])).
% 5.11/1.07  fof(f5991,plain,(
% 5.11/1.07    sK2 = k4_xboole_0(sK1,sK3)),
% 5.11/1.07    inference(forward_demodulation,[],[f5986,f25])).
% 5.11/1.07  fof(f5986,plain,(
% 5.11/1.07    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,sK3)),
% 5.11/1.07    inference(backward_demodulation,[],[f4366,f5982])).
% 5.11/1.07  fof(f5982,plain,(
% 5.11/1.07    k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 5.11/1.07    inference(forward_demodulation,[],[f5966,f266])).
% 5.11/1.07  fof(f5966,plain,(
% 5.11/1.07    k3_xboole_0(k1_xboole_0,sK1) = k3_xboole_0(sK2,sK3)),
% 5.11/1.07    inference(superposition,[],[f2011,f5876])).
% 5.11/1.07  fof(f4366,plain,(
% 5.11/1.07    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK2,k3_xboole_0(sK2,sK3))),
% 5.11/1.07    inference(forward_demodulation,[],[f4365,f4302])).
% 5.11/1.07  fof(f4365,plain,(
% 5.11/1.07    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k3_xboole_0(sK2,sK3))),
% 5.11/1.07    inference(forward_demodulation,[],[f4359,f4101])).
% 5.11/1.07  fof(f4101,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK2,X0) = k3_xboole_0(sK2,k4_xboole_0(sK1,X0))) )),
% 5.11/1.07    inference(superposition,[],[f34,f4079])).
% 5.11/1.07  fof(f4079,plain,(
% 5.11/1.07    sK2 = k3_xboole_0(sK2,sK1)),
% 5.11/1.07    inference(forward_demodulation,[],[f4067,f25])).
% 5.11/1.07  fof(f4067,plain,(
% 5.11/1.07    k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,sK1)),
% 5.11/1.07    inference(superposition,[],[f28,f4048])).
% 5.11/1.07  fof(f4359,plain,(
% 5.11/1.07    k3_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK2,k3_xboole_0(sK2,sK3))),
% 5.11/1.07    inference(superposition,[],[f28,f4319])).
% 5.11/1.07  fof(f4319,plain,(
% 5.11/1.07    k3_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(superposition,[],[f28,f4302])).
% 5.11/1.07  fof(f4302,plain,(
% 5.11/1.07    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK1,sK3)),
% 5.11/1.07    inference(backward_demodulation,[],[f42,f4282])).
% 5.11/1.07  fof(f4282,plain,(
% 5.11/1.07    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3)),
% 5.11/1.07    inference(superposition,[],[f31,f4261])).
% 5.11/1.07  fof(f4261,plain,(
% 5.11/1.07    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3)),
% 5.11/1.07    inference(forward_demodulation,[],[f4260,f2346])).
% 5.11/1.07  fof(f2346,plain,(
% 5.11/1.07    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(forward_demodulation,[],[f2338,f20])).
% 5.11/1.07  fof(f2338,plain,(
% 5.11/1.07    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(superposition,[],[f84,f2313])).
% 5.11/1.07  fof(f84,plain,(
% 5.11/1.07    ( ! [X0] : (k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3))) )),
% 5.11/1.07    inference(superposition,[],[f44,f27])).
% 5.11/1.07  fof(f4260,plain,(
% 5.11/1.07    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(forward_demodulation,[],[f4259,f26])).
% 5.11/1.07  fof(f4259,plain,(
% 5.11/1.07    k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) = k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0)),
% 5.11/1.07    inference(forward_demodulation,[],[f4245,f27])).
% 5.11/1.07  fof(f4245,plain,(
% 5.11/1.07    k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK1,sK3),sK0)),
% 5.11/1.07    inference(superposition,[],[f29,f4196])).
% 5.11/1.07  fof(f4196,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(backward_demodulation,[],[f3206,f4193])).
% 5.11/1.07  fof(f4193,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(backward_demodulation,[],[f3055,f4174])).
% 5.11/1.07  fof(f4174,plain,(
% 5.11/1.07    k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK3)),
% 5.11/1.07    inference(superposition,[],[f4088,f20])).
% 5.11/1.07  fof(f4088,plain,(
% 5.11/1.07    ( ! [X0] : (k2_xboole_0(sK1,X0) = k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) )),
% 5.11/1.07    inference(superposition,[],[f36,f4073])).
% 5.11/1.07  fof(f4073,plain,(
% 5.11/1.07    sK1 = k2_xboole_0(sK1,sK2)),
% 5.11/1.07    inference(forward_demodulation,[],[f4066,f26])).
% 5.11/1.07  fof(f4066,plain,(
% 5.11/1.07    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2)),
% 5.11/1.07    inference(superposition,[],[f29,f4048])).
% 5.11/1.07  fof(f3055,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)))),
% 5.11/1.07    inference(forward_demodulation,[],[f3054,f266])).
% 5.11/1.07  fof(f3054,plain,(
% 5.11/1.07    k3_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)))),
% 5.11/1.07    inference(forward_demodulation,[],[f3053,f339])).
% 5.11/1.07  fof(f339,plain,(
% 5.11/1.07    ( ! [X3] : (k3_xboole_0(k1_xboole_0,X3) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X3,sK1))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f333,f28])).
% 5.11/1.07  fof(f333,plain,(
% 5.11/1.07    ( ! [X3] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X3,sK1))) )),
% 5.11/1.07    inference(superposition,[],[f28,f279])).
% 5.11/1.07  fof(f279,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK1))) )),
% 5.11/1.07    inference(superposition,[],[f263,f27])).
% 5.11/1.07  fof(f3053,plain,(
% 5.11/1.07    k3_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)))),
% 5.11/1.07    inference(backward_demodulation,[],[f799,f3052])).
% 5.11/1.07  fof(f3052,plain,(
% 5.11/1.07    ( ! [X6,X7] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(X6,X7)) = k4_xboole_0(sK0,k2_xboole_0(X6,k2_xboole_0(sK0,X7)))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f3051,f36])).
% 5.11/1.07  fof(f3051,plain,(
% 5.11/1.07    ( ! [X6,X7] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(X6,X7)) = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X6,sK0),X7))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f3050,f2251])).
% 5.11/1.07  fof(f2251,plain,(
% 5.11/1.07    ( ! [X4,X5] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X4,X5))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f2250,f2010])).
% 5.11/1.07  fof(f2250,plain,(
% 5.11/1.07    ( ! [X4,X5] : (k4_xboole_0(k1_xboole_0,k2_xboole_0(X4,X5)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f2236,f34])).
% 5.11/1.07  % (5892)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.11/1.07  fof(f2236,plain,(
% 5.11/1.07    ( ! [X4,X5] : (k4_xboole_0(k1_xboole_0,k2_xboole_0(X4,X5)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X4),X5)) )),
% 5.11/1.07    inference(superposition,[],[f35,f2010])).
% 5.11/1.07  fof(f3050,plain,(
% 5.11/1.07    ( ! [X6,X7] : (k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X6,sK0),X7)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f3039,f34])).
% 5.11/1.07  fof(f3039,plain,(
% 5.11/1.07    ( ! [X6,X7] : (k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X6,sK0),X7)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X6),X7)) )),
% 5.11/1.07    inference(superposition,[],[f35,f2838])).
% 5.11/1.07  fof(f2838,plain,(
% 5.11/1.07    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK0))) )),
% 5.11/1.07    inference(superposition,[],[f2154,f27])).
% 5.11/1.07  fof(f2154,plain,(
% 5.11/1.07    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f1995,f2010])).
% 5.11/1.07  fof(f799,plain,(
% 5.11/1.07    k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)))),
% 5.11/1.07    inference(superposition,[],[f31,f92])).
% 5.11/1.07  fof(f92,plain,(
% 5.11/1.07    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)))),
% 5.11/1.07    inference(forward_demodulation,[],[f83,f43])).
% 5.11/1.07  fof(f83,plain,(
% 5.11/1.07    k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)))),
% 5.11/1.07    inference(superposition,[],[f44,f51])).
% 5.11/1.07  fof(f3206,plain,(
% 5.11/1.07    k4_xboole_0(sK0,k2_xboole_0(sK1,sK3)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(superposition,[],[f31,f2346])).
% 5.11/1.07  fof(f4899,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK1,k2_xboole_0(X0,sK3))) )),
% 5.11/1.07    inference(superposition,[],[f4326,f27])).
% 5.11/1.07  fof(f4326,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,k2_xboole_0(sK3,X0))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f4317,f35])).
% 5.11/1.07  fof(f4317,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(k4_xboole_0(sK1,sK3),X0)) )),
% 5.11/1.07    inference(superposition,[],[f35,f4302])).
% 5.11/1.07  fof(f6049,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK2,X0) = k3_xboole_0(sK2,k4_xboole_0(sK2,X0))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f4327,f6047])).
% 5.11/1.07  fof(f6047,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK1,k2_xboole_0(sK3,X0))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f4326,f6043])).
% 5.11/1.07  fof(f4327,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k3_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK3,X0)))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f4036,f4326])).
% 5.11/1.07  fof(f4036,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k3_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,X0)))) )),
% 5.11/1.07    inference(superposition,[],[f2713,f48])).
% 5.11/1.07  fof(f48,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f45,f35])).
% 5.11/1.07  fof(f45,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X0)) = k4_xboole_0(k4_xboole_0(sK2,sK3),X0)) )),
% 5.11/1.07    inference(superposition,[],[f35,f42])).
% 5.11/1.07  fof(f7843,plain,(
% 5.11/1.07    k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,k4_xboole_0(sK1,sK0))),
% 5.11/1.07    inference(superposition,[],[f28,f7621])).
% 5.11/1.07  fof(f7621,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK0))),
% 5.11/1.07    inference(forward_demodulation,[],[f7615,f37])).
% 5.11/1.07  fof(f7615,plain,(
% 5.11/1.07    k3_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK0))),
% 5.11/1.07    inference(superposition,[],[f28,f7515])).
% 5.11/1.07  fof(f9193,plain,(
% 5.11/1.07    k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 5.11/1.07    inference(superposition,[],[f9191,f34])).
% 5.11/1.07  fof(f9191,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)),
% 5.11/1.07    inference(forward_demodulation,[],[f9183,f1981])).
% 5.11/1.07  fof(f9183,plain,(
% 5.11/1.07    k4_xboole_0(sK0,sK0) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)),
% 5.11/1.07    inference(superposition,[],[f31,f9141])).
% 5.11/1.07  fof(f9141,plain,(
% 5.11/1.07    sK0 = k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)),
% 5.11/1.07    inference(superposition,[],[f30,f9102])).
% 5.11/1.07  fof(f9102,plain,(
% 5.11/1.07    sK0 = k2_xboole_0(k3_xboole_0(sK0,sK1),sK3)),
% 5.11/1.07    inference(backward_demodulation,[],[f6437,f9101])).
% 5.11/1.07  fof(f9101,plain,(
% 5.11/1.07    sK0 = k2_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(forward_demodulation,[],[f9075,f2313])).
% 5.11/1.07  fof(f9075,plain,(
% 5.11/1.07    k2_xboole_0(sK0,sK0) = k2_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(superposition,[],[f7517,f7503])).
% 5.11/1.07  fof(f7503,plain,(
% 5.11/1.07    sK0 = k2_xboole_0(sK3,k3_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(backward_demodulation,[],[f6387,f7496])).
% 5.11/1.07  fof(f6387,plain,(
% 5.11/1.07    k2_xboole_0(sK0,sK3) = k2_xboole_0(sK3,k3_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(forward_demodulation,[],[f6372,f27])).
% 5.11/1.07  fof(f6372,plain,(
% 5.11/1.07    k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k3_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(superposition,[],[f29,f5978])).
% 5.11/1.07  fof(f5978,plain,(
% 5.11/1.07    k4_xboole_0(sK0,sK3) = k3_xboole_0(sK0,sK1)),
% 5.11/1.07    inference(superposition,[],[f28,f5876])).
% 5.11/1.07  fof(f7517,plain,(
% 5.11/1.07    ( ! [X0] : (k2_xboole_0(sK0,X0) = k2_xboole_0(sK0,k2_xboole_0(sK3,X0))) )),
% 5.11/1.07    inference(superposition,[],[f36,f7496])).
% 5.11/1.07  fof(f6437,plain,(
% 5.11/1.07    k2_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k2_xboole_0(k3_xboole_0(sK0,sK1),sK3)),
% 5.11/1.07    inference(forward_demodulation,[],[f6429,f27])).
% 5.11/1.07  fof(f6429,plain,(
% 5.11/1.07    k2_xboole_0(k3_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)),
% 5.11/1.07    inference(superposition,[],[f29,f6388])).
% 5.11/1.07  fof(f7806,plain,(
% 5.11/1.07    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,sK2)),
% 5.11/1.07    inference(forward_demodulation,[],[f7793,f5978])).
% 5.11/1.07  fof(f7793,plain,(
% 5.11/1.07    k4_xboole_0(sK0,sK3) = k3_xboole_0(sK0,sK2)),
% 5.11/1.07    inference(superposition,[],[f28,f7770])).
% 5.11/1.07  fof(f7770,plain,(
% 5.11/1.07    sK3 = k4_xboole_0(sK0,sK2)),
% 5.11/1.07    inference(forward_demodulation,[],[f7760,f7220])).
% 5.11/1.07  fof(f7220,plain,(
% 5.11/1.07    sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 5.11/1.07    inference(backward_demodulation,[],[f4344,f7219])).
% 5.11/1.07  fof(f7219,plain,(
% 5.11/1.07    sK3 = k4_xboole_0(sK3,sK2)),
% 5.11/1.07    inference(forward_demodulation,[],[f7194,f5875])).
% 5.11/1.07  fof(f7194,plain,(
% 5.11/1.07    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2)),
% 5.11/1.07    inference(superposition,[],[f5912,f4073])).
% 5.11/1.07  fof(f4344,plain,(
% 5.11/1.07    k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 5.11/1.07    inference(superposition,[],[f31,f4333])).
% 5.11/1.07  fof(f4333,plain,(
% 5.11/1.07    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 5.11/1.07    inference(forward_demodulation,[],[f4332,f4261])).
% 5.11/1.07  fof(f4332,plain,(
% 5.11/1.07    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK3)),
% 5.11/1.07    inference(forward_demodulation,[],[f4331,f27])).
% 5.11/1.07  fof(f4331,plain,(
% 5.11/1.07    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,sK1)),
% 5.11/1.07    inference(forward_demodulation,[],[f4318,f29])).
% 5.11/1.07  fof(f4318,plain,(
% 5.11/1.07    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k4_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(superposition,[],[f29,f4302])).
% 5.11/1.07  fof(f7760,plain,(
% 5.11/1.07    k4_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 5.11/1.07    inference(superposition,[],[f31,f7523])).
% 5.11/1.07  fof(f7523,plain,(
% 5.11/1.07    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2)),
% 5.11/1.07    inference(forward_demodulation,[],[f7514,f3120])).
% 5.11/1.07  fof(f3120,plain,(
% 5.11/1.07    ( ! [X1] : (k2_xboole_0(sK0,X1) = k2_xboole_0(sK0,k2_xboole_0(X1,sK0))) )),
% 5.11/1.07    inference(superposition,[],[f2875,f36])).
% 5.11/1.07  fof(f2875,plain,(
% 5.11/1.07    ( ! [X7] : (k2_xboole_0(sK0,X7) = k2_xboole_0(k2_xboole_0(sK0,X7),sK0)) )),
% 5.11/1.07    inference(forward_demodulation,[],[f2852,f2019])).
% 5.11/1.07  fof(f2019,plain,(
% 5.11/1.07    ( ! [X2] : (k2_xboole_0(sK0,X2) = k2_xboole_0(k2_xboole_0(sK0,X2),k3_xboole_0(k1_xboole_0,X2))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f147,f2010])).
% 5.11/1.07  fof(f147,plain,(
% 5.11/1.07    ( ! [X2] : (k2_xboole_0(sK0,X2) = k2_xboole_0(k2_xboole_0(sK0,X2),k4_xboole_0(k1_xboole_0,X2))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f140,f26])).
% 5.11/1.07  fof(f140,plain,(
% 5.11/1.07    ( ! [X2] : (k2_xboole_0(k2_xboole_0(sK0,X2),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK0,X2),k4_xboole_0(k1_xboole_0,X2))) )),
% 5.11/1.07    inference(superposition,[],[f29,f129])).
% 5.11/1.07  fof(f2852,plain,(
% 5.11/1.07    ( ! [X7] : (k2_xboole_0(k2_xboole_0(sK0,X7),sK0) = k2_xboole_0(k2_xboole_0(sK0,X7),k3_xboole_0(k1_xboole_0,X7))) )),
% 5.11/1.07    inference(superposition,[],[f29,f2154])).
% 5.11/1.07  fof(f7514,plain,(
% 5.11/1.07    k2_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))),
% 5.11/1.07    inference(superposition,[],[f5420,f7496])).
% 5.11/1.07  fof(f5420,plain,(
% 5.11/1.07    ( ! [X5] : (k2_xboole_0(sK0,k2_xboole_0(sK1,X5)) = k2_xboole_0(k2_xboole_0(X5,sK3),sK2)) )),
% 5.11/1.07    inference(forward_demodulation,[],[f5419,f4299])).
% 5.11/1.07  fof(f4299,plain,(
% 5.11/1.07    ( ! [X2] : (k2_xboole_0(sK0,k2_xboole_0(sK1,X2)) = k2_xboole_0(sK1,k2_xboole_0(X2,sK3))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f4176,f4295])).
% 5.11/1.07  fof(f4295,plain,(
% 5.11/1.07    ( ! [X1] : (k2_xboole_0(sK0,k2_xboole_0(sK1,X1)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK1,X1)))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f4175,f4292])).
% 5.11/1.07  fof(f4292,plain,(
% 5.11/1.07    ( ! [X0] : (k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,k2_xboole_0(sK3,X0))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f4281,f36])).
% 5.11/1.07  fof(f4281,plain,(
% 5.11/1.07    ( ! [X0] : (k2_xboole_0(k2_xboole_0(sK0,sK1),X0) = k2_xboole_0(sK1,k2_xboole_0(sK3,X0))) )),
% 5.11/1.07    inference(superposition,[],[f36,f4261])).
% 5.11/1.07  fof(f4175,plain,(
% 5.11/1.07    ( ! [X1] : (k2_xboole_0(sK1,k2_xboole_0(sK3,X1)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK1,X1)))) )),
% 5.11/1.07    inference(superposition,[],[f4088,f44])).
% 5.11/1.07  fof(f4176,plain,(
% 5.11/1.07    ( ! [X2] : (k2_xboole_0(sK1,k2_xboole_0(X2,sK3)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK1,X2)))) )),
% 5.11/1.07    inference(superposition,[],[f4088,f84])).
% 5.11/1.07  fof(f5419,plain,(
% 5.11/1.07    ( ! [X5] : (k2_xboole_0(k2_xboole_0(X5,sK3),sK2) = k2_xboole_0(sK1,k2_xboole_0(X5,sK3))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f5418,f27])).
% 5.11/1.07  fof(f5418,plain,(
% 5.11/1.07    ( ! [X5] : (k2_xboole_0(k2_xboole_0(X5,sK3),sK2) = k2_xboole_0(k2_xboole_0(X5,sK3),sK1)) )),
% 5.11/1.07    inference(forward_demodulation,[],[f5411,f29])).
% 5.11/1.07  fof(f5411,plain,(
% 5.11/1.07    ( ! [X5] : (k2_xboole_0(k2_xboole_0(X5,sK3),sK2) = k2_xboole_0(k2_xboole_0(X5,sK3),k4_xboole_0(sK1,k2_xboole_0(X5,sK3)))) )),
% 5.11/1.07    inference(superposition,[],[f29,f4899])).
% 5.11/1.07  fof(f6388,plain,(
% 5.11/1.07    sK3 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(forward_demodulation,[],[f6373,f5971])).
% 5.11/1.07  fof(f5971,plain,(
% 5.11/1.07    sK3 = k3_xboole_0(sK0,sK3)),
% 5.11/1.07    inference(superposition,[],[f2199,f5876])).
% 5.11/1.07  fof(f2199,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK0,X0) = k3_xboole_0(sK0,k4_xboole_0(sK0,X0))) )),
% 5.11/1.07    inference(superposition,[],[f34,f2184])).
% 5.11/1.07  fof(f2184,plain,(
% 5.11/1.07    sK0 = k3_xboole_0(sK0,sK0)),
% 5.11/1.07    inference(forward_demodulation,[],[f1997,f25])).
% 5.11/1.07  fof(f1997,plain,(
% 5.11/1.07    k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK0)),
% 5.11/1.07    inference(superposition,[],[f28,f1981])).
% 5.11/1.07  fof(f6373,plain,(
% 5.11/1.07    k3_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(superposition,[],[f28,f5978])).
% 5.11/1.07  fof(f7933,plain,(
% 5.11/1.07    sK3 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK0))),
% 5.11/1.07    inference(backward_demodulation,[],[f7217,f7912])).
% 5.11/1.07  fof(f7912,plain,(
% 5.11/1.07    k3_xboole_0(sK1,sK0) = k3_xboole_0(sK1,sK3)),
% 5.11/1.07    inference(backward_demodulation,[],[f6076,f7902])).
% 5.11/1.07  fof(f7902,plain,(
% 5.11/1.07    k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK2)),
% 5.11/1.07    inference(superposition,[],[f28,f7853])).
% 5.11/1.07  fof(f6076,plain,(
% 5.11/1.07    k4_xboole_0(sK1,sK2) = k3_xboole_0(sK1,sK3)),
% 5.11/1.07    inference(superposition,[],[f28,f5991])).
% 5.11/1.07  fof(f7217,plain,(
% 5.11/1.07    sK3 = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(forward_demodulation,[],[f7192,f5875])).
% 5.11/1.07  fof(f7192,plain,(
% 5.11/1.07    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k3_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(superposition,[],[f5912,f6194])).
% 5.11/1.07  fof(f6194,plain,(
% 5.11/1.07    sK1 = k2_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(forward_demodulation,[],[f6181,f2313])).
% 5.11/1.07  fof(f6181,plain,(
% 5.11/1.07    k2_xboole_0(sK1,sK1) = k2_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(superposition,[],[f4203,f6076])).
% 5.11/1.07  fof(f4203,plain,(
% 5.11/1.07    ( ! [X6] : (k2_xboole_0(sK1,X6) = k2_xboole_0(sK1,k4_xboole_0(X6,sK2))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f4181,f4088])).
% 5.11/1.07  fof(f4181,plain,(
% 5.11/1.07    ( ! [X6] : (k2_xboole_0(sK1,k2_xboole_0(sK2,X6)) = k2_xboole_0(sK1,k4_xboole_0(X6,sK2))) )),
% 5.11/1.07    inference(superposition,[],[f4088,f29])).
% 5.11/1.07  fof(f8519,plain,(
% 5.11/1.07    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,k3_xboole_0(sK1,sK0)))),
% 5.11/1.07    inference(superposition,[],[f7915,f34])).
% 5.11/1.07  fof(f7915,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0))),
% 5.11/1.07    inference(backward_demodulation,[],[f6091,f7912])).
% 5.11/1.07  fof(f6091,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(backward_demodulation,[],[f5737,f6076])).
% 5.11/1.07  fof(f5737,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))),
% 5.11/1.07    inference(forward_demodulation,[],[f5736,f300])).
% 5.11/1.07  fof(f300,plain,(
% 5.11/1.07    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)),
% 5.11/1.07    inference(forward_demodulation,[],[f299,f25])).
% 5.11/1.07  fof(f299,plain,(
% 5.11/1.07    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK2)),
% 5.11/1.07    inference(superposition,[],[f28,f283])).
% 5.11/1.07  fof(f283,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 5.11/1.07    inference(superposition,[],[f263,f257])).
% 5.11/1.07  fof(f257,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))),
% 5.11/1.07    inference(backward_demodulation,[],[f142,f255])).
% 5.11/1.07  fof(f142,plain,(
% 5.11/1.07    k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,sK1)),
% 5.11/1.07    inference(forward_demodulation,[],[f134,f129])).
% 5.11/1.07  fof(f134,plain,(
% 5.11/1.07    k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))),
% 5.11/1.07    inference(superposition,[],[f129,f108])).
% 5.11/1.07  fof(f108,plain,(
% 5.11/1.07    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 5.11/1.07    inference(forward_demodulation,[],[f102,f43])).
% 5.11/1.07  fof(f102,plain,(
% 5.11/1.07    k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 5.11/1.07    inference(superposition,[],[f84,f20])).
% 5.11/1.07  fof(f5736,plain,(
% 5.11/1.07    k3_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))),
% 5.11/1.07    inference(forward_demodulation,[],[f5734,f1142])).
% 5.11/1.07  fof(f1142,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X0)) = k3_xboole_0(k1_xboole_0,X0)) )),
% 5.11/1.07    inference(backward_demodulation,[],[f311,f1141])).
% 5.11/1.07  fof(f1141,plain,(
% 5.11/1.07    ( ! [X14] : (k3_xboole_0(k1_xboole_0,X14) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X14))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f1140,f28])).
% 5.11/1.07  fof(f1140,plain,(
% 5.11/1.07    ( ! [X14] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X14)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X14))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f1104,f311])).
% 5.11/1.07  fof(f1104,plain,(
% 5.11/1.07    ( ! [X14] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X14)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X14))) )),
% 5.11/1.07    inference(superposition,[],[f1062,f268])).
% 5.11/1.07  fof(f268,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X0))) )),
% 5.11/1.07    inference(superposition,[],[f34,f266])).
% 5.11/1.07  fof(f1062,plain,(
% 5.11/1.07    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f156,f1059])).
% 5.11/1.07  fof(f311,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X0))) )),
% 5.11/1.07    inference(superposition,[],[f268,f28])).
% 5.11/1.07  fof(f5734,plain,(
% 5.11/1.07    k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))),
% 5.11/1.07    inference(superposition,[],[f31,f5635])).
% 5.11/1.07  fof(f5635,plain,(
% 5.11/1.07    k4_xboole_0(sK1,sK2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))),
% 5.11/1.07    inference(superposition,[],[f1740,f300])).
% 5.11/1.07  fof(f1740,plain,(
% 5.11/1.07    ( ! [X1] : (k4_xboole_0(sK1,X1) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k4_xboole_0(sK1,X1))) )),
% 5.11/1.07    inference(superposition,[],[f1145,f27])).
% 5.11/1.07  fof(f1145,plain,(
% 5.11/1.07    ( ! [X2] : (k4_xboole_0(sK1,X2) = k2_xboole_0(k4_xboole_0(sK1,X2),k3_xboole_0(k1_xboole_0,X2))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f320,f1141])).
% 5.11/1.07  fof(f320,plain,(
% 5.11/1.07    ( ! [X2] : (k4_xboole_0(sK1,X2) = k2_xboole_0(k4_xboole_0(sK1,X2),k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X2)))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f262,f318])).
% 5.11/1.07  fof(f318,plain,(
% 5.11/1.07    ( ! [X0] : (k3_xboole_0(sK3,k3_xboole_0(sK1,X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X0))) )),
% 5.11/1.07    inference(backward_demodulation,[],[f65,f311])).
% 5.11/1.07  fof(f262,plain,(
% 5.11/1.07    ( ! [X2] : (k4_xboole_0(sK1,X2) = k2_xboole_0(k4_xboole_0(sK1,X2),k3_xboole_0(sK3,k3_xboole_0(sK1,X2)))) )),
% 5.11/1.07    inference(forward_demodulation,[],[f252,f26])).
% 5.11/1.07  fof(f252,plain,(
% 5.11/1.07    ( ! [X2] : (k2_xboole_0(k4_xboole_0(sK1,X2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,X2),k3_xboole_0(sK3,k3_xboole_0(sK1,X2)))) )),
% 5.11/1.07    inference(superposition,[],[f29,f65])).
% 5.11/1.07  fof(f7924,plain,(
% 5.11/1.07    sK2 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK0))),
% 5.11/1.07    inference(backward_demodulation,[],[f6203,f7912])).
% 5.11/1.07  fof(f6203,plain,(
% 5.11/1.07    sK2 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(forward_demodulation,[],[f6187,f6068])).
% 5.11/1.07  fof(f6068,plain,(
% 5.11/1.07    sK2 = k3_xboole_0(sK1,sK2)),
% 5.11/1.07    inference(superposition,[],[f4535,f5991])).
% 5.11/1.07  fof(f4535,plain,(
% 5.11/1.07    ( ! [X0] : (k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k4_xboole_0(sK1,X0))) )),
% 5.11/1.07    inference(superposition,[],[f34,f4529])).
% 5.11/1.07  fof(f4529,plain,(
% 5.11/1.07    sK1 = k3_xboole_0(sK1,sK1)),
% 5.11/1.07    inference(forward_demodulation,[],[f4518,f25])).
% 5.11/1.07  fof(f4518,plain,(
% 5.11/1.07    k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,sK1)),
% 5.11/1.07    inference(superposition,[],[f28,f4505])).
% 5.11/1.07  fof(f4505,plain,(
% 5.11/1.07    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 5.11/1.07    inference(forward_demodulation,[],[f4498,f4048])).
% 5.11/1.07  fof(f4498,plain,(
% 5.11/1.07    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK2,sK1)),
% 5.11/1.07    inference(superposition,[],[f31,f4468])).
% 5.11/1.07  fof(f4468,plain,(
% 5.11/1.07    sK1 = k2_xboole_0(sK2,sK1)),
% 5.11/1.07    inference(superposition,[],[f4138,f4073])).
% 5.11/1.07  fof(f6187,plain,(
% 5.11/1.07    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 5.11/1.07    inference(superposition,[],[f28,f6076])).
% 5.11/1.07  % SZS output end Proof for theBenchmark
% 5.11/1.07  % (5850)------------------------------
% 5.11/1.07  % (5850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.11/1.07  % (5850)Termination reason: Refutation
% 5.11/1.07  
% 5.11/1.07  % (5850)Memory used [KB]: 4733
% 5.11/1.07  % (5850)Time elapsed: 0.638 s
% 5.11/1.07  % (5850)------------------------------
% 5.11/1.07  % (5850)------------------------------
% 5.11/1.08  % (5826)Success in time 0.715 s
%------------------------------------------------------------------------------
