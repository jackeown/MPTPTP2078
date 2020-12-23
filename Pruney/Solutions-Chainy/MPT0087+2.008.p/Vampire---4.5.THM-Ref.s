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
% DateTime   : Thu Dec  3 12:31:28 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   87 (4104 expanded)
%              Number of leaves         :    8 ( 982 expanded)
%              Depth                    :   41
%              Number of atoms          :  141 (11554 expanded)
%              Number of equality atoms :   71 (2368 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4385,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4379,f34])).

fof(f34,plain,(
    r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0) ),
    inference(resolution,[],[f15,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f15,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

fof(f4379,plain,(
    ~ r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0) ),
    inference(resolution,[],[f4342,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f14,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f4342,plain,(
    r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK1) ),
    inference(resolution,[],[f4212,f35])).

fof(f35,plain,(
    r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f15,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4212,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X16,k4_xboole_0(X14,X15))
      | r2_hidden(X16,X14) ) ),
    inference(superposition,[],[f31,f4007])).

fof(f4007,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k3_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(superposition,[],[f3992,f3811])).

fof(f3811,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k4_xboole_0(X7,X8)) = X7 ),
    inference(forward_demodulation,[],[f3808,f3670])).

fof(f3670,plain,(
    ! [X3] : k2_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f3665,f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f3665,plain,(
    ! [X3] : k2_xboole_0(X3,k1_xboole_0) = k2_xboole_0(X3,X3) ),
    inference(superposition,[],[f18,f3645])).

fof(f3645,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f3294,f17])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f3294,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f3281,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f3281,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f3277,f2866])).

fof(f2866,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X4,k1_xboole_0)) = X4 ),
    inference(backward_demodulation,[],[f2642,f2696])).

fof(f2696,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f825,f2667])).

fof(f2667,plain,(
    k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f189,f2557])).

fof(f2557,plain,(
    ! [X5] : k3_xboole_0(sK0,sK1) = k3_xboole_0(X5,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2553,f115])).

fof(f115,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,sK0)
    | k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f85,f68])).

fof(f68,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK4(sK0,sK1,k3_xboole_0(X11,X12)),X12)
      | k3_xboole_0(sK0,sK1) = k3_xboole_0(X11,X12) ) ),
    inference(resolution,[],[f57,f31])).

fof(f57,plain,(
    ! [X2] :
      ( r2_hidden(sK4(sK0,sK1,X2),X2)
      | k3_xboole_0(sK0,sK1) = X2 ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X2] :
      ( r2_hidden(sK4(sK0,sK1,X2),X2)
      | k3_xboole_0(sK0,sK1) = X2
      | r2_hidden(sK4(sK0,sK1,X2),X2)
      | k3_xboole_0(sK0,sK1) = X2 ) ),
    inference(resolution,[],[f40,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f40,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK4(X6,sK1,X7),sK0)
      | r2_hidden(sK4(X6,sK1,X7),X7)
      | k3_xboole_0(X6,sK1) = X7 ) ),
    inference(resolution,[],[f33,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f85,plain,(
    ! [X21] :
      ( ~ r2_hidden(sK4(sK0,sK1,k3_xboole_0(sK1,X21)),sK0)
      | k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,X21) ) ),
    inference(resolution,[],[f67,f33])).

fof(f67,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK4(sK0,sK1,k3_xboole_0(X9,X10)),X9)
      | k3_xboole_0(sK0,sK1) = k3_xboole_0(X9,X10) ) ),
    inference(resolution,[],[f57,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f2553,plain,(
    ! [X5] : k3_xboole_0(sK0,sK1) = k3_xboole_0(X5,k3_xboole_0(sK1,sK0)) ),
    inference(duplicate_literal_removal,[],[f2536])).

fof(f2536,plain,(
    ! [X5] :
      ( k3_xboole_0(sK0,sK1) = k3_xboole_0(X5,k3_xboole_0(sK1,sK0))
      | k3_xboole_0(sK0,sK1) = k3_xboole_0(X5,k3_xboole_0(sK1,sK0)) ) ),
    inference(resolution,[],[f1056,f102])).

fof(f102,plain,(
    ! [X19,X20,X18] :
      ( r2_hidden(sK4(sK0,sK1,k3_xboole_0(X18,k3_xboole_0(X19,X20))),X20)
      | k3_xboole_0(sK0,sK1) = k3_xboole_0(X18,k3_xboole_0(X19,X20)) ) ),
    inference(resolution,[],[f68,f31])).

fof(f1056,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(sK4(sK0,sK1,k3_xboole_0(X37,k3_xboole_0(sK1,X38))),sK0)
      | k3_xboole_0(sK0,sK1) = k3_xboole_0(X37,k3_xboole_0(sK1,X38)) ) ),
    inference(resolution,[],[f101,f33])).

fof(f101,plain,(
    ! [X17,X15,X16] :
      ( r2_hidden(sK4(sK0,sK1,k3_xboole_0(X15,k3_xboole_0(X16,X17))),X16)
      | k3_xboole_0(sK0,sK1) = k3_xboole_0(X15,k3_xboole_0(X16,X17)) ) ),
    inference(resolution,[],[f68,f32])).

fof(f189,plain,(
    ! [X3] : k1_xboole_0 = k2_xboole_0(k3_xboole_0(k1_xboole_0,X3),k1_xboole_0) ),
    inference(superposition,[],[f19,f180])).

fof(f180,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f178,f17])).

fof(f178,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f23,f176])).

fof(f176,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f17,f172])).

fof(f172,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f171,f16])).

fof(f171,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f18,f165])).

fof(f165,plain,(
    k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f17,f161])).

fof(f161,plain,(
    k1_xboole_0 = k2_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f19,f153])).

fof(f153,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f147,f132])).

fof(f132,plain,(
    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f17,f120])).

fof(f120,plain,(
    sK1 = k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f19,f115])).

fof(f147,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),sK1) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f136,f16])).

fof(f136,plain,(
    ! [X0] : k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK1,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f23,f132])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f825,plain,(
    k3_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f137,f824])).

fof(f824,plain,(
    ! [X0] : k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,X0),sK1) ),
    inference(duplicate_literal_removal,[],[f805])).

fof(f805,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,X0),sK1)
      | k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,X0),sK1) ) ),
    inference(resolution,[],[f83,f103])).

fof(f103,plain,(
    ! [X21] :
      ( ~ r2_hidden(sK4(sK0,sK1,k3_xboole_0(X21,sK1)),sK0)
      | k3_xboole_0(sK0,sK1) = k3_xboole_0(X21,sK1) ) ),
    inference(resolution,[],[f68,f33])).

fof(f83,plain,(
    ! [X17,X15,X16] :
      ( r2_hidden(sK4(sK0,sK1,k3_xboole_0(k3_xboole_0(X15,X16),X17)),X15)
      | k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(X15,X16),X17) ) ),
    inference(resolution,[],[f67,f32])).

fof(f137,plain,(
    k3_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK1),sK1),k1_xboole_0) ),
    inference(superposition,[],[f19,f132])).

fof(f2642,plain,(
    ! [X4] : k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X4,k3_xboole_0(sK0,sK1))) = X4 ),
    inference(superposition,[],[f19,f2557])).

fof(f3277,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f2866,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f3808,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k1_xboole_0) = k2_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f18,f3776])).

fof(f3776,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f3668,f19])).

fof(f3668,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f3662,f18])).

fof(f3662,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f3645,f23])).

fof(f3992,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X3,X2)) = X2 ),
    inference(superposition,[],[f3782,f3670])).

fof(f3782,plain,(
    ! [X4,X5] : k2_xboole_0(k3_xboole_0(X4,k2_xboole_0(X5,X4)),k1_xboole_0) = X4 ),
    inference(superposition,[],[f19,f3668])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:20:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (812154880)
% 0.14/0.37  ipcrm: permission denied for id (816218113)
% 0.14/0.37  ipcrm: permission denied for id (812220418)
% 0.14/0.37  ipcrm: permission denied for id (812253188)
% 0.14/0.37  ipcrm: permission denied for id (816283653)
% 0.14/0.38  ipcrm: permission denied for id (812351495)
% 0.14/0.38  ipcrm: permission denied for id (816349192)
% 0.14/0.38  ipcrm: permission denied for id (812417034)
% 0.14/0.38  ipcrm: permission denied for id (812449803)
% 0.14/0.38  ipcrm: permission denied for id (812482572)
% 0.14/0.38  ipcrm: permission denied for id (812515341)
% 0.14/0.38  ipcrm: permission denied for id (816414734)
% 0.14/0.39  ipcrm: permission denied for id (812548111)
% 0.21/0.39  ipcrm: permission denied for id (816480273)
% 0.21/0.39  ipcrm: permission denied for id (812646418)
% 0.21/0.39  ipcrm: permission denied for id (812679187)
% 0.21/0.39  ipcrm: permission denied for id (812711956)
% 0.21/0.39  ipcrm: permission denied for id (816513045)
% 0.21/0.39  ipcrm: permission denied for id (816545814)
% 0.21/0.39  ipcrm: permission denied for id (816578583)
% 0.21/0.40  ipcrm: permission denied for id (816611352)
% 0.21/0.40  ipcrm: permission denied for id (812875801)
% 0.21/0.40  ipcrm: permission denied for id (812908570)
% 0.21/0.40  ipcrm: permission denied for id (812941339)
% 0.21/0.40  ipcrm: permission denied for id (816644124)
% 0.21/0.40  ipcrm: permission denied for id (813039647)
% 0.21/0.41  ipcrm: permission denied for id (816775201)
% 0.21/0.41  ipcrm: permission denied for id (813137954)
% 0.21/0.41  ipcrm: permission denied for id (816807971)
% 0.21/0.41  ipcrm: permission denied for id (816840740)
% 0.21/0.41  ipcrm: permission denied for id (813269030)
% 0.21/0.41  ipcrm: permission denied for id (813301799)
% 0.21/0.42  ipcrm: permission denied for id (813334568)
% 0.21/0.42  ipcrm: permission denied for id (813367337)
% 0.21/0.42  ipcrm: permission denied for id (813400106)
% 0.21/0.42  ipcrm: permission denied for id (813465644)
% 0.21/0.42  ipcrm: permission denied for id (816971822)
% 0.21/0.42  ipcrm: permission denied for id (817004591)
% 0.21/0.43  ipcrm: permission denied for id (817037360)
% 0.21/0.43  ipcrm: permission denied for id (813662257)
% 0.21/0.43  ipcrm: permission denied for id (813695026)
% 0.21/0.43  ipcrm: permission denied for id (813727795)
% 0.21/0.43  ipcrm: permission denied for id (813760564)
% 0.21/0.43  ipcrm: permission denied for id (813826102)
% 0.21/0.44  ipcrm: permission denied for id (813891641)
% 0.21/0.44  ipcrm: permission denied for id (813924410)
% 0.21/0.44  ipcrm: permission denied for id (813957179)
% 0.21/0.44  ipcrm: permission denied for id (813989948)
% 0.21/0.44  ipcrm: permission denied for id (814022717)
% 0.21/0.44  ipcrm: permission denied for id (814055486)
% 0.21/0.44  ipcrm: permission denied for id (814088255)
% 0.21/0.45  ipcrm: permission denied for id (814121024)
% 0.21/0.45  ipcrm: permission denied for id (814153793)
% 0.21/0.45  ipcrm: permission denied for id (814186562)
% 0.21/0.45  ipcrm: permission denied for id (817201219)
% 0.21/0.45  ipcrm: permission denied for id (817233988)
% 0.21/0.45  ipcrm: permission denied for id (814284869)
% 0.21/0.45  ipcrm: permission denied for id (814350407)
% 0.21/0.46  ipcrm: permission denied for id (814383176)
% 0.21/0.46  ipcrm: permission denied for id (814415945)
% 0.21/0.46  ipcrm: permission denied for id (817299530)
% 0.21/0.46  ipcrm: permission denied for id (817365068)
% 0.21/0.46  ipcrm: permission denied for id (814547021)
% 0.21/0.46  ipcrm: permission denied for id (814579790)
% 0.21/0.46  ipcrm: permission denied for id (814612559)
% 0.21/0.47  ipcrm: permission denied for id (814645328)
% 0.21/0.47  ipcrm: permission denied for id (814743635)
% 0.21/0.47  ipcrm: permission denied for id (814776404)
% 0.21/0.47  ipcrm: permission denied for id (817463381)
% 0.21/0.47  ipcrm: permission denied for id (817528919)
% 0.21/0.47  ipcrm: permission denied for id (817561688)
% 0.21/0.48  ipcrm: permission denied for id (814940249)
% 0.21/0.48  ipcrm: permission denied for id (814973018)
% 0.21/0.48  ipcrm: permission denied for id (815005787)
% 0.21/0.48  ipcrm: permission denied for id (815038556)
% 0.21/0.48  ipcrm: permission denied for id (815071325)
% 0.21/0.49  ipcrm: permission denied for id (815202401)
% 0.21/0.49  ipcrm: permission denied for id (815267939)
% 0.21/0.49  ipcrm: permission denied for id (817725540)
% 0.21/0.49  ipcrm: permission denied for id (815333477)
% 0.21/0.49  ipcrm: permission denied for id (815399015)
% 0.21/0.49  ipcrm: permission denied for id (817791080)
% 0.21/0.50  ipcrm: permission denied for id (817823849)
% 0.21/0.50  ipcrm: permission denied for id (815497322)
% 0.21/0.50  ipcrm: permission denied for id (817856619)
% 0.21/0.50  ipcrm: permission denied for id (815595629)
% 0.21/0.50  ipcrm: permission denied for id (815726703)
% 0.21/0.50  ipcrm: permission denied for id (815759472)
% 0.21/0.51  ipcrm: permission denied for id (815825011)
% 0.21/0.51  ipcrm: permission denied for id (815857780)
% 0.21/0.51  ipcrm: permission denied for id (815890549)
% 0.21/0.51  ipcrm: permission denied for id (815923318)
% 0.21/0.51  ipcrm: permission denied for id (818053240)
% 0.21/0.52  ipcrm: permission denied for id (816054394)
% 0.21/0.52  ipcrm: permission denied for id (818118779)
% 0.35/0.52  ipcrm: permission denied for id (816119933)
% 0.35/0.52  ipcrm: permission denied for id (818184318)
% 0.35/0.52  ipcrm: permission denied for id (816185471)
% 0.38/0.62  % (25678)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.38/0.62  % (25685)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.38/0.63  % (25681)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.38/0.64  % (25693)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.38/0.64  % (25690)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.38/0.65  % (25679)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.38/0.65  % (25687)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.38/0.65  % (25692)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.38/0.65  % (25677)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.38/0.66  % (25683)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.38/0.66  % (25694)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.38/0.67  % (25680)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.38/0.67  % (25684)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.38/0.67  % (25691)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.38/0.67  % (25676)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.38/0.67  % (25682)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.38/0.67  % (25696)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.38/0.67  % (25676)Refutation not found, incomplete strategy% (25676)------------------------------
% 0.38/0.67  % (25676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.67  % (25676)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.67  
% 0.38/0.67  % (25676)Memory used [KB]: 6140
% 0.38/0.67  % (25676)Time elapsed: 0.063 s
% 0.38/0.67  % (25676)------------------------------
% 0.38/0.67  % (25676)------------------------------
% 0.38/0.68  % (25688)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.38/0.68  % (25697)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.38/0.68  % (25697)Refutation not found, incomplete strategy% (25697)------------------------------
% 0.38/0.68  % (25697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.68  % (25697)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.68  
% 0.38/0.68  % (25697)Memory used [KB]: 10618
% 0.38/0.68  % (25697)Time elapsed: 0.103 s
% 0.38/0.68  % (25697)------------------------------
% 0.38/0.68  % (25697)------------------------------
% 0.38/0.68  % (25689)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.48/0.69  % (25695)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.48/0.81  % (25690)Refutation found. Thanks to Tanya!
% 0.48/0.81  % SZS status Theorem for theBenchmark
% 0.48/0.81  % SZS output start Proof for theBenchmark
% 0.48/0.81  fof(f4385,plain,(
% 0.48/0.81    $false),
% 0.48/0.81    inference(subsumption_resolution,[],[f4379,f34])).
% 0.48/0.81  fof(f34,plain,(
% 0.48/0.81    r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0)),
% 0.48/0.81    inference(resolution,[],[f15,f21])).
% 0.48/0.81  fof(f21,plain,(
% 0.48/0.81    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.48/0.81    inference(cnf_transformation,[],[f13])).
% 0.48/0.81  fof(f13,plain,(
% 0.48/0.81    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.48/0.81    inference(ennf_transformation,[],[f11])).
% 0.48/0.81  fof(f11,plain,(
% 0.48/0.81    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.48/0.81    inference(rectify,[],[f3])).
% 0.48/0.81  fof(f3,axiom,(
% 0.48/0.81    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.48/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.48/0.81  fof(f15,plain,(
% 0.48/0.81    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.48/0.81    inference(cnf_transformation,[],[f12])).
% 0.48/0.81  fof(f12,plain,(
% 0.48/0.81    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 0.48/0.81    inference(ennf_transformation,[],[f9])).
% 0.48/0.81  fof(f9,negated_conjecture,(
% 0.48/0.81    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.48/0.81    inference(negated_conjecture,[],[f8])).
% 0.48/0.81  fof(f8,conjecture,(
% 0.48/0.81    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.48/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).
% 0.48/0.81  fof(f4379,plain,(
% 0.48/0.81    ~r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0)),
% 0.48/0.81    inference(resolution,[],[f4342,f33])).
% 0.48/0.81  fof(f33,plain,(
% 0.48/0.81    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.48/0.81    inference(resolution,[],[f14,f20])).
% 0.48/0.81  fof(f20,plain,(
% 0.48/0.81    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.48/0.81    inference(cnf_transformation,[],[f13])).
% 0.48/0.81  fof(f14,plain,(
% 0.48/0.81    r1_xboole_0(sK0,sK1)),
% 0.48/0.81    inference(cnf_transformation,[],[f12])).
% 0.48/0.81  fof(f4342,plain,(
% 0.48/0.81    r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK1)),
% 0.48/0.81    inference(resolution,[],[f4212,f35])).
% 0.48/0.81  fof(f35,plain,(
% 0.48/0.81    r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))),
% 0.48/0.81    inference(resolution,[],[f15,f22])).
% 0.48/0.81  fof(f22,plain,(
% 0.48/0.81    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1)) )),
% 0.48/0.81    inference(cnf_transformation,[],[f13])).
% 0.48/0.81  fof(f4212,plain,(
% 0.48/0.81    ( ! [X14,X15,X16] : (~r2_hidden(X16,k4_xboole_0(X14,X15)) | r2_hidden(X16,X14)) )),
% 0.48/0.81    inference(superposition,[],[f31,f4007])).
% 0.48/0.81  fof(f4007,plain,(
% 0.48/0.81    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k3_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 0.48/0.81    inference(superposition,[],[f3992,f3811])).
% 0.48/0.81  fof(f3811,plain,(
% 0.48/0.81    ( ! [X8,X7] : (k2_xboole_0(X7,k4_xboole_0(X7,X8)) = X7) )),
% 0.48/0.81    inference(forward_demodulation,[],[f3808,f3670])).
% 0.48/0.81  fof(f3670,plain,(
% 0.48/0.81    ( ! [X3] : (k2_xboole_0(X3,k1_xboole_0) = X3) )),
% 0.48/0.81    inference(forward_demodulation,[],[f3665,f16])).
% 0.48/0.81  fof(f16,plain,(
% 0.48/0.81    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.48/0.81    inference(cnf_transformation,[],[f10])).
% 0.48/0.81  fof(f10,plain,(
% 0.48/0.81    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.48/0.81    inference(rectify,[],[f2])).
% 0.48/0.81  fof(f2,axiom,(
% 0.48/0.81    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.48/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.48/0.81  fof(f3665,plain,(
% 0.48/0.81    ( ! [X3] : (k2_xboole_0(X3,k1_xboole_0) = k2_xboole_0(X3,X3)) )),
% 0.48/0.81    inference(superposition,[],[f18,f3645])).
% 0.48/0.81  fof(f3645,plain,(
% 0.48/0.81    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.48/0.81    inference(superposition,[],[f3294,f17])).
% 0.48/0.81  fof(f17,plain,(
% 0.48/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.48/0.81    inference(cnf_transformation,[],[f6])).
% 0.48/0.81  fof(f6,axiom,(
% 0.48/0.81    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.48/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.48/0.81  fof(f3294,plain,(
% 0.48/0.81    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))) )),
% 0.48/0.81    inference(superposition,[],[f3281,f23])).
% 0.48/0.81  fof(f23,plain,(
% 0.48/0.81    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.48/0.81    inference(cnf_transformation,[],[f5])).
% 0.48/0.81  fof(f5,axiom,(
% 0.48/0.81    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.48/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.48/0.81  fof(f3281,plain,(
% 0.48/0.81    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.48/0.81    inference(superposition,[],[f3277,f2866])).
% 0.48/0.81  fof(f2866,plain,(
% 0.48/0.81    ( ! [X4] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X4,k1_xboole_0)) = X4) )),
% 0.48/0.81    inference(backward_demodulation,[],[f2642,f2696])).
% 0.48/0.81  fof(f2696,plain,(
% 0.48/0.81    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.48/0.81    inference(backward_demodulation,[],[f825,f2667])).
% 0.48/0.81  fof(f2667,plain,(
% 0.48/0.81    k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.48/0.81    inference(superposition,[],[f189,f2557])).
% 0.48/0.81  fof(f2557,plain,(
% 0.48/0.81    ( ! [X5] : (k3_xboole_0(sK0,sK1) = k3_xboole_0(X5,k3_xboole_0(sK0,sK1))) )),
% 0.48/0.81    inference(forward_demodulation,[],[f2553,f115])).
% 0.48/0.81  fof(f115,plain,(
% 0.48/0.81    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,sK0)),
% 0.48/0.81    inference(duplicate_literal_removal,[],[f108])).
% 0.48/0.81  fof(f108,plain,(
% 0.48/0.81    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,sK0) | k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,sK0)),
% 0.48/0.81    inference(resolution,[],[f85,f68])).
% 0.48/0.81  fof(f68,plain,(
% 0.48/0.81    ( ! [X12,X11] : (r2_hidden(sK4(sK0,sK1,k3_xboole_0(X11,X12)),X12) | k3_xboole_0(sK0,sK1) = k3_xboole_0(X11,X12)) )),
% 0.48/0.81    inference(resolution,[],[f57,f31])).
% 0.48/0.81  fof(f57,plain,(
% 0.48/0.81    ( ! [X2] : (r2_hidden(sK4(sK0,sK1,X2),X2) | k3_xboole_0(sK0,sK1) = X2) )),
% 0.48/0.81    inference(duplicate_literal_removal,[],[f54])).
% 0.48/0.81  fof(f54,plain,(
% 0.48/0.81    ( ! [X2] : (r2_hidden(sK4(sK0,sK1,X2),X2) | k3_xboole_0(sK0,sK1) = X2 | r2_hidden(sK4(sK0,sK1,X2),X2) | k3_xboole_0(sK0,sK1) = X2) )),
% 0.48/0.81    inference(resolution,[],[f40,f25])).
% 0.48/0.81  fof(f25,plain,(
% 0.48/0.81    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.48/0.81    inference(cnf_transformation,[],[f1])).
% 0.48/0.81  fof(f1,axiom,(
% 0.48/0.81    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.48/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.48/0.81  fof(f40,plain,(
% 0.48/0.81    ( ! [X6,X7] : (~r2_hidden(sK4(X6,sK1,X7),sK0) | r2_hidden(sK4(X6,sK1,X7),X7) | k3_xboole_0(X6,sK1) = X7) )),
% 0.48/0.81    inference(resolution,[],[f33,f26])).
% 0.48/0.81  fof(f26,plain,(
% 0.48/0.81    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.48/0.81    inference(cnf_transformation,[],[f1])).
% 0.48/0.81  fof(f85,plain,(
% 0.48/0.81    ( ! [X21] : (~r2_hidden(sK4(sK0,sK1,k3_xboole_0(sK1,X21)),sK0) | k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,X21)) )),
% 0.48/0.81    inference(resolution,[],[f67,f33])).
% 0.48/0.81  fof(f67,plain,(
% 0.48/0.81    ( ! [X10,X9] : (r2_hidden(sK4(sK0,sK1,k3_xboole_0(X9,X10)),X9) | k3_xboole_0(sK0,sK1) = k3_xboole_0(X9,X10)) )),
% 0.48/0.81    inference(resolution,[],[f57,f32])).
% 0.48/0.81  fof(f32,plain,(
% 0.48/0.81    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.48/0.81    inference(equality_resolution,[],[f27])).
% 0.48/0.81  fof(f27,plain,(
% 0.48/0.81    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.48/0.81    inference(cnf_transformation,[],[f1])).
% 0.48/0.81  fof(f2553,plain,(
% 0.48/0.81    ( ! [X5] : (k3_xboole_0(sK0,sK1) = k3_xboole_0(X5,k3_xboole_0(sK1,sK0))) )),
% 0.48/0.81    inference(duplicate_literal_removal,[],[f2536])).
% 0.48/0.81  fof(f2536,plain,(
% 0.48/0.81    ( ! [X5] : (k3_xboole_0(sK0,sK1) = k3_xboole_0(X5,k3_xboole_0(sK1,sK0)) | k3_xboole_0(sK0,sK1) = k3_xboole_0(X5,k3_xboole_0(sK1,sK0))) )),
% 0.48/0.81    inference(resolution,[],[f1056,f102])).
% 0.48/0.81  fof(f102,plain,(
% 0.48/0.81    ( ! [X19,X20,X18] : (r2_hidden(sK4(sK0,sK1,k3_xboole_0(X18,k3_xboole_0(X19,X20))),X20) | k3_xboole_0(sK0,sK1) = k3_xboole_0(X18,k3_xboole_0(X19,X20))) )),
% 0.48/0.81    inference(resolution,[],[f68,f31])).
% 0.48/0.81  fof(f1056,plain,(
% 0.48/0.81    ( ! [X37,X38] : (~r2_hidden(sK4(sK0,sK1,k3_xboole_0(X37,k3_xboole_0(sK1,X38))),sK0) | k3_xboole_0(sK0,sK1) = k3_xboole_0(X37,k3_xboole_0(sK1,X38))) )),
% 0.48/0.81    inference(resolution,[],[f101,f33])).
% 0.48/0.81  fof(f101,plain,(
% 0.48/0.81    ( ! [X17,X15,X16] : (r2_hidden(sK4(sK0,sK1,k3_xboole_0(X15,k3_xboole_0(X16,X17))),X16) | k3_xboole_0(sK0,sK1) = k3_xboole_0(X15,k3_xboole_0(X16,X17))) )),
% 0.48/0.81    inference(resolution,[],[f68,f32])).
% 0.48/0.81  fof(f189,plain,(
% 0.48/0.81    ( ! [X3] : (k1_xboole_0 = k2_xboole_0(k3_xboole_0(k1_xboole_0,X3),k1_xboole_0)) )),
% 0.48/0.81    inference(superposition,[],[f19,f180])).
% 0.48/0.81  fof(f180,plain,(
% 0.48/0.81    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.48/0.81    inference(forward_demodulation,[],[f178,f17])).
% 0.48/0.81  fof(f178,plain,(
% 0.48/0.81    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))) )),
% 0.48/0.81    inference(superposition,[],[f23,f176])).
% 0.48/0.81  fof(f176,plain,(
% 0.48/0.81    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.48/0.81    inference(superposition,[],[f17,f172])).
% 0.48/0.81  fof(f172,plain,(
% 0.48/0.81    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1))),
% 0.48/0.81    inference(forward_demodulation,[],[f171,f16])).
% 0.48/0.81  fof(f171,plain,(
% 0.48/0.81    k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.48/0.81    inference(superposition,[],[f18,f165])).
% 0.48/0.81  fof(f165,plain,(
% 0.48/0.81    k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k1_xboole_0)),
% 0.48/0.81    inference(superposition,[],[f17,f161])).
% 0.48/0.81  fof(f161,plain,(
% 0.48/0.81    k1_xboole_0 = k2_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k1_xboole_0)),
% 0.48/0.81    inference(superposition,[],[f19,f153])).
% 0.48/0.81  fof(f153,plain,(
% 0.48/0.81    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 0.48/0.81    inference(forward_demodulation,[],[f147,f132])).
% 0.48/0.81  fof(f132,plain,(
% 0.48/0.81    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK1)),
% 0.48/0.81    inference(superposition,[],[f17,f120])).
% 0.48/0.81  fof(f120,plain,(
% 0.48/0.81    sK1 = k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 0.48/0.81    inference(superposition,[],[f19,f115])).
% 0.48/0.81  fof(f147,plain,(
% 0.48/0.81    k4_xboole_0(k3_xboole_0(sK0,sK1),sK1) = k4_xboole_0(k1_xboole_0,sK1)),
% 0.48/0.81    inference(superposition,[],[f136,f16])).
% 0.48/0.81  fof(f136,plain,(
% 0.48/0.81    ( ! [X0] : (k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK1,X0)) = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.48/0.81    inference(superposition,[],[f23,f132])).
% 0.48/0.81  fof(f19,plain,(
% 0.48/0.81    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.48/0.81    inference(cnf_transformation,[],[f7])).
% 0.48/0.81  fof(f7,axiom,(
% 0.48/0.81    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.48/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.48/0.81  fof(f825,plain,(
% 0.48/0.81    k3_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.48/0.81    inference(backward_demodulation,[],[f137,f824])).
% 0.48/0.81  fof(f824,plain,(
% 0.48/0.81    ( ! [X0] : (k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,X0),sK1)) )),
% 0.48/0.81    inference(duplicate_literal_removal,[],[f805])).
% 0.48/0.81  fof(f805,plain,(
% 0.48/0.81    ( ! [X0] : (k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,X0),sK1) | k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,X0),sK1)) )),
% 0.48/0.81    inference(resolution,[],[f83,f103])).
% 0.48/0.81  fof(f103,plain,(
% 0.48/0.81    ( ! [X21] : (~r2_hidden(sK4(sK0,sK1,k3_xboole_0(X21,sK1)),sK0) | k3_xboole_0(sK0,sK1) = k3_xboole_0(X21,sK1)) )),
% 0.48/0.81    inference(resolution,[],[f68,f33])).
% 0.48/0.81  fof(f83,plain,(
% 0.48/0.81    ( ! [X17,X15,X16] : (r2_hidden(sK4(sK0,sK1,k3_xboole_0(k3_xboole_0(X15,X16),X17)),X15) | k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(X15,X16),X17)) )),
% 0.48/0.81    inference(resolution,[],[f67,f32])).
% 0.48/0.81  fof(f137,plain,(
% 0.48/0.81    k3_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK1),sK1),k1_xboole_0)),
% 0.48/0.81    inference(superposition,[],[f19,f132])).
% 0.48/0.81  fof(f2642,plain,(
% 0.48/0.81    ( ! [X4] : (k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X4,k3_xboole_0(sK0,sK1))) = X4) )),
% 0.48/0.81    inference(superposition,[],[f19,f2557])).
% 0.48/0.81  fof(f3277,plain,(
% 0.48/0.81    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.48/0.81    inference(superposition,[],[f2866,f18])).
% 0.48/0.81  fof(f18,plain,(
% 0.48/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.48/0.81    inference(cnf_transformation,[],[f4])).
% 0.48/0.81  fof(f4,axiom,(
% 0.48/0.81    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.48/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.48/0.81  fof(f3808,plain,(
% 0.48/0.81    ( ! [X8,X7] : (k2_xboole_0(X7,k1_xboole_0) = k2_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 0.48/0.81    inference(superposition,[],[f18,f3776])).
% 0.48/0.81  fof(f3776,plain,(
% 0.48/0.81    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 0.48/0.81    inference(superposition,[],[f3668,f19])).
% 0.48/0.81  fof(f3668,plain,(
% 0.48/0.81    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 0.48/0.81    inference(forward_demodulation,[],[f3662,f18])).
% 0.48/0.81  fof(f3662,plain,(
% 0.48/0.81    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3)))) )),
% 0.48/0.81    inference(superposition,[],[f3645,f23])).
% 0.48/0.81  fof(f3992,plain,(
% 0.48/0.81    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X3,X2)) = X2) )),
% 0.48/0.81    inference(superposition,[],[f3782,f3670])).
% 0.48/0.81  fof(f3782,plain,(
% 0.48/0.81    ( ! [X4,X5] : (k2_xboole_0(k3_xboole_0(X4,k2_xboole_0(X5,X4)),k1_xboole_0) = X4) )),
% 0.48/0.82    inference(superposition,[],[f19,f3668])).
% 0.48/0.82  fof(f31,plain,(
% 0.48/0.82    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.48/0.82    inference(equality_resolution,[],[f28])).
% 0.48/0.82  fof(f28,plain,(
% 0.48/0.82    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.48/0.82    inference(cnf_transformation,[],[f1])).
% 0.48/0.82  % SZS output end Proof for theBenchmark
% 0.48/0.82  % (25690)------------------------------
% 0.48/0.82  % (25690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.48/0.82  % (25690)Termination reason: Refutation
% 0.48/0.82  
% 0.48/0.82  % (25690)Memory used [KB]: 3709
% 0.48/0.82  % (25690)Time elapsed: 0.224 s
% 0.48/0.82  % (25690)------------------------------
% 0.48/0.82  % (25690)------------------------------
% 0.48/0.82  % (25534)Success in time 0.456 s
%------------------------------------------------------------------------------
