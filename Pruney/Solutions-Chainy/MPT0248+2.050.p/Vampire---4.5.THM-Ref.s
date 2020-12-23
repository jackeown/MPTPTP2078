%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:56 EST 2020

% Result     : Theorem 2.30s
% Output     : Refutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  110 (1741 expanded)
%              Number of leaves         :   18 ( 509 expanded)
%              Depth                    :   26
%              Number of atoms          :  191 (5615 expanded)
%              Number of equality atoms :  162 (5107 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4257,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4256,f4236])).

fof(f4236,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f4063,f4234])).

fof(f4234,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f4231,f4061])).

fof(f4061,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f35,f4060])).

fof(f4060,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f65,f1158,f4059])).

fof(f4059,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f4012])).

fof(f4012,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f4011,f1158])).

fof(f4011,plain,
    ( sK2 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f4006,f1193])).

fof(f1193,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f1160])).

fof(f1160,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f36,f1158])).

fof(f36,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f4006,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | sK2 = k1_tarski(sK0) ),
    inference(resolution,[],[f3955,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f3955,plain,
    ( r1_tarski(sK2,k1_tarski(sK0))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f78,f3948])).

fof(f3948,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f3942,f1571])).

fof(f1571,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f1551,f67])).

fof(f67,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f43,f38])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1551,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f57,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f3942,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f3688,f1158])).

fof(f3688,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f3680,f1778])).

fof(f1778,plain,(
    ! [X32] : k3_xboole_0(sK1,X32) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,X32)) ),
    inference(forward_demodulation,[],[f1741,f38])).

fof(f1741,plain,(
    ! [X32] : k5_xboole_0(k3_xboole_0(sK1,X32),k1_xboole_0) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,X32)) ),
    inference(superposition,[],[f1578,f161])).

fof(f161,plain,(
    ! [X17] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,X17),k1_tarski(sK0)) ),
    inference(resolution,[],[f54,f78])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1578,plain,(
    ! [X8,X7] : k3_xboole_0(X8,X7) = k5_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f1571,f256])).

fof(f256,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f47,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f3680,plain,(
    k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f1577,f796])).

fof(f796,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f48,f33])).

fof(f33,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f1577,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f1571,f47])).

fof(f78,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),k1_tarski(sK0)) ),
    inference(superposition,[],[f55,f33])).

fof(f55,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f1158,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f50,f66])).

fof(f66,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f41,f33])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f65,plain,
    ( sK1 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(inner_rewriting,[],[f64])).

fof(f64,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f34])).

fof(f34,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f4231,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k1_tarski(sK0) ),
    inference(resolution,[],[f4182,f50])).

fof(f4182,plain,(
    r1_tarski(sK2,k1_tarski(sK0)) ),
    inference(superposition,[],[f663,f4149])).

fof(f4149,plain,(
    sK2 = k3_xboole_0(sK2,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f4136,f4148])).

fof(f4148,plain,(
    sK2 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_xboole_0,sK2)) ),
    inference(forward_demodulation,[],[f4116,f67])).

fof(f4116,plain,(
    k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f3944,f4060])).

fof(f3944,plain,(
    k5_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f1571,f3688])).

fof(f4136,plain,(
    k3_xboole_0(sK2,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_xboole_0,sK2)) ),
    inference(forward_demodulation,[],[f4094,f266])).

fof(f266,plain,(
    ! [X6] : k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f47,f67])).

fof(f4094,plain,(
    k3_xboole_0(sK2,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f1721,f4060])).

fof(f1721,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK2,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f1683,f42])).

fof(f1683,plain,(
    k3_xboole_0(k1_tarski(sK0),sK2) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f1577,f180])).

fof(f180,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),sK2) ),
    inference(superposition,[],[f46,f33])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f663,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(backward_demodulation,[],[f90,f661])).

fof(f661,plain,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    inference(forward_demodulation,[],[f643,f103])).

fof(f103,plain,(
    ! [X2] : k3_xboole_0(X2,k3_tarski(k1_tarski(X2))) = X2 ),
    inference(resolution,[],[f49,f92])).

fof(f92,plain,(
    ! [X4] : r1_tarski(X4,k3_tarski(k1_tarski(X4))) ),
    inference(superposition,[],[f41,f89])).

fof(f89,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f44,f39])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f643,plain,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = k3_xboole_0(X1,k3_tarski(k1_tarski(X1))) ),
    inference(superposition,[],[f299,f42])).

fof(f299,plain,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = k3_xboole_0(k3_tarski(k1_tarski(X1)),X1) ),
    inference(resolution,[],[f297,f49])).

fof(f297,plain,(
    ! [X0] : r1_tarski(k3_tarski(k1_tarski(X0)),X0) ),
    inference(trivial_inequality_removal,[],[f296])).

fof(f296,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k3_tarski(k1_tarski(X0)),X0) ) ),
    inference(superposition,[],[f53,f269])).

fof(f269,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k3_tarski(k1_tarski(X0)),X0) ),
    inference(backward_demodulation,[],[f181,f268])).

fof(f268,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f255,f37])).

fof(f255,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f47,f40])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f181,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k3_tarski(k1_tarski(X0)),X0) ),
    inference(superposition,[],[f46,f89])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),k3_tarski(k1_tarski(X0))) ),
    inference(superposition,[],[f76,f89])).

fof(f76,plain,(
    ! [X4,X2,X3] : r1_tarski(k3_xboole_0(X3,X2),k2_xboole_0(X2,X4)) ),
    inference(superposition,[],[f55,f42])).

fof(f4063,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(backward_demodulation,[],[f36,f4060])).

fof(f4256,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f4238,f662])).

fof(f662,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(backward_demodulation,[],[f89,f661])).

fof(f4238,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f4062,f4234])).

fof(f4062,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f33,f4060])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 09:29:45 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.50  % (14926)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (14918)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (14923)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (14922)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (14921)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (14920)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (14919)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (14941)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (14947)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (14946)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (14933)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (14924)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (14939)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (14938)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (14933)Refutation not found, incomplete strategy% (14933)------------------------------
% 0.22/0.54  % (14933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14933)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14933)Memory used [KB]: 6140
% 0.22/0.54  % (14933)Time elapsed: 0.004 s
% 0.22/0.54  % (14933)------------------------------
% 0.22/0.54  % (14933)------------------------------
% 0.22/0.54  % (14927)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (14931)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (14930)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (14943)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (14934)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (14945)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (14940)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (14937)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (14935)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (14936)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (14935)Refutation not found, incomplete strategy% (14935)------------------------------
% 0.22/0.56  % (14935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (14935)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (14935)Memory used [KB]: 10618
% 0.22/0.56  % (14935)Time elapsed: 0.130 s
% 0.22/0.56  % (14935)------------------------------
% 0.22/0.56  % (14935)------------------------------
% 0.22/0.56  % (14928)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (14929)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (14944)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (14929)Refutation not found, incomplete strategy% (14929)------------------------------
% 0.22/0.56  % (14929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (14929)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (14929)Memory used [KB]: 10618
% 0.22/0.56  % (14929)Time elapsed: 0.139 s
% 0.22/0.56  % (14929)------------------------------
% 0.22/0.56  % (14929)------------------------------
% 0.22/0.56  % (14928)Refutation not found, incomplete strategy% (14928)------------------------------
% 0.22/0.56  % (14928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (14932)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.57  % (14925)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.57  % (14942)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.58  % (14928)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (14928)Memory used [KB]: 10618
% 0.22/0.58  % (14928)Time elapsed: 0.142 s
% 0.22/0.58  % (14928)------------------------------
% 0.22/0.58  % (14928)------------------------------
% 2.05/0.67  % (14953)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.30/0.68  % (14962)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.30/0.69  % (14956)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.30/0.69  % (14960)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.30/0.72  % (14925)Refutation found. Thanks to Tanya!
% 2.30/0.72  % SZS status Theorem for theBenchmark
% 2.75/0.74  % SZS output start Proof for theBenchmark
% 2.75/0.74  fof(f4257,plain,(
% 2.75/0.74    $false),
% 2.75/0.74    inference(subsumption_resolution,[],[f4256,f4236])).
% 2.75/0.74  fof(f4236,plain,(
% 2.75/0.74    k1_xboole_0 != k1_tarski(sK0)),
% 2.75/0.74    inference(subsumption_resolution,[],[f4063,f4234])).
% 2.75/0.74  fof(f4234,plain,(
% 2.75/0.74    k1_xboole_0 = sK2),
% 2.75/0.74    inference(subsumption_resolution,[],[f4231,f4061])).
% 2.75/0.74  fof(f4061,plain,(
% 2.75/0.74    sK2 != k1_tarski(sK0)),
% 2.75/0.74    inference(subsumption_resolution,[],[f35,f4060])).
% 2.75/0.74  fof(f4060,plain,(
% 2.75/0.74    k1_xboole_0 = sK1),
% 2.75/0.74    inference(global_subsumption,[],[f65,f1158,f4059])).
% 2.75/0.74  fof(f4059,plain,(
% 2.75/0.74    sK1 = sK2 | k1_xboole_0 = sK1),
% 2.75/0.74    inference(duplicate_literal_removal,[],[f4012])).
% 2.75/0.74  fof(f4012,plain,(
% 2.75/0.74    sK1 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 2.75/0.74    inference(superposition,[],[f4011,f1158])).
% 2.75/0.74  fof(f4011,plain,(
% 2.75/0.74    sK2 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 2.75/0.74    inference(subsumption_resolution,[],[f4006,f1193])).
% 2.75/0.74  fof(f1193,plain,(
% 2.75/0.74    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.75/0.74    inference(trivial_inequality_removal,[],[f1160])).
% 2.75/0.74  fof(f1160,plain,(
% 2.75/0.74    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.75/0.74    inference(superposition,[],[f36,f1158])).
% 2.75/0.74  fof(f36,plain,(
% 2.75/0.74    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.75/0.74    inference(cnf_transformation,[],[f29])).
% 2.75/0.74  fof(f29,plain,(
% 2.75/0.74    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.75/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f28])).
% 2.75/0.74  fof(f28,plain,(
% 2.75/0.74    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.75/0.74    introduced(choice_axiom,[])).
% 2.75/0.74  fof(f26,plain,(
% 2.75/0.74    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.75/0.74    inference(ennf_transformation,[],[f24])).
% 2.75/0.74  fof(f24,negated_conjecture,(
% 2.75/0.74    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.75/0.74    inference(negated_conjecture,[],[f23])).
% 2.75/0.74  fof(f23,conjecture,(
% 2.75/0.74    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.75/0.74  fof(f4006,plain,(
% 2.75/0.74    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | sK2 = k1_tarski(sK0)),
% 2.75/0.74    inference(resolution,[],[f3955,f50])).
% 2.75/0.74  fof(f50,plain,(
% 2.75/0.74    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.75/0.74    inference(cnf_transformation,[],[f31])).
% 2.75/0.74  fof(f31,plain,(
% 2.75/0.74    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.75/0.74    inference(flattening,[],[f30])).
% 2.75/0.74  fof(f30,plain,(
% 2.75/0.74    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.75/0.74    inference(nnf_transformation,[],[f21])).
% 2.75/0.74  fof(f21,axiom,(
% 2.75/0.74    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.75/0.74  fof(f3955,plain,(
% 2.75/0.74    r1_tarski(sK2,k1_tarski(sK0)) | k1_xboole_0 = sK1),
% 2.75/0.74    inference(superposition,[],[f78,f3948])).
% 2.75/0.74  fof(f3948,plain,(
% 2.75/0.74    sK2 = k3_xboole_0(sK1,sK2) | k1_xboole_0 = sK1),
% 2.75/0.74    inference(forward_demodulation,[],[f3942,f1571])).
% 2.75/0.74  fof(f1571,plain,(
% 2.75/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.75/0.74    inference(forward_demodulation,[],[f1551,f67])).
% 2.75/0.74  fof(f67,plain,(
% 2.75/0.74    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.75/0.74    inference(superposition,[],[f43,f38])).
% 2.75/0.74  fof(f38,plain,(
% 2.75/0.74    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.75/0.74    inference(cnf_transformation,[],[f10])).
% 2.75/0.74  fof(f10,axiom,(
% 2.75/0.74    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.75/0.74  fof(f43,plain,(
% 2.75/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f2])).
% 2.75/0.74  fof(f2,axiom,(
% 2.75/0.74    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.75/0.74  fof(f1551,plain,(
% 2.75/0.74    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.75/0.74    inference(superposition,[],[f57,f37])).
% 2.75/0.74  fof(f37,plain,(
% 2.75/0.74    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f13])).
% 2.75/0.74  fof(f13,axiom,(
% 2.75/0.74    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.75/0.74  fof(f57,plain,(
% 2.75/0.74    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.75/0.74    inference(cnf_transformation,[],[f12])).
% 2.75/0.74  fof(f12,axiom,(
% 2.75/0.74    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.75/0.74  fof(f3942,plain,(
% 2.75/0.74    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | k1_xboole_0 = sK1),
% 2.75/0.74    inference(superposition,[],[f3688,f1158])).
% 2.75/0.74  fof(f3688,plain,(
% 2.75/0.74    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2))),
% 2.75/0.74    inference(forward_demodulation,[],[f3680,f1778])).
% 2.75/0.74  fof(f1778,plain,(
% 2.75/0.74    ( ! [X32] : (k3_xboole_0(sK1,X32) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,X32))) )),
% 2.75/0.74    inference(forward_demodulation,[],[f1741,f38])).
% 2.75/0.74  fof(f1741,plain,(
% 2.75/0.74    ( ! [X32] : (k5_xboole_0(k3_xboole_0(sK1,X32),k1_xboole_0) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,X32))) )),
% 2.75/0.74    inference(superposition,[],[f1578,f161])).
% 2.75/0.74  fof(f161,plain,(
% 2.75/0.74    ( ! [X17] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,X17),k1_tarski(sK0))) )),
% 2.75/0.74    inference(resolution,[],[f54,f78])).
% 2.75/0.74  fof(f54,plain,(
% 2.75/0.74    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.75/0.74    inference(cnf_transformation,[],[f32])).
% 2.75/0.74  fof(f32,plain,(
% 2.75/0.74    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.75/0.74    inference(nnf_transformation,[],[f4])).
% 2.75/0.74  fof(f4,axiom,(
% 2.75/0.74    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.75/0.74  fof(f1578,plain,(
% 2.75/0.74    ( ! [X8,X7] : (k3_xboole_0(X8,X7) = k5_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 2.75/0.74    inference(superposition,[],[f1571,f256])).
% 2.75/0.74  fof(f256,plain,(
% 2.75/0.74    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 2.75/0.74    inference(superposition,[],[f47,f42])).
% 2.75/0.74  fof(f42,plain,(
% 2.75/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f1])).
% 2.75/0.74  fof(f1,axiom,(
% 2.75/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.75/0.74  fof(f47,plain,(
% 2.75/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.75/0.74    inference(cnf_transformation,[],[f6])).
% 2.75/0.74  fof(f6,axiom,(
% 2.75/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.75/0.74  fof(f3680,plain,(
% 2.75/0.74    k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2))),
% 2.75/0.74    inference(superposition,[],[f1577,f796])).
% 2.75/0.74  fof(f796,plain,(
% 2.75/0.74    k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))),
% 2.75/0.74    inference(superposition,[],[f48,f33])).
% 2.75/0.74  fof(f33,plain,(
% 2.75/0.74    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.75/0.74    inference(cnf_transformation,[],[f29])).
% 2.75/0.74  fof(f48,plain,(
% 2.75/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.75/0.74    inference(cnf_transformation,[],[f5])).
% 2.75/0.74  fof(f5,axiom,(
% 2.75/0.74    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.75/0.74  fof(f1577,plain,(
% 2.75/0.74    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 2.75/0.74    inference(superposition,[],[f1571,f47])).
% 2.75/0.74  fof(f78,plain,(
% 2.75/0.74    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),k1_tarski(sK0))) )),
% 2.75/0.74    inference(superposition,[],[f55,f33])).
% 2.75/0.74  fof(f55,plain,(
% 2.75/0.74    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 2.75/0.74    inference(cnf_transformation,[],[f8])).
% 2.75/0.74  fof(f8,axiom,(
% 2.75/0.74    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
% 2.75/0.74  fof(f1158,plain,(
% 2.75/0.74    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 2.75/0.74    inference(resolution,[],[f50,f66])).
% 2.75/0.74  fof(f66,plain,(
% 2.75/0.74    r1_tarski(sK1,k1_tarski(sK0))),
% 2.75/0.74    inference(superposition,[],[f41,f33])).
% 2.75/0.74  fof(f41,plain,(
% 2.75/0.74    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.75/0.74    inference(cnf_transformation,[],[f11])).
% 2.75/0.74  fof(f11,axiom,(
% 2.75/0.74    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.75/0.74  fof(f65,plain,(
% 2.75/0.74    sK1 != sK2 | sK1 != k1_tarski(sK0)),
% 2.75/0.74    inference(inner_rewriting,[],[f64])).
% 2.75/0.74  fof(f64,plain,(
% 2.75/0.74    sK2 != k1_tarski(sK0) | sK1 != sK2),
% 2.75/0.74    inference(inner_rewriting,[],[f34])).
% 2.75/0.74  fof(f34,plain,(
% 2.75/0.74    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.75/0.74    inference(cnf_transformation,[],[f29])).
% 2.75/0.74  fof(f35,plain,(
% 2.75/0.74    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.75/0.74    inference(cnf_transformation,[],[f29])).
% 2.75/0.74  fof(f4231,plain,(
% 2.75/0.74    k1_xboole_0 = sK2 | sK2 = k1_tarski(sK0)),
% 2.75/0.74    inference(resolution,[],[f4182,f50])).
% 2.75/0.74  fof(f4182,plain,(
% 2.75/0.74    r1_tarski(sK2,k1_tarski(sK0))),
% 2.75/0.74    inference(superposition,[],[f663,f4149])).
% 2.75/0.74  fof(f4149,plain,(
% 2.75/0.74    sK2 = k3_xboole_0(sK2,k1_tarski(sK0))),
% 2.75/0.74    inference(backward_demodulation,[],[f4136,f4148])).
% 2.75/0.74  fof(f4148,plain,(
% 2.75/0.74    sK2 = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_xboole_0,sK2))),
% 2.75/0.74    inference(forward_demodulation,[],[f4116,f67])).
% 2.75/0.74  fof(f4116,plain,(
% 2.75/0.74    k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_xboole_0,sK2))),
% 2.75/0.74    inference(backward_demodulation,[],[f3944,f4060])).
% 2.75/0.74  fof(f3944,plain,(
% 2.75/0.74    k5_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))),
% 2.75/0.74    inference(superposition,[],[f1571,f3688])).
% 2.75/0.74  fof(f4136,plain,(
% 2.75/0.74    k3_xboole_0(sK2,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_xboole_0,sK2))),
% 2.75/0.74    inference(forward_demodulation,[],[f4094,f266])).
% 2.75/0.74  fof(f266,plain,(
% 2.75/0.74    ( ! [X6] : (k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6)) )),
% 2.75/0.74    inference(superposition,[],[f47,f67])).
% 2.75/0.74  fof(f4094,plain,(
% 2.75/0.74    k3_xboole_0(sK2,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_xboole_0,sK2))),
% 2.75/0.74    inference(backward_demodulation,[],[f1721,f4060])).
% 2.75/0.74  fof(f1721,plain,(
% 2.75/0.74    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK2,k1_tarski(sK0))),
% 2.75/0.74    inference(forward_demodulation,[],[f1683,f42])).
% 2.75/0.74  fof(f1683,plain,(
% 2.75/0.74    k3_xboole_0(k1_tarski(sK0),sK2) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,sK2))),
% 2.75/0.74    inference(superposition,[],[f1577,f180])).
% 2.75/0.74  fof(f180,plain,(
% 2.75/0.74    k4_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),sK2)),
% 2.75/0.74    inference(superposition,[],[f46,f33])).
% 2.75/0.74  fof(f46,plain,(
% 2.75/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f9])).
% 2.75/0.74  fof(f9,axiom,(
% 2.75/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.75/0.74  fof(f663,plain,(
% 2.75/0.74    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 2.75/0.74    inference(backward_demodulation,[],[f90,f661])).
% 2.75/0.74  fof(f661,plain,(
% 2.75/0.74    ( ! [X1] : (k3_tarski(k1_tarski(X1)) = X1) )),
% 2.75/0.74    inference(forward_demodulation,[],[f643,f103])).
% 2.75/0.74  fof(f103,plain,(
% 2.75/0.74    ( ! [X2] : (k3_xboole_0(X2,k3_tarski(k1_tarski(X2))) = X2) )),
% 2.75/0.74    inference(resolution,[],[f49,f92])).
% 2.75/0.74  fof(f92,plain,(
% 2.75/0.74    ( ! [X4] : (r1_tarski(X4,k3_tarski(k1_tarski(X4)))) )),
% 2.75/0.74    inference(superposition,[],[f41,f89])).
% 2.75/0.74  fof(f89,plain,(
% 2.75/0.74    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 2.75/0.74    inference(superposition,[],[f44,f39])).
% 2.75/0.74  fof(f39,plain,(
% 2.75/0.74    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f14])).
% 2.75/0.74  fof(f14,axiom,(
% 2.75/0.74    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.75/0.74  fof(f44,plain,(
% 2.75/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.75/0.74    inference(cnf_transformation,[],[f22])).
% 2.75/0.74  fof(f22,axiom,(
% 2.75/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.75/0.74  fof(f49,plain,(
% 2.75/0.74    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.75/0.74    inference(cnf_transformation,[],[f27])).
% 2.75/0.74  fof(f27,plain,(
% 2.75/0.74    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.75/0.74    inference(ennf_transformation,[],[f7])).
% 2.75/0.74  fof(f7,axiom,(
% 2.75/0.74    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.75/0.74  fof(f643,plain,(
% 2.75/0.74    ( ! [X1] : (k3_tarski(k1_tarski(X1)) = k3_xboole_0(X1,k3_tarski(k1_tarski(X1)))) )),
% 2.75/0.74    inference(superposition,[],[f299,f42])).
% 2.75/0.74  fof(f299,plain,(
% 2.75/0.74    ( ! [X1] : (k3_tarski(k1_tarski(X1)) = k3_xboole_0(k3_tarski(k1_tarski(X1)),X1)) )),
% 2.75/0.74    inference(resolution,[],[f297,f49])).
% 2.75/0.74  fof(f297,plain,(
% 2.75/0.74    ( ! [X0] : (r1_tarski(k3_tarski(k1_tarski(X0)),X0)) )),
% 2.75/0.74    inference(trivial_inequality_removal,[],[f296])).
% 2.75/0.74  fof(f296,plain,(
% 2.75/0.74    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k3_tarski(k1_tarski(X0)),X0)) )),
% 2.75/0.74    inference(superposition,[],[f53,f269])).
% 2.75/0.74  fof(f269,plain,(
% 2.75/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k3_tarski(k1_tarski(X0)),X0)) )),
% 2.75/0.74    inference(backward_demodulation,[],[f181,f268])).
% 2.75/0.74  fof(f268,plain,(
% 2.75/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.75/0.74    inference(forward_demodulation,[],[f255,f37])).
% 2.75/0.74  fof(f255,plain,(
% 2.75/0.74    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 2.75/0.74    inference(superposition,[],[f47,f40])).
% 2.75/0.74  fof(f40,plain,(
% 2.75/0.74    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.75/0.74    inference(cnf_transformation,[],[f25])).
% 2.75/0.74  fof(f25,plain,(
% 2.75/0.74    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.75/0.74    inference(rectify,[],[f3])).
% 2.75/0.74  fof(f3,axiom,(
% 2.75/0.74    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.75/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.75/0.74  fof(f181,plain,(
% 2.75/0.74    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k3_tarski(k1_tarski(X0)),X0)) )),
% 2.75/0.74    inference(superposition,[],[f46,f89])).
% 2.75/0.74  fof(f53,plain,(
% 2.75/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.75/0.74    inference(cnf_transformation,[],[f32])).
% 2.75/0.74  fof(f90,plain,(
% 2.75/0.74    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),k3_tarski(k1_tarski(X0)))) )),
% 2.75/0.74    inference(superposition,[],[f76,f89])).
% 2.75/0.74  fof(f76,plain,(
% 2.75/0.74    ( ! [X4,X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),k2_xboole_0(X2,X4))) )),
% 2.75/0.74    inference(superposition,[],[f55,f42])).
% 2.75/0.74  fof(f4063,plain,(
% 2.75/0.74    k1_xboole_0 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.75/0.74    inference(backward_demodulation,[],[f36,f4060])).
% 2.75/0.74  fof(f4256,plain,(
% 2.75/0.74    k1_xboole_0 = k1_tarski(sK0)),
% 2.75/0.74    inference(forward_demodulation,[],[f4238,f662])).
% 2.75/0.74  fof(f662,plain,(
% 2.75/0.74    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.75/0.74    inference(backward_demodulation,[],[f89,f661])).
% 2.75/0.74  fof(f4238,plain,(
% 2.75/0.74    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.75/0.74    inference(backward_demodulation,[],[f4062,f4234])).
% 2.75/0.74  fof(f4062,plain,(
% 2.75/0.74    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 2.75/0.74    inference(backward_demodulation,[],[f33,f4060])).
% 2.75/0.74  % SZS output end Proof for theBenchmark
% 2.75/0.74  % (14925)------------------------------
% 2.75/0.74  % (14925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.75/0.74  % (14925)Termination reason: Refutation
% 2.75/0.74  
% 2.75/0.74  % (14925)Memory used [KB]: 8443
% 2.75/0.74  % (14925)Time elapsed: 0.296 s
% 2.75/0.74  % (14925)------------------------------
% 2.75/0.74  % (14925)------------------------------
% 2.75/0.75  % (14917)Success in time 0.368 s
%------------------------------------------------------------------------------
