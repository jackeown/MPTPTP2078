%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:31 EST 2020

% Result     : Theorem 2.61s
% Output     : Refutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  101 (3588 expanded)
%              Number of leaves         :    9 ( 907 expanded)
%              Depth                    :   42
%              Number of atoms          :  160 (8187 expanded)
%              Number of equality atoms :   92 (6420 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2694,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2693,f2549])).

fof(f2549,plain,(
    sK1 != sK3 ),
    inference(trivial_inequality_removal,[],[f2415])).

fof(f2415,plain,
    ( sK0 != sK0
    | sK1 != sK3 ),
    inference(backward_demodulation,[],[f29,f2414])).

fof(f2414,plain,(
    sK0 = sK2 ),
    inference(backward_demodulation,[],[f1462,f2413])).

fof(f2413,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f2409,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f2409,plain,(
    r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f2353,f84])).

fof(f84,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f45,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2353,plain,(
    ! [X6] :
      ( ~ r1_tarski(k2_zfmisc_1(X6,sK1),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(X6,sK2) ) ),
    inference(subsumption_resolution,[],[f2336,f32])).

fof(f32,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f2336,plain,(
    ! [X6] :
      ( ~ r1_tarski(k2_zfmisc_1(X6,sK1),k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 = sK1
      | r1_tarski(X6,sK2) ) ),
    inference(superposition,[],[f64,f2268])).

fof(f2268,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f2228,f35])).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f2228,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK1)) = k2_zfmisc_1(sK2,sK1) ),
    inference(superposition,[],[f1495,f1348])).

fof(f1348,plain,(
    sK1 = k3_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f1344,f42])).

fof(f1344,plain,(
    r1_tarski(sK1,sK3) ),
    inference(subsumption_resolution,[],[f1328,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f1328,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(sK1,sK3) ),
    inference(resolution,[],[f65,f890])).

fof(f890,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    inference(superposition,[],[f542,f872])).

fof(f872,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) ),
    inference(backward_demodulation,[],[f604,f871])).

fof(f871,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(backward_demodulation,[],[f719,f870])).

fof(f870,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(resolution,[],[f863,f42])).

fof(f863,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f842,f35])).

fof(f842,plain,(
    ! [X6] : r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(X6,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f841,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f841,plain,(
    ! [X6] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X6),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f840,f30])).

fof(f30,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f840,plain,(
    ! [X6] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X6),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f831,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f831,plain,(
    ! [X6] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X6,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f583,f604])).

fof(f583,plain,(
    ! [X45,X46,X44] : r1_tarski(k2_zfmisc_1(X44,k3_xboole_0(X45,X46)),k2_zfmisc_1(X44,X46)) ),
    inference(superposition,[],[f527,f49])).

fof(f527,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f509])).

fof(f509,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f92,f45])).

fof(f92,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK6(k3_xboole_0(X6,X7),X8),X7)
      | r1_tarski(k3_xboole_0(X6,X7),X8) ) ),
    inference(resolution,[],[f68,f44])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f719,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f718,f604])).

fof(f718,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f717,f381])).

fof(f381,plain,(
    ! [X1] : k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3) = k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) ),
    inference(superposition,[],[f315,f276])).

fof(f276,plain,(
    ! [X0] : k2_zfmisc_1(k3_xboole_0(X0,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f48,f30])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f315,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3) ),
    inference(superposition,[],[f274,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f274,plain,(
    ! [X0] : k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) ),
    inference(superposition,[],[f48,f30])).

fof(f717,plain,(
    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f696,f635])).

fof(f635,plain,(
    ! [X3] : k2_zfmisc_1(k3_xboole_0(sK2,X3),sK3) = k2_zfmisc_1(k3_xboole_0(sK2,k3_xboole_0(X3,sK2)),sK3) ),
    inference(backward_demodulation,[],[f404,f627])).

fof(f627,plain,(
    ! [X2] : k2_zfmisc_1(k3_xboole_0(sK2,X2),sK3) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK2,X2),sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f540,f42])).

fof(f540,plain,(
    ! [X10] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,X10),sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f527,f315])).

fof(f404,plain,(
    ! [X3] : k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK2,X3),sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK2,k3_xboole_0(X3,sK2)),sK3) ),
    inference(superposition,[],[f315,f381])).

fof(f696,plain,(
    k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k3_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3) ),
    inference(superposition,[],[f274,f604])).

fof(f604,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f603,f36])).

fof(f603,plain,(
    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f559,f36])).

fof(f559,plain,(
    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f49,f315])).

fof(f542,plain,(
    ! [X12] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X12,sK2),sK3),k2_zfmisc_1(X12,sK3)) ),
    inference(superposition,[],[f527,f366])).

fof(f366,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3)) = k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) ),
    inference(superposition,[],[f276,f36])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f1495,plain,(
    ! [X12] : k2_zfmisc_1(sK2,k3_xboole_0(X12,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(X12,sK1)) ),
    inference(backward_demodulation,[],[f557,f1488])).

fof(f1488,plain,(
    ! [X1] : k2_zfmisc_1(sK0,k3_xboole_0(X1,sK1)) = k3_xboole_0(k2_zfmisc_1(sK2,X1),k2_zfmisc_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f876,f1462])).

fof(f876,plain,(
    ! [X1] : k2_zfmisc_1(sK0,k3_xboole_0(X1,sK1)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X1),k2_zfmisc_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f722,f871])).

fof(f722,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(sK0,k3_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f721,f49])).

fof(f721,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f720,f30])).

fof(f720,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f697,f66])).

fof(f697,plain,(
    ! [X1] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X1,sK3)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f49,f604])).

fof(f557,plain,(
    ! [X12] : k2_zfmisc_1(sK2,k3_xboole_0(X12,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X12),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f49,f30])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1462,plain,(
    sK2 = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f1461,f36])).

fof(f1461,plain,(
    sK2 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f1459,f42])).

fof(f1459,plain,(
    r1_tarski(sK2,sK0) ),
    inference(subsumption_resolution,[],[f1456,f32])).

fof(f1456,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f1411,f64])).

fof(f1411,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f833,f1348])).

fof(f833,plain,(
    ! [X9] : r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(X9,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f583,f30])).

fof(f29,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f2693,plain,(
    sK1 = sK3 ),
    inference(forward_demodulation,[],[f2692,f1429])).

fof(f1429,plain,(
    sK1 = k3_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f753,f1348])).

fof(f753,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f533,f36])).

fof(f533,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(k3_xboole_0(X4,X5),X5) ),
    inference(resolution,[],[f527,f42])).

fof(f2692,plain,(
    sK3 = k3_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f2668,f42])).

fof(f2668,plain,(
    r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f2580,f84])).

fof(f2580,plain,(
    ! [X10] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X10))
      | r1_tarski(sK3,X10) ) ),
    inference(subsumption_resolution,[],[f2579,f31])).

fof(f2579,plain,(
    ! [X10] :
      ( k1_xboole_0 = sK0
      | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X10))
      | r1_tarski(sK3,X10) ) ),
    inference(forward_demodulation,[],[f2427,f2414])).

fof(f2427,plain,(
    ! [X10] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X10))
      | k1_xboole_0 = sK2
      | r1_tarski(sK3,X10) ) ),
    inference(backward_demodulation,[],[f1336,f2414])).

fof(f1336,plain,(
    ! [X10] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X10))
      | k1_xboole_0 = sK2
      | r1_tarski(sK3,X10) ) ),
    inference(superposition,[],[f65,f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:09:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (20104)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (20120)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (20102)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (20110)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (20110)Refutation not found, incomplete strategy% (20110)------------------------------
% 0.22/0.55  % (20110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20110)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20110)Memory used [KB]: 10618
% 0.22/0.55  % (20110)Time elapsed: 0.117 s
% 0.22/0.55  % (20110)------------------------------
% 0.22/0.55  % (20110)------------------------------
% 0.22/0.55  % (20106)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (20122)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (20093)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (20121)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (20098)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (20095)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (20112)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (20119)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (20097)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (20118)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (20107)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (20109)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (20111)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (20113)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (20096)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (20099)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (20101)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (20108)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.57  % (20115)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.57  % (20105)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (20117)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (20094)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.57  % (20103)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.55/0.57  % (20116)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.55/0.57  % (20100)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.55/0.58  % (20114)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.06/0.67  % (20146)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.61/0.73  % (20099)Refutation found. Thanks to Tanya!
% 2.61/0.73  % SZS status Theorem for theBenchmark
% 2.61/0.73  % SZS output start Proof for theBenchmark
% 2.61/0.73  fof(f2694,plain,(
% 2.61/0.73    $false),
% 2.61/0.73    inference(subsumption_resolution,[],[f2693,f2549])).
% 2.61/0.73  fof(f2549,plain,(
% 2.61/0.73    sK1 != sK3),
% 2.61/0.73    inference(trivial_inequality_removal,[],[f2415])).
% 2.61/0.73  fof(f2415,plain,(
% 2.61/0.73    sK0 != sK0 | sK1 != sK3),
% 2.61/0.73    inference(backward_demodulation,[],[f29,f2414])).
% 2.61/0.73  fof(f2414,plain,(
% 2.61/0.73    sK0 = sK2),
% 2.61/0.73    inference(backward_demodulation,[],[f1462,f2413])).
% 2.61/0.73  fof(f2413,plain,(
% 2.61/0.73    sK0 = k3_xboole_0(sK0,sK2)),
% 2.61/0.73    inference(resolution,[],[f2409,f42])).
% 2.61/0.73  fof(f42,plain,(
% 2.61/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.61/0.73    inference(cnf_transformation,[],[f26])).
% 2.61/0.73  fof(f26,plain,(
% 2.61/0.73    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.61/0.73    inference(ennf_transformation,[],[f9])).
% 2.61/0.73  fof(f9,axiom,(
% 2.61/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.61/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.61/0.73  fof(f2409,plain,(
% 2.61/0.73    r1_tarski(sK0,sK2)),
% 2.61/0.73    inference(resolution,[],[f2353,f84])).
% 2.61/0.73  fof(f84,plain,(
% 2.61/0.73    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.61/0.73    inference(duplicate_literal_removal,[],[f83])).
% 2.61/0.73  fof(f83,plain,(
% 2.61/0.73    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 2.61/0.73    inference(resolution,[],[f45,f44])).
% 2.61/0.73  fof(f44,plain,(
% 2.61/0.73    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.61/0.73    inference(cnf_transformation,[],[f27])).
% 2.61/0.73  fof(f27,plain,(
% 2.61/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.61/0.73    inference(ennf_transformation,[],[f3])).
% 2.61/0.73  fof(f3,axiom,(
% 2.61/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.61/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.61/0.73  fof(f45,plain,(
% 2.61/0.73    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.61/0.73    inference(cnf_transformation,[],[f27])).
% 2.61/0.73  fof(f2353,plain,(
% 2.61/0.73    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(X6,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(X6,sK2)) )),
% 2.61/0.73    inference(subsumption_resolution,[],[f2336,f32])).
% 2.61/0.73  fof(f32,plain,(
% 2.61/0.73    k1_xboole_0 != sK1),
% 2.61/0.73    inference(cnf_transformation,[],[f22])).
% 2.61/0.73  fof(f22,plain,(
% 2.61/0.73    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 2.61/0.73    inference(flattening,[],[f21])).
% 2.61/0.73  fof(f21,plain,(
% 2.61/0.73    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 2.61/0.73    inference(ennf_transformation,[],[f17])).
% 2.61/0.73  fof(f17,negated_conjecture,(
% 2.61/0.73    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.61/0.73    inference(negated_conjecture,[],[f16])).
% 2.61/0.73  fof(f16,conjecture,(
% 2.61/0.73    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.61/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 2.61/0.73  fof(f2336,plain,(
% 2.61/0.73    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(X6,sK1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK1 | r1_tarski(X6,sK2)) )),
% 2.61/0.73    inference(superposition,[],[f64,f2268])).
% 2.61/0.73  fof(f2268,plain,(
% 2.61/0.73    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)),
% 2.61/0.73    inference(forward_demodulation,[],[f2228,f35])).
% 2.61/0.73  fof(f35,plain,(
% 2.61/0.73    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.61/0.73    inference(cnf_transformation,[],[f18])).
% 2.61/0.73  fof(f18,plain,(
% 2.61/0.73    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.61/0.73    inference(rectify,[],[f6])).
% 2.61/0.73  fof(f6,axiom,(
% 2.61/0.73    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.61/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.61/0.73  fof(f2228,plain,(
% 2.61/0.73    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK1)) = k2_zfmisc_1(sK2,sK1)),
% 2.61/0.73    inference(superposition,[],[f1495,f1348])).
% 2.61/0.73  fof(f1348,plain,(
% 2.61/0.73    sK1 = k3_xboole_0(sK1,sK3)),
% 2.61/0.73    inference(resolution,[],[f1344,f42])).
% 2.61/0.73  fof(f1344,plain,(
% 2.61/0.73    r1_tarski(sK1,sK3)),
% 2.61/0.73    inference(subsumption_resolution,[],[f1328,f31])).
% 2.61/0.73  fof(f31,plain,(
% 2.61/0.73    k1_xboole_0 != sK0),
% 2.61/0.73    inference(cnf_transformation,[],[f22])).
% 2.61/0.73  fof(f1328,plain,(
% 2.61/0.73    k1_xboole_0 = sK0 | r1_tarski(sK1,sK3)),
% 2.61/0.73    inference(resolution,[],[f65,f890])).
% 2.61/0.73  fof(f890,plain,(
% 2.61/0.73    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 2.61/0.73    inference(superposition,[],[f542,f872])).
% 2.61/0.73  fof(f872,plain,(
% 2.61/0.73    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)),
% 2.61/0.73    inference(backward_demodulation,[],[f604,f871])).
% 2.61/0.73  fof(f871,plain,(
% 2.61/0.73    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 2.61/0.73    inference(backward_demodulation,[],[f719,f870])).
% 2.61/0.73  fof(f870,plain,(
% 2.61/0.73    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 2.61/0.73    inference(resolution,[],[f863,f42])).
% 2.61/0.73  fof(f863,plain,(
% 2.61/0.73    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 2.61/0.73    inference(superposition,[],[f842,f35])).
% 2.61/0.73  fof(f842,plain,(
% 2.61/0.73    ( ! [X6] : (r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(X6,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 2.61/0.73    inference(forward_demodulation,[],[f841,f49])).
% 2.61/0.73  fof(f49,plain,(
% 2.61/0.73    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 2.61/0.73    inference(cnf_transformation,[],[f14])).
% 2.61/0.73  fof(f14,axiom,(
% 2.61/0.73    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.61/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 2.61/0.73  fof(f841,plain,(
% 2.61/0.73    ( ! [X6] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X6),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 2.61/0.73    inference(forward_demodulation,[],[f840,f30])).
% 2.61/0.73  fof(f30,plain,(
% 2.61/0.73    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 2.61/0.73    inference(cnf_transformation,[],[f22])).
% 2.61/0.73  fof(f840,plain,(
% 2.61/0.73    ( ! [X6] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,X6),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 2.61/0.73    inference(forward_demodulation,[],[f831,f66])).
% 2.61/0.73  fof(f66,plain,(
% 2.61/0.73    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.61/0.73    inference(cnf_transformation,[],[f15])).
% 2.61/0.73  fof(f15,axiom,(
% 2.61/0.73    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 2.61/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 2.61/0.73  fof(f831,plain,(
% 2.61/0.73    ( ! [X6] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X6,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 2.61/0.73    inference(superposition,[],[f583,f604])).
% 2.61/0.73  fof(f583,plain,(
% 2.61/0.73    ( ! [X45,X46,X44] : (r1_tarski(k2_zfmisc_1(X44,k3_xboole_0(X45,X46)),k2_zfmisc_1(X44,X46))) )),
% 2.61/0.73    inference(superposition,[],[f527,f49])).
% 2.61/0.73  fof(f527,plain,(
% 2.61/0.73    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 2.61/0.73    inference(duplicate_literal_removal,[],[f509])).
% 2.61/0.73  fof(f509,plain,(
% 2.61/0.73    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 2.61/0.73    inference(resolution,[],[f92,f45])).
% 2.61/0.73  fof(f92,plain,(
% 2.61/0.73    ( ! [X6,X8,X7] : (r2_hidden(sK6(k3_xboole_0(X6,X7),X8),X7) | r1_tarski(k3_xboole_0(X6,X7),X8)) )),
% 2.61/0.73    inference(resolution,[],[f68,f44])).
% 2.61/0.73  fof(f68,plain,(
% 2.61/0.73    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X1)) )),
% 2.61/0.73    inference(equality_resolution,[],[f54])).
% 2.61/0.73  fof(f54,plain,(
% 2.61/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.61/0.73    inference(cnf_transformation,[],[f4])).
% 2.61/0.73  fof(f4,axiom,(
% 2.61/0.73    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.61/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.61/0.73  fof(f719,plain,(
% 2.61/0.73    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 2.61/0.73    inference(forward_demodulation,[],[f718,f604])).
% 2.61/0.73  fof(f718,plain,(
% 2.61/0.73    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 2.61/0.73    inference(forward_demodulation,[],[f717,f381])).
% 2.61/0.73  fof(f381,plain,(
% 2.61/0.73    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3) = k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3)) )),
% 2.61/0.73    inference(superposition,[],[f315,f276])).
% 2.61/0.73  fof(f276,plain,(
% 2.61/0.73    ( ! [X0] : (k2_zfmisc_1(k3_xboole_0(X0,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 2.61/0.73    inference(superposition,[],[f48,f30])).
% 2.61/0.73  fof(f48,plain,(
% 2.61/0.73    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.61/0.73    inference(cnf_transformation,[],[f14])).
% 2.61/0.73  fof(f315,plain,(
% 2.61/0.73    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3)) )),
% 2.61/0.73    inference(superposition,[],[f274,f36])).
% 2.61/0.73  fof(f36,plain,(
% 2.61/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.61/0.73    inference(cnf_transformation,[],[f1])).
% 2.61/0.74  fof(f1,axiom,(
% 2.61/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.61/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.61/0.74  fof(f274,plain,(
% 2.61/0.74    ( ! [X0] : (k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))) )),
% 2.61/0.74    inference(superposition,[],[f48,f30])).
% 2.61/0.74  fof(f717,plain,(
% 2.61/0.74    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 2.61/0.74    inference(forward_demodulation,[],[f696,f635])).
% 2.61/0.74  fof(f635,plain,(
% 2.61/0.74    ( ! [X3] : (k2_zfmisc_1(k3_xboole_0(sK2,X3),sK3) = k2_zfmisc_1(k3_xboole_0(sK2,k3_xboole_0(X3,sK2)),sK3)) )),
% 2.61/0.74    inference(backward_demodulation,[],[f404,f627])).
% 2.61/0.74  fof(f627,plain,(
% 2.61/0.74    ( ! [X2] : (k2_zfmisc_1(k3_xboole_0(sK2,X2),sK3) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK2,X2),sK3),k2_zfmisc_1(sK0,sK1))) )),
% 2.61/0.74    inference(resolution,[],[f540,f42])).
% 2.61/0.74  fof(f540,plain,(
% 2.61/0.74    ( ! [X10] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,X10),sK3),k2_zfmisc_1(sK0,sK1))) )),
% 2.61/0.74    inference(superposition,[],[f527,f315])).
% 2.61/0.74  fof(f404,plain,(
% 2.61/0.74    ( ! [X3] : (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK2,X3),sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK2,k3_xboole_0(X3,sK2)),sK3)) )),
% 2.61/0.74    inference(superposition,[],[f315,f381])).
% 2.61/0.74  fof(f696,plain,(
% 2.61/0.74    k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k3_xboole_0(sK2,k3_xboole_0(sK0,sK2)),sK3)),
% 2.61/0.74    inference(superposition,[],[f274,f604])).
% 2.61/0.74  fof(f604,plain,(
% 2.61/0.74    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 2.61/0.74    inference(forward_demodulation,[],[f603,f36])).
% 2.61/0.74  fof(f603,plain,(
% 2.61/0.74    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 2.61/0.74    inference(forward_demodulation,[],[f559,f36])).
% 2.61/0.74  fof(f559,plain,(
% 2.61/0.74    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK1))),
% 2.61/0.74    inference(superposition,[],[f49,f315])).
% 2.61/0.74  fof(f542,plain,(
% 2.61/0.74    ( ! [X12] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X12,sK2),sK3),k2_zfmisc_1(X12,sK3))) )),
% 2.61/0.74    inference(superposition,[],[f527,f366])).
% 2.61/0.74  fof(f366,plain,(
% 2.61/0.74    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3)) = k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3)) )),
% 2.61/0.74    inference(superposition,[],[f276,f36])).
% 2.61/0.74  fof(f65,plain,(
% 2.61/0.74    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 2.61/0.74    inference(cnf_transformation,[],[f28])).
% 2.61/0.74  fof(f28,plain,(
% 2.61/0.74    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 2.61/0.74    inference(ennf_transformation,[],[f13])).
% 2.61/0.74  fof(f13,axiom,(
% 2.61/0.74    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 2.61/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 2.61/0.74  fof(f1495,plain,(
% 2.61/0.74    ( ! [X12] : (k2_zfmisc_1(sK2,k3_xboole_0(X12,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(X12,sK1))) )),
% 2.61/0.74    inference(backward_demodulation,[],[f557,f1488])).
% 2.61/0.74  fof(f1488,plain,(
% 2.61/0.74    ( ! [X1] : (k2_zfmisc_1(sK0,k3_xboole_0(X1,sK1)) = k3_xboole_0(k2_zfmisc_1(sK2,X1),k2_zfmisc_1(sK0,sK1))) )),
% 2.61/0.74    inference(backward_demodulation,[],[f876,f1462])).
% 2.61/0.74  fof(f876,plain,(
% 2.61/0.74    ( ! [X1] : (k2_zfmisc_1(sK0,k3_xboole_0(X1,sK1)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X1),k2_zfmisc_1(sK0,sK1))) )),
% 2.61/0.74    inference(backward_demodulation,[],[f722,f871])).
% 2.61/0.74  fof(f722,plain,(
% 2.61/0.74    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(sK0,k3_xboole_0(X1,sK1))) )),
% 2.61/0.74    inference(forward_demodulation,[],[f721,f49])).
% 2.61/0.74  fof(f721,plain,(
% 2.61/0.74    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK0,sK1))) )),
% 2.61/0.74    inference(forward_demodulation,[],[f720,f30])).
% 2.61/0.74  fof(f720,plain,(
% 2.61/0.74    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK2,sK3))) )),
% 2.61/0.74    inference(forward_demodulation,[],[f697,f66])).
% 2.61/0.74  fof(f697,plain,(
% 2.61/0.74    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X1,sK3)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 2.61/0.74    inference(superposition,[],[f49,f604])).
% 2.61/0.74  fof(f557,plain,(
% 2.61/0.74    ( ! [X12] : (k2_zfmisc_1(sK2,k3_xboole_0(X12,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X12),k2_zfmisc_1(sK0,sK1))) )),
% 2.61/0.74    inference(superposition,[],[f49,f30])).
% 2.61/0.74  fof(f64,plain,(
% 2.61/0.74    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 2.61/0.74    inference(cnf_transformation,[],[f28])).
% 2.61/0.74  fof(f1462,plain,(
% 2.61/0.74    sK2 = k3_xboole_0(sK0,sK2)),
% 2.61/0.74    inference(superposition,[],[f1461,f36])).
% 2.61/0.74  fof(f1461,plain,(
% 2.61/0.74    sK2 = k3_xboole_0(sK2,sK0)),
% 2.61/0.74    inference(resolution,[],[f1459,f42])).
% 2.61/0.74  fof(f1459,plain,(
% 2.61/0.74    r1_tarski(sK2,sK0)),
% 2.61/0.74    inference(subsumption_resolution,[],[f1456,f32])).
% 2.61/0.74  fof(f1456,plain,(
% 2.61/0.74    k1_xboole_0 = sK1 | r1_tarski(sK2,sK0)),
% 2.61/0.74    inference(resolution,[],[f1411,f64])).
% 2.61/0.74  fof(f1411,plain,(
% 2.61/0.74    r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1))),
% 2.61/0.74    inference(superposition,[],[f833,f1348])).
% 2.61/0.74  fof(f833,plain,(
% 2.61/0.74    ( ! [X9] : (r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(X9,sK3)),k2_zfmisc_1(sK0,sK1))) )),
% 2.61/0.74    inference(superposition,[],[f583,f30])).
% 2.61/0.74  fof(f29,plain,(
% 2.61/0.74    sK1 != sK3 | sK0 != sK2),
% 2.61/0.74    inference(cnf_transformation,[],[f22])).
% 2.61/0.74  fof(f2693,plain,(
% 2.61/0.74    sK1 = sK3),
% 2.61/0.74    inference(forward_demodulation,[],[f2692,f1429])).
% 2.61/0.74  fof(f1429,plain,(
% 2.61/0.74    sK1 = k3_xboole_0(sK3,sK1)),
% 2.61/0.74    inference(superposition,[],[f753,f1348])).
% 2.61/0.74  fof(f753,plain,(
% 2.61/0.74    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 2.61/0.74    inference(superposition,[],[f533,f36])).
% 2.61/0.74  fof(f533,plain,(
% 2.61/0.74    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k3_xboole_0(k3_xboole_0(X4,X5),X5)) )),
% 2.61/0.74    inference(resolution,[],[f527,f42])).
% 2.61/0.74  fof(f2692,plain,(
% 2.61/0.74    sK3 = k3_xboole_0(sK3,sK1)),
% 2.61/0.74    inference(resolution,[],[f2668,f42])).
% 2.61/0.74  fof(f2668,plain,(
% 2.61/0.74    r1_tarski(sK3,sK1)),
% 2.61/0.74    inference(resolution,[],[f2580,f84])).
% 2.61/0.74  fof(f2580,plain,(
% 2.61/0.74    ( ! [X10] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X10)) | r1_tarski(sK3,X10)) )),
% 2.61/0.74    inference(subsumption_resolution,[],[f2579,f31])).
% 2.61/0.74  fof(f2579,plain,(
% 2.61/0.74    ( ! [X10] : (k1_xboole_0 = sK0 | ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X10)) | r1_tarski(sK3,X10)) )),
% 2.61/0.74    inference(forward_demodulation,[],[f2427,f2414])).
% 2.61/0.74  fof(f2427,plain,(
% 2.61/0.74    ( ! [X10] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X10)) | k1_xboole_0 = sK2 | r1_tarski(sK3,X10)) )),
% 2.61/0.74    inference(backward_demodulation,[],[f1336,f2414])).
% 2.61/0.74  fof(f1336,plain,(
% 2.61/0.74    ( ! [X10] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X10)) | k1_xboole_0 = sK2 | r1_tarski(sK3,X10)) )),
% 2.61/0.74    inference(superposition,[],[f65,f30])).
% 2.61/0.74  % SZS output end Proof for theBenchmark
% 2.61/0.74  % (20099)------------------------------
% 2.61/0.74  % (20099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.61/0.74  % (20099)Termination reason: Refutation
% 2.61/0.74  
% 2.61/0.74  % (20099)Memory used [KB]: 8187
% 2.61/0.74  % (20099)Time elapsed: 0.291 s
% 2.61/0.74  % (20099)------------------------------
% 2.61/0.74  % (20099)------------------------------
% 2.61/0.74  % (20092)Success in time 0.366 s
%------------------------------------------------------------------------------
